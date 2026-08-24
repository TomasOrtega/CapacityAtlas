# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import date
from pathlib import Path

from yaml import YAMLError

from .build import build_site
from .data import find_root, load_atlas
from .model import Atlas
from .validate import validate_atlas

PROBLEM_ID_PATTERN = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")


def _new_problem(root: Path, problem_id: str) -> int:
    if not PROBLEM_ID_PATTERN.fullmatch(problem_id):
        print("ERROR Problem IDs use lowercase letters, numbers, and hyphens.", file=sys.stderr)
        return 1

    relative = Path("data") / "problems" / f"{problem_id}.yaml"
    destination = root / relative
    template_path = root / "docs" / "problem-template.yaml"
    try:
        template = template_path.read_text(encoding="utf-8")
    except OSError as error:
        print(f"ERROR Could not read {template_path}: {error}", file=sys.stderr)
        return 1

    marker = "id: example-channel"
    if marker not in template:
        print(f"ERROR {template_path} has no example problem ID.", file=sys.stderr)
        return 1

    try:
        contents = template.replace(marker, f"id: {problem_id}", 1)
        contents = re.sub(
            r"(?m)^updated:.*$",
            f"updated: {date.today().isoformat()}",
            contents,
            count=1,
        )
        with destination.open("x", encoding="utf-8") as handle:
            handle.write(contents)
    except FileExistsError:
        print(f"ERROR {relative} already exists.", file=sys.stderr)
        return 1
    except OSError as error:
        print(f"ERROR Could not create {relative}: {error}", file=sys.stderr)
        return 1

    print(f"Created {relative}. Complete its placeholders before validating.")
    return 0


def _selected_sources(atlas: Atlas, paths: list[Path]) -> set[str] | None:
    known = {
        path.resolve(): path.relative_to(atlas.root).as_posix()
        for path in atlas.problem_files.values()
    }
    selected: set[str] = set()
    for path in paths:
        candidate = path if path.is_absolute() else atlas.root / path
        source = known.get(candidate.resolve())
        if source is None:
            print(f"ERROR {path} is not a registry problem file.", file=sys.stderr)
            return None
        selected.add(source)
    return selected


def _load_atlas(root: Path) -> Atlas | None:
    try:
        return load_atlas(root)
    except (OSError, ValueError, TypeError, AttributeError, KeyError, YAMLError) as error:
        print(f"ERROR Could not load registry: {error}", file=sys.stderr)
        return None


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="capacity-atlas")
    parser.add_argument("--root", type=Path)
    commands = parser.add_subparsers(dest="command", required=True)
    validate = commands.add_parser("validate")
    validate.add_argument("--lean-report", type=Path)
    validate.add_argument("problems", nargs="*", type=Path, metavar="PROBLEM")
    build = commands.add_parser("build")
    build.add_argument("--output", type=Path)
    build.add_argument("--base-url")
    new = commands.add_parser("new")
    new.add_argument("problem_id", metavar="PROBLEM-ID")
    args = parser.parse_args(argv)
    root = args.root.resolve() if args.root else find_root()

    if args.command == "new":
        return _new_problem(root, args.problem_id)

    if args.command == "validate":
        lean_report = None
        if args.lean_report:
            lean_report = json.loads(args.lean_report.read_text(encoding="utf-8"))
        atlas = _load_atlas(root)
        if atlas is None:
            return 1
        issues = validate_atlas(atlas, lean_report)
        if args.problems:
            selected = _selected_sources(atlas, args.problems)
            if selected is None:
                return 1
            problem_sources = {
                path.relative_to(atlas.root).as_posix() for path in atlas.problem_files.values()
            }
            issues = [
                issue
                for issue in issues
                if issue.source in selected or issue.source not in problem_sources
            ]
        for issue in issues:
            print(f"ERROR {issue}", file=sys.stderr)
        if issues:
            print(f"Validation failed with {len(issues)} issue(s).", file=sys.stderr)
            return 1
        message = (
            "Selected problem data is valid." if args.problems else "Capacity Atlas data is valid."
        )
        print(message)
        return 0

    destination = build_site(
        root=root,
        output=args.output.resolve() if args.output else None,
        base_url=args.base_url,
    )
    print(f"Built Capacity Atlas at {destination}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
