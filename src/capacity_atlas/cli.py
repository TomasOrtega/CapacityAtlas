# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .build import build_site
from .data import find_root, load_atlas
from .validate import validate_atlas


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="capacity-atlas")
    parser.add_argument("--root", type=Path)
    commands = parser.add_subparsers(dest="command", required=True)
    validate = commands.add_parser("validate")
    validate.add_argument("--lean-report", type=Path)
    build = commands.add_parser("build")
    build.add_argument("--output", type=Path)
    build.add_argument("--base-url")
    args = parser.parse_args(argv)
    root = args.root.resolve() if args.root else find_root()

    if args.command == "validate":
        lean_report = None
        if args.lean_report:
            lean_report = json.loads(args.lean_report.read_text(encoding="utf-8"))
        issues = validate_atlas(load_atlas(root), lean_report)
        for issue in issues:
            print(f"ERROR {issue}", file=sys.stderr)
        if issues:
            print(f"Validation failed with {len(issues)} issue(s).", file=sys.stderr)
            return 1
        print("Capacity Atlas data is valid.")
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
