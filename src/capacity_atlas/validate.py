# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

import re
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator, FormatChecker

from .data import json_ready, load_atlas, load_yaml
from .model import Atlas


@dataclass(frozen=True)
class ValidationIssue:
    source: str
    message: str

    def __str__(self) -> str:
        return f"{self.source}: {self.message}"


def _all_reference_ids(problem: dict[str, Any]) -> Iterable[str]:
    yield from problem.get("references", [])
    for bound in problem.get("bounds", []):
        yield from bound.get("references", [])
    for event in problem.get("timeline", []):
        yield from event.get("references", [])


def _declaration_token(declaration: str) -> str:
    return declaration.rsplit(".", maxsplit=1)[-1]


def validate_atlas(atlas: Atlas | None = None) -> list[ValidationIssue]:
    atlas = atlas or load_atlas()
    issues: list[ValidationIssue] = []
    schema = load_yaml(atlas.root / "schema" / "problem.schema.json")
    validator = Draft202012Validator(schema, format_checker=FormatChecker())
    tag_values = atlas.tag_values
    reference_ids = set(atlas.references)
    seen_ids: set[str] = set()

    for problem in atlas.problems:
        problem_id = str(problem.get("id", "<missing-id>"))
        path = atlas.problem_files.get(problem_id)
        source = str(path.relative_to(atlas.root)) if path else problem_id

        for error in sorted(
            validator.iter_errors(json_ready(problem)), key=lambda item: list(item.path)
        ):
            location = ".".join(str(part) for part in error.path)
            suffix = f" at {location}" if location else ""
            issues.append(ValidationIssue(source, f"schema error{suffix}: {error.message}"))

        if problem_id in seen_ids:
            issues.append(ValidationIssue(source, f"duplicate problem id {problem_id!r}"))
        seen_ids.add(problem_id)
        if path and path.stem != problem_id:
            issues.append(ValidationIssue(source, f"filename must be {problem_id}.yaml"))

        for axis_id, selected in problem.get("tags", {}).items():
            if axis_id not in tag_values:
                issues.append(ValidationIssue(source, f"unknown tag axis {axis_id!r}"))
                continue
            for tag_id in selected:
                if tag_id not in tag_values[axis_id]:
                    issues.append(ValidationIssue(source, f"unknown {axis_id} tag {tag_id!r}"))

        for reference_id in sorted(set(_all_reference_ids(problem))):
            if reference_id not in reference_ids:
                issues.append(ValidationIssue(source, f"unknown reference {reference_id!r}"))

        bound_ids: set[str] = set()
        for bound in problem.get("bounds", []):
            bound_id = bound.get("id")
            if bound_id in bound_ids:
                issues.append(ValidationIssue(source, f"duplicate bound id {bound_id!r}"))
            if isinstance(bound_id, str):
                bound_ids.add(bound_id)

        formalization = problem.get("formalization", {})
        statement = formalization.get("statement", {})
        statement_status = statement.get("status", "none")
        files = statement.get("files", [])
        if statement.get("language") != "Lean":
            issues.append(ValidationIssue(source, "formalization language must be Lean"))
        if statement_status == "none" and files:
            issues.append(ValidationIssue(source, "a missing statement cannot list Lean files"))
        if statement_status != "none" and not files:
            issues.append(
                ValidationIssue(source, "formalized definitions/statements need a Lean file")
            )

        for entry in files:
            relative = entry.get("path", "")
            declaration = entry.get("declaration", "")
            if not isinstance(relative, str) or not relative.startswith("lean/"):
                issues.append(
                    ValidationIssue(source, f"Lean path must be under lean/: {relative!r}")
                )
                continue
            lean_path = atlas.root / relative
            if not lean_path.is_file():
                issues.append(ValidationIssue(source, f"missing Lean file {relative}"))
                continue
            contents = lean_path.read_text(encoding="utf-8")
            token = _declaration_token(str(declaration))
            kinds = r"(?:def|theorem|lemma|structure|inductive|abbrev)"
            declaration_match = (
                re.search(rf"\b{kinds}\s+{re.escape(token)}\b", contents) if declaration else None
            )
            if declaration and declaration_match is None:
                issues.append(
                    ValidationIssue(
                        source, f"declaration {declaration!r} was not found in {relative}"
                    )
                )
                continue
            if declaration_match is not None:
                metadata = contents[
                    max(0, declaration_match.start() - 800) : declaration_match.start()
                ]
                role_attribute = {
                    "definition": "capacity_definition",
                    "statement": "capacity_statement",
                    "short-proof": "capacity_short_proof",
                    "test": "capacity_short_proof",
                    "shared-api": "capacity_shared_api",
                }[entry.get("role")]
                if role_attribute not in metadata:
                    issues.append(
                        ValidationIssue(
                            source,
                            f"declaration {declaration!r} lacks [{role_attribute}] metadata",
                        )
                    )
                if entry.get("role") != "shared-api":
                    problem_marker = f'capacity_problem "{problem_id}"'
                    if problem_marker not in metadata:
                        issues.append(
                            ValidationIssue(
                                source,
                                f"declaration {declaration!r} lacks {problem_marker!r}",
                            )
                        )

        version = statement.get("version")
        proofs = formalization.get("proofs", [])
        if proofs and statement_status != "statement":
            issues.append(
                ValidationIssue(
                    source,
                    "external proofs require a canonical Lean statement, not definitions only",
                )
            )
        proof_ids: set[str] = set()
        for proof in proofs:
            proof_id = proof.get("id")
            claim = proof.get("claim")
            if proof_id in proof_ids:
                issues.append(ValidationIssue(source, f"duplicate external proof id {proof_id!r}"))
            if isinstance(proof_id, str):
                proof_ids.add(proof_id)
            if proof.get("statement_version") != version:
                issues.append(
                    ValidationIssue(
                        source,
                        f"external proof {claim!r} targets statement version "
                        f"{proof.get('statement_version')}, expected {version}",
                    )
                )
            commit = str(proof.get("commit", ""))
            if not re.fullmatch(r"[0-9a-f]{40}", commit):
                issues.append(
                    ValidationIssue(source, f"external proof {claim!r} needs a 40-character commit")
                )
            repository = str(proof.get("repository", ""))
            expected_prefix = f"https://github.com/{repository}/commit/{commit}"
            if not str(proof.get("url", "")).startswith(expected_prefix):
                issues.append(
                    ValidationIssue(
                        source,
                        f"external proof {claim!r} must link to its immutable commit",
                    )
                )

    if not atlas.problems:
        issues.append(ValidationIssue("data/problems", "at least one problem is required"))
    return issues


def assert_valid(root: Path | None = None) -> Atlas:
    atlas = load_atlas(root)
    issues = validate_atlas(atlas)
    if issues:
        formatted = "\n".join(f"- {issue}" for issue in issues)
        raise RuntimeError(f"Atlas validation failed:\n{formatted}")
    return atlas
