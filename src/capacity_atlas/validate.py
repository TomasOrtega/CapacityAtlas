from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

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

    seen_ids: set[str] = set()
    category_ids = set(atlas.categories_by_id)
    reference_ids = set(atlas.references)

    for problem in atlas.problems:
        problem_id = str(problem.get("id", "<missing-id>"))
        source_path = atlas.problem_files.get(problem_id)
        source = str(source_path.relative_to(atlas.root)) if source_path else problem_id

        errors = validator.iter_errors(json_ready(problem))
        for error in sorted(errors, key=lambda item: list(item.path)):
            location = ".".join(str(part) for part in error.path)
            suffix = f" at {location}" if location else ""
            issues.append(ValidationIssue(source, f"schema error{suffix}: {error.message}"))

        if problem_id in seen_ids:
            issues.append(ValidationIssue(source, f"duplicate problem id {problem_id!r}"))
        seen_ids.add(problem_id)

        if source_path and source_path.stem != problem_id:
            issues.append(
                ValidationIssue(source, f"filename must match id; expected {problem_id}.yaml")
            )

        category = problem.get("category")
        if category not in category_ids:
            issues.append(ValidationIssue(source, f"unknown category {category!r}"))

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

        formalization = problem.get("formalization", {"status": "none"})
        status = formalization.get("status", "none")
        language = formalization.get("language")
        files = formalization.get("files", [])

        if status != "none" and language != "Lean":
            issues.append(
                ValidationIssue(source, "formalizations must use language: Lean")
            )
        if status == "none" and files:
            issues.append(
                ValidationIssue(source, "formalization files require a non-none status")
            )

        for entry in files:
            relative = entry.get("path", "")
            declaration = entry.get("declaration", "")
            if not isinstance(relative, str) or not relative.startswith("lean/"):
                issues.append(
                    ValidationIssue(source, f"formalization path must be under lean/: {relative!r}")
                )
                continue
            lean_path = atlas.root / relative
            if not lean_path.is_file():
                issues.append(ValidationIssue(source, f"missing Lean file {relative}"))
                continue
            if declaration:
                contents = lean_path.read_text(encoding="utf-8")
                token = _declaration_token(str(declaration))
                declaration_kinds = r"(?:def|theorem|lemma|structure|inductive|abbrev)"
                pattern = rf"\b{declaration_kinds}\s+{re.escape(token)}\b"
                if not re.search(pattern, contents):
                    issues.append(
                        ValidationIssue(
                            source,
                            f"declaration {declaration!r} was not found in {relative}",
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
