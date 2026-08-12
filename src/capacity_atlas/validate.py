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
        claims = statement.get("claims", [])
        files = statement.get("files", [])
        if statement.get("language") != "Lean":
            issues.append(ValidationIssue(source, "formalization language must be Lean"))
        if statement_status == "none" and (files or claims):
            issues.append(
                ValidationIssue(source, "a missing formalization cannot list claims or Lean files")
            )
        if statement_status != "none" and not files:
            issues.append(
                ValidationIssue(source, "formalized definitions/statements need a Lean file")
            )
        if statement_status == "statement" and not claims:
            issues.append(ValidationIssue(source, "a formalized statement needs a claim record"))

        claim_by_id: dict[str, dict[str, Any]] = {}
        for claim in claims:
            claim_id = claim.get("id")
            if claim_id in claim_by_id:
                issues.append(ValidationIssue(source, f"duplicate formal claim id {claim_id!r}"))
            if isinstance(claim_id, str):
                claim_by_id[claim_id] = claim
            kind = claim.get("kind")
            claim_status = claim.get("status")
            if kind == "definition" and claim_status != "stated":
                issues.append(
                    ValidationIssue(source, f"definition claim {claim_id!r} must be stated")
                )
            if kind != "definition" and claim_status == "stated":
                issues.append(
                    ValidationIssue(source, f"non-definition claim {claim_id!r} cannot be stated")
                )
            if statement_status == "definitions" and kind != "definition":
                issues.append(
                    ValidationIssue(
                        source,
                        "definitions-only formalization cannot register "
                        f"{kind!r} claim {claim_id!r}",
                    )
                )

        claim_links: dict[str, list[tuple[str, str, bool]]] = {}
        for entry in files:
            relative = entry.get("path", "")
            declaration = entry.get("declaration", "")
            role = str(entry.get("role", ""))
            claim_id = entry.get("claim_id")
            if role in {"statement", "short-proof"} and not isinstance(claim_id, str):
                issues.append(
                    ValidationIssue(
                        source,
                        f"{role} declaration {declaration!r} must identify a formal claim",
                    )
                )
            if isinstance(claim_id, str) and claim_id not in claim_by_id:
                issues.append(
                    ValidationIssue(
                        source,
                        f"declaration {declaration!r} targets unknown formal claim {claim_id!r}",
                    )
                )
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
            kinds = r"(?P<kind>def|theorem|lemma|structure|inductive|abbrev)"
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
                declaration_kind = declaration_match.group("kind")
                declaration_end = contents.find(":=", declaration_match.end())
                declaration_header = contents[
                    declaration_match.start() : declaration_end + 2
                    if declaration_end >= 0
                    else declaration_match.end()
                ]
                is_named_prop = declaration_kind == "def" and bool(
                    re.search(r":\s*Prop\s*:=", declaration_header, flags=re.DOTALL)
                )
                if isinstance(claim_id, str) and claim_id in claim_by_id:
                    claim_links.setdefault(claim_id, []).append(
                        (role, declaration_kind, is_named_prop)
                    )
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
                if role != "shared-api":
                    problem_marker = f'capacity_problem "{problem_id}"'
                    if problem_marker not in metadata:
                        issues.append(
                            ValidationIssue(
                                source,
                                f"declaration {declaration!r} lacks {problem_marker!r}",
                            )
                        )

        proofs = formalization.get("proofs", [])
        if proofs and statement_status != "statement":
            issues.append(
                ValidationIssue(
                    source,
                    "external proofs require a canonical Lean claim, not definitions only",
                )
            )
        proof_ids: set[str] = set()
        complete_external_claims: set[str] = set()
        for proof in proofs:
            proof_id = proof.get("id")
            claim_id = proof.get("claim_id")
            if proof_id in proof_ids:
                issues.append(ValidationIssue(source, f"duplicate external proof id {proof_id!r}"))
            if isinstance(proof_id, str):
                proof_ids.add(proof_id)
            claim = claim_by_id.get(str(claim_id))
            if claim is None:
                issues.append(
                    ValidationIssue(
                        source,
                        f"external proof targets unknown formal claim {claim_id!r}",
                    )
                )
            elif proof.get("claim_version") != claim.get("version"):
                issues.append(
                    ValidationIssue(
                        source,
                        f"external proof for {claim_id!r} targets claim version "
                        f"{proof.get('claim_version')}, expected {claim.get('version')}",
                    )
                )
            if proof.get("status") == "complete" and isinstance(claim_id, str):
                complete_external_claims.add(claim_id)
            commit = str(proof.get("commit", ""))
            if not re.fullmatch(r"[0-9a-f]{40}", commit):
                issues.append(
                    ValidationIssue(
                        source, f"external proof for {claim_id!r} needs a 40-character commit"
                    )
                )
            repository = str(proof.get("repository", ""))
            expected_prefix = f"https://github.com/{repository}/commit/{commit}"
            if not str(proof.get("url", "")).startswith(expected_prefix):
                issues.append(
                    ValidationIssue(
                        source,
                        f"external proof for {claim_id!r} must link to its immutable commit",
                    )
                )

        for claim_id, claim in claim_by_id.items():
            links = claim_links.get(claim_id, [])
            claim_status = claim.get("status")
            has_local_proof = any(
                role == "short-proof" or declaration_kind in {"theorem", "lemma"}
                for role, declaration_kind, _ in links
            )
            has_complete_proof = has_local_proof or claim_id in complete_external_claims
            if claim_status == "open":
                has_open_prop = any(
                    role == "statement" and is_named_prop for role, _, is_named_prop in links
                )
                if not has_open_prop:
                    issues.append(
                        ValidationIssue(
                            source,
                            f"open formal claim {claim_id!r} needs a named Prop definition",
                        )
                    )
                if has_complete_proof:
                    issues.append(
                        ValidationIssue(
                            source,
                            f"open formal claim {claim_id!r} has a complete proof",
                        )
                    )
            elif claim_status == "proved" and not has_complete_proof:
                issues.append(
                    ValidationIssue(
                        source,
                        f"proved formal claim {claim_id!r} needs a complete local "
                        "or external proof",
                    )
                )
            elif claim_status == "stated" and not any(role == "definition" for role, _, _ in links):
                issues.append(
                    ValidationIssue(
                        source, f"definition claim {claim_id!r} needs a linked definition"
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
