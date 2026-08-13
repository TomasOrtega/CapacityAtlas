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


def validate_atlas(
    atlas: Atlas | None = None,
    lean_report: dict[str, Any] | None = None,
) -> list[ValidationIssue]:
    atlas = atlas or load_atlas()
    issues: list[ValidationIssue] = []
    schema = load_yaml(atlas.root / "schema" / "problem.schema.json")
    validator = Draft202012Validator(schema, format_checker=FormatChecker())
    tag_values = atlas.tag_values
    reference_ids = set(atlas.references)
    seen_ids: set[str] = set()
    yaml_claims: list[tuple[str, str, dict[str, Any], str, bool]] = []

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
        formalization_status = formalization.get("status", "none")
        claims = formalization.get("claims", [])
        files = formalization.get("files", [])
        if formalization_status == "none" and (files or claims):
            issues.append(
                ValidationIssue(source, "a missing formalization cannot list claims or Lean files")
            )
        if formalization_status != "none" and not files:
            issues.append(
                ValidationIssue(source, "formalized definitions or claims need a Lean file")
            )
        if formalization_status == "stated" and not claims:
            issues.append(ValidationIssue(source, "a formally stated entry needs a claim record"))
        if formalization_status == "definitions" and claims:
            issues.append(
                ValidationIssue(source, "a definitions-only formalization cannot list claims")
            )

        claim_by_id: dict[str, dict[str, Any]] = {}
        for claim in claims:
            claim_id = claim.get("id")
            if claim_id in claim_by_id:
                issues.append(ValidationIssue(source, f"duplicate formal claim id {claim_id!r}"))
            if isinstance(claim_id, str):
                claim_by_id[claim_id] = claim
            if claim.get("category") == "open" and claim.get("formal_status") == "proved":
                issues.append(
                    ValidationIssue(
                        source,
                        f"open claim {claim_id!r} cannot be formally proved",
                    )
                )

        claim_links: dict[str, list[tuple[str, str, str, str]]] = {}
        for entry in files:
            relative = entry.get("path", "")
            declaration = entry.get("declaration", "")
            role = str(entry.get("role", ""))
            claim_id = entry.get("claim_id")
            if role == "claim" and not isinstance(claim_id, str):
                issues.append(
                    ValidationIssue(
                        source,
                        f"claim declaration {declaration!r} must identify a formal claim",
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
                re.search(rf"\b{kinds}\s+(?:\w+\.)*{re.escape(token)}\b", contents)
                if declaration
                else None
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
                next_declaration = re.search(
                    r"(?m)^(?:@\[[^\n]*\]\n)*(?:private\s+|protected\s+)?"
                    r"(?:def|theorem|lemma|structure|inductive|abbrev)\s+",
                    contents[declaration_match.end() :],
                )
                declaration_stop = (
                    declaration_match.end() + next_declaration.start()
                    if next_declaration
                    else len(contents)
                )
                declaration_body = contents[declaration_match.start() : declaration_stop]
                prefix = contents[: declaration_match.start()]
                attribute_start = prefix.rfind("@[")
                metadata = prefix[attribute_start:] if attribute_start >= 0 else ""
                if isinstance(claim_id, str) and claim_id in claim_by_id:
                    claim_links.setdefault(claim_id, []).append(
                        (role, declaration_kind, metadata, declaration_body)
                    )
                role_attribute = {
                    "definition": "capacity_definition",
                    "claim": "capacity_statement",
                    "test": "capacity_test",
                    "API": "capacity_shared_api",
                }.get(entry.get("role"))
                if role_attribute and role_attribute not in metadata:
                    issues.append(
                        ValidationIssue(
                            source,
                            f"declaration {declaration!r} lacks [{role_attribute}] metadata",
                        )
                    )
                if role != "API":
                    problem_marker = f'capacity_problem "{problem_id}"'
                    if problem_marker not in metadata:
                        issues.append(
                            ValidationIssue(
                                source,
                                f"declaration {declaration!r} lacks {problem_marker!r}",
                            )
                        )

        proofs = formalization.get("proofs", [])
        if proofs and formalization_status != "stated":
            issues.append(
                ValidationIssue(
                    source,
                    "formal proofs require a canonical claim, not definitions only",
                )
            )
        proof_ids: set[str] = set()
        complete_linked_claims: set[str] = set()
        for proof in proofs:
            proof_id = proof.get("id")
            claim_id = proof.get("claim_id")
            if proof_id in proof_ids:
                issues.append(ValidationIssue(source, f"duplicate formal proof id {proof_id!r}"))
            if isinstance(proof_id, str):
                proof_ids.add(proof_id)
            claim = claim_by_id.get(str(claim_id))
            if claim is None:
                issues.append(
                    ValidationIssue(
                        source,
                        f"formal proof targets unknown claim {claim_id!r}",
                    )
                )
            elif proof.get("claim_version") != claim.get("version"):
                issues.append(
                    ValidationIssue(
                        source,
                        f"formal proof for {claim_id!r} targets claim version "
                        f"{proof.get('claim_version')}, expected {claim.get('version')}",
                    )
                )
            if proof.get("status") == "complete" and isinstance(claim_id, str):
                complete_linked_claims.add(claim_id)
            commit = str(proof.get("commit", ""))
            if not re.fullmatch(r"[0-9a-f]{40}", commit):
                issues.append(
                    ValidationIssue(
                        source, f"formal proof for {claim_id!r} needs a 40-character commit"
                    )
                )
            repository = str(proof.get("repository", ""))
            expected_prefix = f"https://github.com/{repository}/commit/{commit}"
            if not str(proof.get("url", "")).startswith(expected_prefix):
                issues.append(
                    ValidationIssue(
                        source,
                        f"formal proof for {claim_id!r} must link to its immutable commit",
                    )
                )

        for claim_id, claim in claim_by_id.items():
            links = claim_links.get(claim_id, [])
            claim_declarations = [
                (declaration_kind, metadata, body)
                for role, declaration_kind, metadata, body in links
                if role == "claim"
            ]
            if len(claim_declarations) != 1 or claim_declarations[0][0] not in {
                "theorem",
                "lemma",
            }:
                issues.append(
                    ValidationIssue(
                        source,
                        f"formal claim {claim_id!r} needs one theorem or lemma declaration",
                    )
                )
                continue

            metadata = claim_declarations[0][1]
            category_attribute = {
                "open": "capacity_open",
                "solved": "capacity_solved",
                "API": "capacity_api",
                "test": "capacity_test",
            }.get(claim.get("category"))
            if category_attribute and category_attribute not in metadata:
                issues.append(
                    ValidationIssue(
                        source,
                        f"formal claim {claim_id!r} lacks [{category_attribute}] metadata",
                    )
                )

            has_local_proof = "capacity_formal_proof" in metadata
            has_linked_proof = claim_id in complete_linked_claims
            formal_status = claim.get("formal_status")
            if formal_status == "proved" and not (has_local_proof or has_linked_proof):
                issues.append(
                    ValidationIssue(
                        source,
                        f"formally proved claim {claim_id!r} needs local or linked proof metadata",
                    )
                )
            if formal_status == "stated" and (has_local_proof or has_linked_proof):
                issues.append(
                    ValidationIssue(
                        source,
                        f"formally stated claim {claim_id!r} has complete proof metadata",
                    )
                )
            declarations = [
                str(entry.get("declaration", ""))
                for entry in files
                if entry.get("role") == "claim" and entry.get("claim_id") == claim_id
            ]
            if len(declarations) == 1:
                yaml_claims.append((source, problem_id, claim, declarations[0], has_linked_proof))

    if lean_report is not None:
        for error in lean_report.get("errors", []):
            issues.append(ValidationIssue("lean/environment", str(error)))

        lean_claims = [
            declaration
            for declaration in lean_report.get("declarations", [])
            if isinstance(declaration, dict) and declaration.get("claimId") is not None
        ]
        yaml_by_declaration: dict[str, list[tuple[str, str, dict[str, Any], bool]]] = {}
        for source, problem_id, claim, declaration, linked in yaml_claims:
            yaml_by_declaration.setdefault(declaration, []).append(
                (source, problem_id, claim, linked)
            )
        lean_by_declaration: dict[str, list[dict[str, Any]]] = {}
        for declaration in lean_claims:
            name = str(declaration.get("declaration", ""))
            lean_by_declaration.setdefault(name, []).append(declaration)

        for declaration, records in yaml_by_declaration.items():
            if len(records) > 1:
                for source, _, _, _ in records:
                    issues.append(
                        ValidationIssue(
                            source,
                            f"duplicate YAML claim declaration {declaration!r}",
                        )
                    )

        for declaration, records in lean_by_declaration.items():
            if len(records) > 1:
                issues.append(
                    ValidationIssue(
                        "lean/environment",
                        f"duplicate tagged Lean claim declaration {declaration!r}",
                    )
                )
                first = records[0]
                issues.append(
                    ValidationIssue(
                        "lean/environment",
                        "duplicate tagged Lean claim "
                        f"{first.get('problemId')!r}/{first.get('claimId')!r}",
                    )
                )

        for source, problem_id, claim, declaration, has_linked_proof in yaml_claims:
            matches = lean_by_declaration.get(declaration, [])
            claim_id = str(claim.get("id"))
            if len(matches) != 1:
                issues.append(
                    ValidationIssue(
                        source,
                        f"formal claim {claim_id!r} needs exactly one matching tagged "
                        f"Lean declaration, found {len(matches)}",
                    )
                )
                continue
            lean_claim = matches[0]
            comparisons = (
                ("problem ID", lean_claim.get("problemId"), problem_id),
                ("claim ID", lean_claim.get("claimId"), claim.get("id")),
                ("category", lean_claim.get("category"), claim.get("category")),
                ("version", lean_claim.get("claimVersion"), claim.get("version")),
            )
            for field, actual, expected in comparisons:
                if actual != expected:
                    issues.append(
                        ValidationIssue(
                            source,
                            f"formal claim {claim_id!r} Lean {field} {actual!r} "
                            f"does not match YAML {field} {expected!r}",
                        )
                    )

            axioms = {str(axiom) for axiom in lean_claim.get("axioms", [])}
            has_local_proof = lean_claim.get("formalProof") is True
            formal_status = claim.get("formal_status")
            if has_local_proof and "sorryAx" in axioms:
                issues.append(
                    ValidationIssue(
                        source,
                        f"locally proved claim {claim_id!r} transitively depends on sorryAx",
                    )
                )
            if claim.get("category") in {"API", "test"} and "sorryAx" in axioms:
                trust_role = "reusable API" if claim.get("category") == "API" else "test"
                issues.append(
                    ValidationIssue(
                        source,
                        f"{trust_role} claim {claim_id!r} transitively depends on sorryAx",
                    )
                )
            if formal_status == "proved" and not (has_local_proof or has_linked_proof):
                issues.append(
                    ValidationIssue(
                        source,
                        f"formally proved claim {claim_id!r} needs local or linked proof metadata",
                    )
                )
            if formal_status == "stated" and (has_local_proof or has_linked_proof):
                issues.append(
                    ValidationIssue(
                        source,
                        f"formally stated claim {claim_id!r} has complete proof metadata",
                    )
                )
            if formal_status == "stated" and not has_linked_proof and "sorryAx" not in axioms:
                issues.append(
                    ValidationIssue(
                        source,
                        f"formally stated claim {claim_id!r} must transitively depend on sorryAx",
                    )
                )

        for declaration, records in lean_by_declaration.items():
            yaml_records = yaml_by_declaration.get(declaration, [])
            if len(yaml_records) != 1:
                for record in records:
                    issues.append(
                        ValidationIssue(
                            "lean/environment",
                            "tagged Lean claim has no YAML record: "
                            f"{record.get('problemId')!r}/{record.get('claimId')!r}",
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
