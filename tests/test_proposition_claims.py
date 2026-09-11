# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

from copy import deepcopy
from dataclasses import replace
from pathlib import Path
from typing import Any

import pytest

from capacity_atlas.data import load_atlas
from capacity_atlas.model import Atlas
from capacity_atlas.validate import validate_atlas


def _proposition_atlas(tmp_path: Path, *, extra_tags: str = "") -> tuple[Atlas, dict[str, Any]]:
    atlas = load_atlas()
    problem = deepcopy(atlas.problems_by_id["binary-symmetric-channel"])
    problem["formalization"] = {
        "status": "stated",
        "claims": [
            {
                "id": "example",
                "version": 1,
                "kind": "structural",
                "category": "solved",
                "formal_status": "stated",
                "description": "A parameterized canonical proposition.",
            }
        ],
        "files": [
            {
                "path": "lean/Example.lean",
                "declaration": "Example.claim",
                "role": "claim",
                "claim_id": "example",
                "description": "Canonical proposition with binders.",
            }
        ],
        "proofs": [],
    }
    (tmp_path / "schema").mkdir()
    (tmp_path / "schema/problem.schema.json").write_text(
        (atlas.root / "schema/problem.schema.json").read_text(encoding="utf-8"),
        encoding="utf-8",
    )
    (tmp_path / "lean").mkdir()
    (tmp_path / "lean/Example.lean").write_text(
        '@[capacity_problem "binary-symmetric-channel", capacity_claim "example" 1,\n'
        f"  capacity_statement, capacity_proposition, capacity_solved{extra_tags}]\n"
        "def claim (n : Nat) : Prop := n = n\n",
        encoding="utf-8",
    )
    atlas = replace(atlas, root=tmp_path, problems=[problem], problem_files={})
    report = {
        "declarations": [
            {
                "declaration": "Example.claim",
                "module": "Example",
                "problemId": problem["id"],
                "claimId": "example",
                "claimVersion": 1,
                "category": "solved",
                "formalProof": False,
                "proposition": True,
                "test": False,
                "axioms": [],
            }
        ],
        "errors": [],
    }
    return atlas, report


def _linked_proof(status: str = "complete") -> dict[str, Any]:
    return {
        "id": "external-example",
        "claim_id": "example",
        "claim_version": 1,
        "status": status,
        "system": "Lean",
        "repository": "example/proof",
        "commit": "0" * 40,
        "url": f"https://github.com/example/proof/commit/{'0' * 40}",
        "file": "Example.lean",
        "declaration": "Example.proof",
    }


@pytest.mark.parametrize("compiled", [False, True])
def test_clean_proposition_can_be_stated(tmp_path: Path, compiled: bool) -> None:
    atlas, report = _proposition_atlas(tmp_path)
    assert validate_atlas(atlas, report if compiled else None) == []


def test_claim_metadata_accepts_lean_whitespace(tmp_path: Path) -> None:
    atlas, report = _proposition_atlas(tmp_path)
    path = tmp_path / "lean/Example.lean"
    path.write_text(
        path.read_text(encoding="utf-8").replace(
            'capacity_claim "example" 1,', 'capacity_claim\n    "example"   \n    1,'
        ),
        encoding="utf-8",
    )
    assert validate_atlas(atlas, report) == []


def test_proposition_can_be_proved_by_complete_linked_proof(tmp_path: Path) -> None:
    atlas, report = _proposition_atlas(tmp_path)
    formalization = atlas.problems[0]["formalization"]
    formalization["claims"][0]["formal_status"] = "proved"
    formalization["proofs"] = [_linked_proof()]
    assert validate_atlas(atlas, report) == []


@pytest.mark.parametrize("proofs", [[], [_linked_proof("partial")]])
def test_proved_proposition_requires_complete_linked_proof(
    tmp_path: Path, proofs: list[dict[str, Any]]
) -> None:
    atlas, report = _proposition_atlas(tmp_path)
    formalization = atlas.problems[0]["formalization"]
    formalization["claims"][0]["formal_status"] = "proved"
    formalization["proofs"] = proofs
    messages = [issue.message for issue in validate_atlas(atlas, report)]
    assert any("proposition claim 'example' needs a complete linked proof" in m for m in messages)


@pytest.mark.parametrize("compiled", [False, True])
def test_proposition_cannot_be_marked_as_local_proof(tmp_path: Path, compiled: bool) -> None:
    atlas, report = _proposition_atlas(tmp_path, extra_tags=", capacity_formal_proof")
    atlas.problems[0]["formalization"]["claims"][0]["formal_status"] = "proved"
    report["declarations"][0]["formalProof"] = True
    messages = [issue.message for issue in validate_atlas(atlas, report if compiled else None)]
    assert any("proposition claim 'example' cannot be a local proof" in m for m in messages)
    assert any("proposition claim 'example' needs a complete linked proof" in m for m in messages)


@pytest.mark.parametrize("category", ["API", "test"])
def test_proposition_requires_research_category(tmp_path: Path, category: str) -> None:
    atlas, report = _proposition_atlas(tmp_path)
    atlas.problems[0]["formalization"]["claims"][0]["category"] = category
    report["declarations"][0]["category"] = category
    messages = [issue.message for issue in validate_atlas(atlas, report)]
    assert any(
        "proposition claim 'example' requires an open or solved category" in m for m in messages
    )


@pytest.mark.parametrize("axiom", ["sorryAx", "Lean.ofReduceBool", "Unreviewed.axiom"])
def test_proposition_requires_clean_transitive_axioms(tmp_path: Path, axiom: str) -> None:
    atlas, report = _proposition_atlas(tmp_path)
    report["declarations"][0]["axioms"] = [axiom]
    messages = [issue.message for issue in validate_atlas(atlas, report)]
    assert any(
        "proposition claim 'example' has undeclared trust dependencies" in m for m in messages
    )


def test_proposition_role_must_match_compiled_declaration(tmp_path: Path) -> None:
    atlas, report = _proposition_atlas(tmp_path)
    report["declarations"][0]["proposition"] = False
    messages = [issue.message for issue in validate_atlas(atlas, report)]
    assert any("proposition role" in m and "does not match" in m for m in messages)


def test_untagged_definition_cannot_register_a_claim(tmp_path: Path) -> None:
    atlas, report = _proposition_atlas(tmp_path)
    path = tmp_path / "lean/Example.lean"
    path.write_text(path.read_text(encoding="utf-8").replace("capacity_proposition, ", ""))
    messages = [issue.message for issue in validate_atlas(atlas, report)]
    assert any("needs one theorem or lemma declaration" in m for m in messages)


def test_proposition_requires_claim_identity_and_version(tmp_path: Path) -> None:
    atlas, _ = _proposition_atlas(tmp_path)
    path = tmp_path / "lean/Example.lean"
    path.write_text(
        path.read_text(encoding="utf-8").replace('capacity_claim "example" 1,', ""),
        encoding="utf-8",
    )
    messages = [issue.message for issue in validate_atlas(atlas)]
    assert any("lacks 'capacity_claim" in m for m in messages)
