# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

from copy import deepcopy

from capacity_atlas.data import load_atlas
from capacity_atlas.validate import validate_atlas


def test_registry_is_valid() -> None:
    assert validate_atlas() == []


def test_expanded_registry_and_controlled_axes() -> None:
    atlas = load_atlas()
    assert len(atlas.problems) == 32
    assert list(atlas.tag_axes) == ["model", "features", "quantity", "knowledge"]
    assert "AMS" not in str(atlas.tag_axes)
    assert not (atlas.root / "data" / "categories.yaml").exists()
    for problem in atlas.problems:
        assert "category" not in problem
        assert set(problem["tags"]) == set(atlas.tag_axes)
        assert problem["tags"]["model"]
        assert problem["tags"]["quantity"]
        assert problem["tags"]["knowledge"]


def test_external_proof_must_match_statement_version() -> None:
    atlas = deepcopy(load_atlas())
    problem = atlas.problems_by_id["binary-symmetric-channel"]
    problem["formalization"]["proofs"] = [
        {
            "id": "example-proof",
            "claim": "capacity",
            "status": "complete",
            "system": "Lean",
            "repository": "example/bsc-proof",
            "commit": "0" * 40,
            "url": f"https://github.com/example/bsc-proof/commit/{'0' * 40}",
            "file": "BSC/Main.lean",
            "declaration": "BSC.capacity",
            "statement_version": 2,
        }
    ]
    messages = [issue.message for issue in validate_atlas(atlas)]
    assert any("targets statement version 2, expected 1" in message for message in messages)


def test_formalized_entries_link_existing_declarations() -> None:
    atlas = load_atlas()
    formalized = [
        problem
        for problem in atlas.problems
        if problem["formalization"]["statement"]["status"] != "none"
    ]
    assert formalized
    assert all(problem["formalization"]["statement"]["files"] for problem in formalized)
