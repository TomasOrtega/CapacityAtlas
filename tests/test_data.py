# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

from copy import deepcopy
from pathlib import Path

from capacity_atlas.data import load_atlas
from capacity_atlas.validate import validate_atlas


def test_registry_is_valid() -> None:
    assert validate_atlas() == []


def test_registry_uses_controlled_axes() -> None:
    atlas = load_atlas()
    assert list(atlas.tag_axes) == ["model", "features", "quantity", "knowledge"]
    assert "AMS" not in str(atlas.tag_axes)
    assert not (atlas.root / "data" / "categories.yaml").exists()
    for problem in atlas.problems:
        assert "category" not in problem
        assert set(problem["tags"]) == set(atlas.tag_axes)
        assert problem["tags"]["model"]
        assert problem["tags"]["quantity"]
        assert problem["tags"]["knowledge"]
    knowledge = atlas.tag_values["knowledge"]
    assert "linear-encoder-only" in knowledge
    assert "linear-only" not in knowledge


def test_discussion_configuration_matches_the_enabled_repository() -> None:
    atlas = load_atlas()
    social = atlas.site["social"]
    giscus = social["giscus"]

    assert social["discussions_enabled"] is True
    assert giscus["enabled"] is True
    assert giscus["repo"] == "TomasOrtega/CapacityAtlas"
    assert giscus["repo_id"] == "R_kgDOTzuIlQ"
    assert giscus["category"] == "General"
    assert giscus["category_id"] == "DIC_kwDOTzuIlc4DDFDj"
    assert giscus["term_prefix"] == "capacityatlas:"
    assert giscus["strict"] is True


def test_external_proof_must_match_claim_version() -> None:
    atlas = deepcopy(load_atlas())
    problem = atlas.problems_by_id["binary-symmetric-channel"]
    problem["formalization"]["proofs"] = [
        {
            "id": "example-proof",
            "claim_id": "operational-capacity",
            "status": "complete",
            "system": "Lean",
            "repository": "example/bsc-proof",
            "commit": "0" * 40,
            "url": f"https://github.com/example/bsc-proof/commit/{'0' * 40}",
            "file": "BSC/Main.lean",
            "declaration": "BSC.capacity",
            "claim_version": 1,
        }
    ]
    messages = [issue.message for issue in validate_atlas(atlas)]
    assert any("targets claim version 1, expected 2" in message for message in messages)


def test_formalized_entries_link_existing_declarations() -> None:
    atlas = load_atlas()
    formalized = [
        problem
        for problem in atlas.problems
        if problem["formalization"]["statement"]["status"] != "none"
    ]
    assert formalized
    assert all(problem["formalization"]["statement"]["files"] for problem in formalized)


def test_formal_claims_have_independent_identity_and_status() -> None:
    atlas = load_atlas()
    claims = atlas.problems_by_id["sun-jafar-11-message-index-coding"]["formalization"][
        "statement"
    ]["claims"]
    claims_by_id = {claim["id"]: claim for claim in claims}

    assert claims_by_id["linear-achievability"]["kind"] == "achievability"
    assert claims_by_id["linear-achievability"]["status"] == "open"
    assert claims_by_id["internal-conflicts-exact"]["kind"] == "structural"
    assert claims_by_id["internal-conflicts-exact"]["status"] == "proved"


def test_linear_encoder_quantity_is_named_conservatively() -> None:
    atlas = load_atlas()
    for problem_id in (
        "sun-jafar-11-message-index-coding",
        "sun-jafar-six-message-groupcast-index-coding",
    ):
        problem = atlas.problems_by_id[problem_id]
        linear_bound = next(
            bound for bound in problem["bounds"] if bound["id"] == "linear-encoder-capacity"
        )
        assert linear_bound["direction"] == "linear-encoder-exact"
        assert "linear-encoder" in problem["capacity"]["notes"].lower()
        assert "arbitrary zero-error decoders" in problem["capacity"]["notes"].lower()

    issue_template = Path(".github/ISSUE_TEMPLATE/add_bound.yml").read_text(encoding="utf-8")
    assert "Linear-encoder-only exact result" in issue_template
    assert "Linear-only exact result" not in issue_template


def test_open_claim_requires_named_prop_definition() -> None:
    atlas = deepcopy(load_atlas())
    problem = atlas.problems_by_id["sun-jafar-11-message-index-coding"]
    files = problem["formalization"]["statement"]["files"]
    problem["formalization"]["statement"]["files"] = [
        entry for entry in files if entry.get("claim_id") != "exact-capacity"
    ]

    messages = [issue.message for issue in validate_atlas(atlas)]

    assert any(
        "open formal claim 'exact-capacity' needs a named Prop definition" in message
        for message in messages
    )


def test_open_claim_cannot_have_complete_proof() -> None:
    atlas = deepcopy(load_atlas())
    problem = atlas.problems_by_id["binary-symmetric-channel"]
    claim = next(
        claim
        for claim in problem["formalization"]["statement"]["claims"]
        if claim["id"] == "operational-capacity"
    )
    claim["status"] = "open"

    messages = [issue.message for issue in validate_atlas(atlas)]

    assert any(
        "open formal claim 'operational-capacity' has a complete proof" in message
        for message in messages
    )


def test_structural_proof_does_not_prove_capacity_claim() -> None:
    atlas = load_atlas()
    problem = atlas.problems_by_id["sun-jafar-11-message-index-coding"]
    structural = next(
        claim
        for claim in problem["formalization"]["statement"]["claims"]
        if claim["id"] == "internal-conflicts-exact"
    )
    assert structural["kind"] == "structural"
    assert structural["status"] == "proved"
    assert not any(
        claim["kind"] != "structural" and claim["status"] == "proved"
        for claim in problem["formalization"]["statement"]["claims"]
    )
