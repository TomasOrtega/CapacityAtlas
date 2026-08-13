# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

import re
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


def test_formal_proof_must_match_claim_version() -> None:
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
        problem for problem in atlas.problems if problem["formalization"]["status"] != "none"
    ]
    assert formalized
    assert all(problem["formalization"]["files"] for problem in formalized)


def test_every_problem_statement_is_registered() -> None:
    atlas = load_atlas()
    registered = {
        (entry["path"], entry["declaration"].rsplit(".", 1)[-1])
        for problem in atlas.problems
        for entry in problem["formalization"]["files"]
        if entry["role"] == "claim"
    }
    declared: set[tuple[str, str]] = set()
    pattern = re.compile(
        r"@\[[^\]]*\bcapacity_statement\b[^\]]*\]\s*"
        r"(?:theorem|lemma)\s+(\w+)",
        re.MULTILINE,
    )
    for lean_path in (atlas.root / "lean").rglob("*.lean"):
        relative = lean_path.relative_to(atlas.root).as_posix()
        contents = lean_path.read_text(encoding="utf-8")
        declared.update((relative, match.group(1)) for match in pattern.finditer(contents))

    assert declared == registered


def test_only_faithful_problem_statements_are_registered() -> None:
    atlas = load_atlas()
    expected = {
        "binary-erasure-channel",
        "binary-symmetric-channel",
        "discrete-memoryless-channel",
        "finite-dmc-input-cost",
        "finite-group-additive-noise-channel",
        "noiseless-q-ary-channel",
        "q-ary-symmetric-channel",
        "seven-cycle-zero-error-channel",
        "sun-jafar-11-message-index-coding",
        "sun-jafar-six-message-groupcast-index-coding",
    }

    stated = {
        problem["id"]
        for problem in atlas.problems
        if problem["formalization"]["status"] == "stated"
    }

    assert stated == expected


def test_removed_statement_shells_are_definitions_only() -> None:
    atlas = load_atlas()
    downgraded = {
        "binary-insertion-channel",
        "binary-skew-symmetric-broadcast-channel",
        "blackwell-broadcast-channel",
        "gaussian-mimo-channel",
        "general-finite-wiretap-channel",
        "index-coding-at-most-five-messages",
        "less-noisy-broadcast-channel",
        "more-capable-broadcast-channel",
        "primitive-relay-channel",
        "strong-interference-two-user-dmc",
        "trapdoor-channel-with-feedback",
        "trapdoor-channel-without-feedback",
    }

    for problem_id in downgraded:
        formalization = atlas.problems_by_id[problem_id]["formalization"]
        assert formalization["status"] == "definitions"
        assert formalization["claims"] == []


def test_formal_claims_have_independent_identity_and_status() -> None:
    atlas = load_atlas()
    claims = atlas.problems_by_id["sun-jafar-11-message-index-coding"]["formalization"]["claims"]
    claims_by_id = {claim["id"]: claim for claim in claims}

    assert claims_by_id["linear-achievability"]["kind"] == "achievability"
    assert claims_by_id["linear-achievability"]["category"] == "solved"
    assert claims_by_id["linear-achievability"]["formal_status"] == "stated"
    assert claims_by_id["exact-capacity"]["category"] == "open"
    assert claims_by_id["exact-capacity"]["formal_status"] == "stated"
    assert claims_by_id["internal-conflicts-exact"]["kind"] == "structural"
    assert claims_by_id["internal-conflicts-exact"]["category"] == "test"
    assert claims_by_id["internal-conflicts-exact"]["formal_status"] == "proved"


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


def test_open_claim_requires_theorem_declaration() -> None:
    atlas = deepcopy(load_atlas())
    problem = atlas.problems_by_id["sun-jafar-11-message-index-coding"]
    files = problem["formalization"]["files"]
    problem["formalization"]["files"] = [
        entry for entry in files if entry.get("claim_id") != "exact-capacity"
    ]

    messages = [issue.message for issue in validate_atlas(atlas)]

    assert any(
        "formal claim 'exact-capacity' needs one theorem or lemma declaration" in message
        for message in messages
    )


def test_open_claim_cannot_be_formally_proved() -> None:
    atlas = deepcopy(load_atlas())
    problem = atlas.problems_by_id["binary-symmetric-channel"]
    claim = next(
        claim
        for claim in problem["formalization"]["claims"]
        if claim["id"] == "operational-capacity"
    )
    claim["category"] = "open"

    messages = [issue.message for issue in validate_atlas(atlas)]

    assert any(
        "open claim 'operational-capacity' cannot be formally proved" in message
        for message in messages
    )


def test_formally_stated_claim_uses_sorry() -> None:
    atlas = deepcopy(load_atlas())
    problem = atlas.problems_by_id["binary-symmetric-channel"]
    claim = next(
        claim
        for claim in problem["formalization"]["claims"]
        if claim["id"] == "operational-capacity"
    )
    claim["formal_status"] = "stated"

    messages = [issue.message for issue in validate_atlas(atlas)]

    assert any(
        "formally stated claim 'operational-capacity' must use `sorry`" in message
        for message in messages
    )


def test_reusable_api_claim_cannot_contain_placeholder() -> None:
    atlas = deepcopy(load_atlas())
    problem = atlas.problems_by_id["seven-cycle-zero-error-channel"]
    claim = problem["formalization"]["claims"][0]
    claim["category"] = "API"

    messages = [issue.message for issue in validate_atlas(atlas)]

    assert any(
        "reusable API claim 'capacity-bounds' contains a placeholder" in message
        for message in messages
    )


def test_structural_proof_does_not_prove_capacity_claim() -> None:
    atlas = load_atlas()
    problem = atlas.problems_by_id["sun-jafar-11-message-index-coding"]
    structural = next(
        claim
        for claim in problem["formalization"]["claims"]
        if claim["id"] == "internal-conflicts-exact"
    )
    assert structural["kind"] == "structural"
    assert structural["formal_status"] == "proved"
    assert not any(
        claim["kind"] != "structural" and claim["formal_status"] == "proved"
        for claim in problem["formalization"]["claims"]
    )
