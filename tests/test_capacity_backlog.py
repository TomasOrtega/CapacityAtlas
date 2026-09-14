# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0
"""Bookkeeping and scope regressions. Lean ModelSanity tests mathematical definitions."""

import json
from copy import deepcopy
from pathlib import Path

import pytest
import yaml

from capacity_atlas.backlog import target_claims
from capacity_atlas.data import load_atlas
from capacity_atlas.validate import validate_atlas

ROOT = Path(__file__).resolve().parents[1]


def backlog():
    return json.loads((ROOT / "docs/capacity-backlog.json").read_text())["problems"]


def test_backlog_has_fifty_problems_and_explicit_targets():
    entries = backlog()
    assert [entry["order"] for entry in entries] == list(range(1, 51))
    assert len({entry["problem"] for entry in entries}) == 50
    for entry in entries:
        assert all(1 <= prior < entry["order"] for prior in entry["reuse"])
        record = yaml.safe_load((ROOT / f"data/problems/{entry['problem']}.yaml").read_text())
        resolved = target_claims(entry, record)
        assert resolved
        assert entry["completion"]["requires"] == "all-target-claims-proved"
        linked = {ident for claim in resolved for ident in claim.get("bound_ids", [])}
        assert set(entry["selected_bound_ids"]) == linked
        assert not set(entry.get("deferred_bound_ids", [])) & linked


def test_sun_jafar_open_conjecture_is_context_only():
    entry = backlog()[-1]
    problem = load_atlas().problems_by_id[entry["problem"]]
    assert "exact-capacity" in entry["context_claims"]
    assert "exact-capacity" not in entry["target_claims"]
    assert {claim["id"] for claim in target_claims(entry, problem)} == {
        "linear-achievability",
        "unrestricted-achievability",
        "linear-converse",
        "nonlinear-converse",
    }
    wrong = deepcopy(entry)
    wrong["context_claims"].remove("exact-capacity")
    wrong["target_claims"].append("exact-capacity")
    with pytest.raises(ValueError, match="solved literature claims"):
        target_claims(wrong, problem)


def test_remaining_claim_manifest_matches_imports_and_registry():
    claims = json.loads((ROOT / "docs/remaining-capacity-claims.json").read_text())
    assert {claim["order"] for claim in claims} == set(range(9, 50))
    assert len({(claim["problem"], claim["claim_id"]) for claim in claims}) == len(claims)
    imports = (ROOT / "lean/CapacityAtlas/Claims.lean").read_text().splitlines()
    for claim in claims:
        assert f"import {claim['module']}" in imports
        assert (ROOT / claim["path"]).is_file()
        record = yaml.safe_load((ROOT / f"data/problems/{claim['problem']}.yaml").read_text())
        registered = next(
            c for c in record["formalization"]["claims"] if c["id"] == claim["claim_id"]
        )
        assert registered["version"] == claim["version"]
        assert registered["kind"] == claim["kind"]
        assert registered["bound_ids"] == claim["bound_ids"]
        assert any(
            link["role"] == "claim"
            and link.get("claim_id") == claim["claim_id"]
            and link["path"] == claim["path"]
            and link["declaration"] == claim["declaration"]
            for link in record["formalization"]["files"]
        )


def test_unknown_literature_bound_is_rejected():
    atlas = deepcopy(load_atlas())
    claim = atlas.problems_by_id["general-relay-channel"]["formalization"]["claims"][0]
    claim["bound_ids"] = ["missing-literature-bound"]
    assert any("links unknown literature bound" in issue.message for issue in validate_atlas(atlas))


def test_gaussian_power_conventions_match_model_assumptions():
    conventions = json.loads((ROOT / "docs/gaussian-power-conventions.json").read_text())
    assert {entry["order"] for entry in conventions} == set(range(30, 40))
    for entry in conventions:
        record = yaml.safe_load((ROOT / f"data/problems/{entry['problem']}.yaml").read_text())
        assert entry["model_assumption"] in record["model"]["assumptions"]
        assert entry["predicate"].rsplit(".", 1)[-1] in record["formalization"]["notes"]


def test_interface_obligations_are_explicit_unproved_propositions():
    obligations = json.loads((ROOT / "docs/interface-obligations.json").read_text())
    ids = {entry["id"] for entry in obligations}
    assert len(ids) == len(obligations)
    for entry in obligations:
        text = (ROOT / entry["path"]).read_text()
        assert f"def {entry['declaration'].rsplit('.', 1)[-1]} " in text
        assert entry["status"] == "specified-unproved"
    for entry in backlog():
        assert set(entry["interface_obligations"]) <= ids
    imports = (ROOT / "lean/CapacityAtlas.lean").read_text()
    assert "import CapacityAtlas.Obligations.Interfaces" in imports
    assert "import CapacityAtlas.Tests.ModelSanity" in imports


def test_basic_information_does_not_import_converses():
    pending = ["CapacityAtlasForMathlib.InformationTheory.FiniteInformation"]
    seen = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = ROOT / "lean" / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            continue
        for line in path.read_text().splitlines():
            if line.startswith("import CapacityAtlas"):
                pending.append(line.split()[1])
    assert not any("CodingConverse" in module or "OperationalCapacity" in module for module in seen)
