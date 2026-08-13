# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

import re
from collections import Counter
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[1]


def test_issue_forms_have_unique_names_and_titles() -> None:
    forms = sorted((ROOT / ".github" / "ISSUE_TEMPLATE").glob("*.yml"))
    definitions = [yaml.safe_load(form.read_text(encoding="utf-8")) for form in forms]

    for field in ("name", "title"):
        values = [definition[field] for definition in definitions if field in definition]
        duplicates = sorted(value for value, count in Counter(values).items() if count > 1)
        assert duplicates == [], field


def test_temporary_ci_files_are_absent() -> None:
    temporary_files = [
        ROOT / ".ci-runtime-debug",
        ROOT / ".ci-workflow-marker",
        ROOT / ".github" / "workflows" / "debug-lean-runtime.yml",
        ROOT / ".github" / "workflows" / "export-lean-runtime-bits.yml",
        ROOT / ".github" / "workflows" / "export-lean-runtime-direct.yml",
        ROOT / ".github" / "workflows" / "export-lean-runtime-manifest-v2.yml",
        ROOT / ".github" / "workflows" / "export-lean-runtime-manifest.yml",
        ROOT / ".github" / "workflows" / "export-lean-runtime-simple.yml",
        ROOT / ".github" / "workflows" / "export-lean-runtime.yml",
        ROOT / ".github" / "workflows" / "test-branch-write.yml",
    ]

    assert [str(path.relative_to(ROOT)) for path in temporary_files if path.exists()] == []


def test_lean_ci_uses_layered_warning_boundary() -> None:
    workflow = (ROOT / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")

    assert "lake --wfail build CapacityAtlasForMathlib CapacityAtlasUtil" in workflow
    assert "lake --wfail build CapacityAtlas" in workflow
    assert "lake exe capacity_audit" in workflow
    assert "--lean-report" in workflow
    assert "grep -RInE" not in workflow
    assert "Reject placeholders" not in workflow


def test_ci_actions_are_immutable_and_jobs_are_least_privilege() -> None:
    workflow_path = ROOT / ".github" / "workflows" / "ci.yml"
    workflow_text = workflow_path.read_text(encoding="utf-8")
    workflow = yaml.safe_load(workflow_text)

    action_refs = re.findall(r"^\s*- uses: [^@\s]+@([^\s#]+)", workflow_text, re.MULTILINE)
    assert action_refs
    assert all(re.fullmatch(r"[0-9a-f]{40}", ref) for ref in action_refs)

    assert workflow["permissions"] == {"contents": "read"}
    assert workflow["jobs"]["site"]["permissions"] == {"contents": "read"}
    assert workflow["jobs"]["lean"]["permissions"] == {"contents": "read"}
    assert workflow["jobs"]["deploy"]["permissions"] == {
        "pages": "write",
        "id-token": "write",
    }
    assert all("timeout-minutes" in job for job in workflow["jobs"].values())


def test_central_ci_excludes_external_proof_sandboxing() -> None:
    workflow = (ROOT / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")

    for excluded in ("leanprover/comparator", "lean4export", "landrun"):
        assert excluded not in workflow.lower()


def test_cc_by_license_contains_complete_legal_code() -> None:
    legal_code = (ROOT / "LICENSES" / "CC-BY-4.0.txt").read_text(encoding="utf-8")

    assert legal_code.startswith("Attribution 4.0 International\n")
    assert "Section 1 -- Definitions." in legal_code
    assert "Section 8 -- Interpretation." in legal_code
    assert legal_code.rstrip().endswith("Creative Commons may be contacted at creativecommons.org.")
    assert len(legal_code.splitlines()) > 350


def test_obsolete_lean_compatibility_surface_is_removed() -> None:
    obsolete = [
        ROOT / "lean" / "CapacityAtlas" / "Code.lean",
        ROOT / "lean" / "CapacityAtlas" / "FiniteChannel.lean",
        ROOT / "lean" / "CapacityAtlas" / "Network" / "IndexCoding.lean",
    ]
    assert [str(path.relative_to(ROOT)) for path in obsolete if path.exists()] == []

    lean = "\n".join(path.read_text(encoding="utf-8") for path in (ROOT / "lean").rglob("*.lean"))
    assert "ScalarOperationalTheory" not in lean
    assert "RegionOperationalTheory" not in lean
    assert "WiretapOperationalTheory" not in lean
    assert "linearSymmetricCapacity" not in lean
