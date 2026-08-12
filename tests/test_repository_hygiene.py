# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

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
