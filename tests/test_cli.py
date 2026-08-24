# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

from datetime import date
from pathlib import Path

import pytest

from capacity_atlas import cli
from capacity_atlas.model import Atlas
from capacity_atlas.validate import ValidationIssue


def _atlas(root: Path) -> Atlas:
    problem_dir = root / "data" / "problems"
    problem_dir.mkdir(parents=True)
    problem_files = {
        "first-problem": problem_dir / "first-problem.yaml",
        "second-problem": problem_dir / "second-problem.yaml",
    }
    for path in problem_files.values():
        path.write_text("placeholder\n", encoding="utf-8")
    return Atlas(
        root=root,
        site={},
        tag_axes={},
        references={},
        problems=[{"id": problem_id} for problem_id in problem_files],
        problem_files=problem_files,
    )


def test_new_scaffolds_problem_from_template(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    root = tmp_path / "atlas"
    template = root / "docs" / "problem-template.yaml"
    template.parent.mkdir(parents=True)
    template.write_text(
        "id: example-channel\ntitle: Example channel\nupdated: 2020-01-01\n",
        encoding="utf-8",
    )
    (root / "data" / "problems").mkdir(parents=True)

    result = cli.main(["--root", str(root), "new", "sample-channel"])

    destination = root / "data" / "problems" / "sample-channel.yaml"
    assert result == 0
    assert destination.read_text(encoding="utf-8") == (
        f"id: sample-channel\ntitle: Example channel\nupdated: {date.today().isoformat()}\n"
    )
    assert capsys.readouterr().out == (
        "Created data/problems/sample-channel.yaml. Complete its placeholders before validating.\n"
    )


def test_new_does_not_overwrite_existing_problem(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    root = tmp_path / "atlas"
    template = root / "docs" / "problem-template.yaml"
    template.parent.mkdir(parents=True)
    template.write_text("id: example-channel\n", encoding="utf-8")
    destination = root / "data" / "problems" / "sample-channel.yaml"
    destination.parent.mkdir(parents=True)
    destination.write_text("keep me\n", encoding="utf-8")

    result = cli.main(["--root", str(root), "new", "sample-channel"])

    assert result == 1
    assert destination.read_text(encoding="utf-8") == "keep me\n"
    assert "already exists" in capsys.readouterr().err


def test_new_rejects_unsafe_problem_id(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    result = cli.main(["--root", str(tmp_path), "new", "../sample-channel"])

    assert result == 1
    assert not list(tmp_path.rglob("*.yaml"))
    assert "Problem IDs use lowercase letters" in capsys.readouterr().err


def test_validate_paths_prints_selected_and_global_issues(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    atlas = _atlas(tmp_path)
    issues = [
        ValidationIssue("data/problems/first-problem.yaml", "selected issue"),
        ValidationIssue("data/problems/second-problem.yaml", "other issue"),
        ValidationIssue("lean/environment", "global issue"),
    ]
    loaded: list[Path] = []

    def load(root: Path) -> Atlas:
        loaded.append(root)
        return atlas

    monkeypatch.setattr(cli, "load_atlas", load)
    monkeypatch.setattr(cli, "validate_atlas", lambda atlas, report: issues)

    result = cli.main(["--root", str(tmp_path), "validate", "data/problems/first-problem.yaml"])

    output = capsys.readouterr()
    assert result == 1
    assert loaded == [tmp_path.resolve()]
    assert "selected issue" in output.err
    assert "global issue" in output.err
    assert "other issue" not in output.err
    assert "Validation failed with 2 issue(s)." in output.err


def test_validate_paths_reports_full_registry_load_failures(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    def fail_to_load(root: Path) -> Atlas:
        raise ValueError("broken registry")

    monkeypatch.setattr(cli, "load_atlas", fail_to_load)

    result = cli.main(["--root", str(tmp_path), "validate", "data/problems/first-problem.yaml"])

    assert result == 1
    assert "Could not load registry: broken registry" in capsys.readouterr().err


def test_validate_paths_reports_selected_success(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    atlas = _atlas(tmp_path)
    monkeypatch.setattr(cli, "load_atlas", lambda root: atlas)
    monkeypatch.setattr(cli, "validate_atlas", lambda atlas, report: [])

    result = cli.main(["--root", str(tmp_path), "validate", "data/problems/first-problem.yaml"])

    assert result == 0
    assert capsys.readouterr().out == "Selected problem data is valid.\n"
