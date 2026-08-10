import json
from pathlib import Path

from capacity_atlas.build import build_site


def test_build_writes_pages_and_api(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site", base_url="/CapacityAtlas")
    assert (output / "index.html").is_file()
    assert (output / "problems" / "index.html").is_file()
    assert (output / "formalizations" / "index.html").is_file()

    problems = json.loads((output / "api" / "problems.json").read_text(encoding="utf-8"))
    assert problems
    assert all(problem["url"].startswith("/CapacityAtlas/") for problem in problems)


def test_problem_pages_have_edit_links(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (output / "problems" / "binary-symmetric-channel" / "index.html").read_text(
        encoding="utf-8"
    )
    assert "Edit this entry" in page
    assert "data/problems/binary-symmetric-channel.yaml" in page
