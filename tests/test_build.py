import json
from pathlib import Path

from capacity_atlas.build import build_site


def test_build_writes_pages_and_api(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    assert (output / "index.html").is_file()
    assert (output / "problems" / "index.html").is_file()
    assert (output / "formalizations" / "index.html").is_file()

    problems = json.loads((output / "api" / "problems.json").read_text(encoding="utf-8"))
    assert problems
    assert all(problem["url"].startswith("/problems/") for problem in problems)


def test_production_urls_use_custom_domain_root(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    home = (output / "index.html").read_text(encoding="utf-8")
    problem = (output / "problems" / "binary-symmetric-channel" / "index.html").read_text(
        encoding="utf-8"
    )

    assert 'href="https://capacityatlas.org/"' in home
    assert (
        'href="https://capacityatlas.org/problems/binary-symmetric-channel/"'
        in problem
    )
    assert 'href="/assets/styles.css"' in home
    assert 'href="/problems/"' in home
    assert "/CapacityAtlas/" not in home
    assert "/CapacityAtlas/" not in problem


def test_problem_pages_have_edit_links(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (output / "problems" / "binary-symmetric-channel" / "index.html").read_text(
        encoding="utf-8"
    )
    assert "Edit this entry" in page
    assert "data/problems/binary-symmetric-channel.yaml" in page
