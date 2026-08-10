# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

import json
from pathlib import Path

from bs4 import BeautifulSoup

from capacity_atlas.build import build_site


def test_build_writes_pages_and_api(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    assert (output / "index.html").is_file()
    assert (output / "problems" / "index.html").is_file()
    assert not (output / "formalizations" / "index.html").exists()
    assert (output / "api" / "tags.json").is_file()

    problems = json.loads((output / "api" / "problems.json").read_text(encoding="utf-8"))
    assert len(problems) == 32
    assert all(problem["url"].startswith("/problems/") for problem in problems)
    assert all("tags" in problem for problem in problems)


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
    assert 'href="/CapacityAtlas/' not in home
    assert 'src="/CapacityAtlas/' not in home


def test_problem_page_exposes_versioned_lean_and_discussion(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (output / "problems" / "binary-symmetric-channel" / "index.html").read_text(
        encoding="utf-8"
    )
    soup = BeautifulSoup(page, "html.parser")

    assert "Version 1" in soup.get_text(" ", strip=True)
    assert "capacityatlas:binary-symmetric-channel" in page
    assert "GitHub Discussions is enabled" in page
    assert "giscus GitHub App" in page
    assert "discussions/new?category=general" in page
    assert "Inline discussion is ready but not yet activated" not in page
    assert "Edit this entry" in page
    assert "data/problems/binary-symmetric-channel.yaml" in page


def test_navigation_has_discussions_without_a_lean_tab(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (output / "index.html").read_text(encoding="utf-8")
    soup = BeautifulSoup(page, "html.parser")
    labels = [link.get_text(" ", strip=True) for link in soup.select("#site-nav a")]

    assert "Discussions" in labels
    assert "Lean" not in labels
    assert not soup.select('a[href="/formalizations/"]')


def test_home_is_compact_faceted_registry(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (output / "index.html").read_text(encoding="utf-8")
    soup = BeautifulSoup(page, "html.parser")

    assert soup.select_one(".stats__grid")
    assert not soup.select(".eyebrow")
    headings = {heading.get_text(" ", strip=True) for heading in soup.select(".browse-group h3")}
    assert headings == {"Channel model", "Features", "Quantity", "Current knowledge"}
    assert "Formal Conjectures" in soup.get_text(" ", strip=True)


def test_typography_uses_a_balanced_scale() -> None:
    css = Path("site/static/styles.css").read_text(encoding="utf-8")
    assert "--title-xl: clamp(2.2rem, 5vw, 3.6rem)" in css
    assert "--text-sm: 0.84rem" in css
    assert "5.4rem" not in css
    assert "font-size: 0.72rem" not in css


def test_license_split_is_visible(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (output / "index.html").read_text(encoding="utf-8")
    assert "Apache-2.0" in page
    assert "CC-BY-4.0" in page
