# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

import json
from pathlib import Path

from bs4 import BeautifulSoup

from capacity_atlas.build import _browse_formalization, build_site


def test_build_writes_pages_and_api(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    assert (output / "index.html").is_file()
    assert (output / "problems" / "index.html").is_file()
    assert not (output / "formalizations" / "index.html").exists()
    assert (output / "api" / "tags.json").is_file()

    problems = json.loads((output / "api" / "problems.json").read_text(encoding="utf-8"))
    assert problems
    assert all(problem["url"].startswith("/problems/") for problem in problems)
    assert all("tags" in problem for problem in problems)
    assert all("browse_formalization" not in problem for problem in problems)


def test_production_urls_use_custom_domain_root(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    home = (output / "index.html").read_text(encoding="utf-8")
    problem = (output / "problems" / "binary-symmetric-channel" / "index.html").read_text(
        encoding="utf-8"
    )

    assert 'href="https://capacityatlas.org/"' in home
    assert 'href="https://capacityatlas.org/problems/binary-symmetric-channel/"' in problem
    assert 'href="/assets/styles.css"' in home
    assert 'href="/problems/"' in home
    assert 'href="/CapacityAtlas/' not in home
    assert 'src="/CapacityAtlas/' not in home


def test_problem_page_exposes_versioned_claims_and_active_giscus(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (output / "problems" / "binary-symmetric-channel" / "index.html").read_text(
        encoding="utf-8"
    )
    soup = BeautifulSoup(page, "html.parser")
    giscus = soup.select_one('script[src="https://giscus.app/client.js"]')

    assert "operational-capacity" in soup.get_text(" ", strip=True)
    assert "v2" in soup.get_text(" ", strip=True)
    assert "capacityatlas:binary-symmetric-channel" in page
    assert "discussions/new?category=general" in page
    assert giscus is not None
    assert giscus["data-repo"] == "TomasOrtega/CapacityAtlas"
    assert giscus["data-repo-id"] == "R_kgDOTzuIlQ"
    assert giscus["data-category"] == "General"
    assert giscus["data-category-id"] == "DIC_kwDOTzuIlc4DDFDj"
    assert giscus["data-mapping"] == "specific"
    assert giscus["data-term"] == "capacityatlas:binary-symmetric-channel"
    assert giscus["data-strict"] == "1"
    assert "GitHub Discussions is enabled" not in page
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


def test_browse_filters_keep_status_and_formalization_separate(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (output / "problems" / "index.html").read_text(encoding="utf-8")
    soup = BeautifulSoup(page, "html.parser")
    status_filter = soup.select_one('select[name="status"]')
    formalization_filter = soup.select_one('select[name="formalization"]')

    assert status_filter is not None
    assert formalization_filter is not None
    assert [option.get("value", "") for option in status_filter.select("option")] == [
        "",
        "open",
        "partially-solved",
        "solved",
    ]
    formalization_options = {
        option.get("value", ""): option.get_text(" ", strip=True)
        for option in formalization_filter.select("option")
    }
    assert formalization_options["formally-stated"].startswith("Formally stated")
    assert formalization_options["formally-proved"].startswith("Capacity claim formally proved")
    assert not formalization_options["formally-proved"].endswith("(0)")

    formalized_row = soup.select_one('[data-problem-row][data-formalization~="formally-stated"]')
    assert formalized_row is not None
    assert formalized_row.get("data-status") in {
        "open",
        "partially-solved",
        "solved",
    }
    assert "formally-stated" not in formalized_row.get("data-status", "")

    bsc_link = soup.select_one('a[href="/problems/binary-symmetric-channel/"]')
    assert bsc_link is not None
    bsc_row = bsc_link.find_parent(attrs={"data-problem-row": True})
    assert bsc_row is not None
    assert "formally-proved" in bsc_row.get("data-formalization", "").split()

    sun_jafar_link = soup.select_one('a[href="/problems/sun-jafar-11-message-index-coding/"]')
    assert sun_jafar_link is not None
    sun_jafar_row = sun_jafar_link.find_parent(attrs={"data-problem-row": True})
    assert sun_jafar_row is not None
    assert "formally-proved" not in sun_jafar_row.get("data-formalization", "").split()


def test_browse_formalization_includes_proved_capacity_claim() -> None:
    problem = {
        "status": "open",
        "formalization": {
            "statement": {
                "status": "statement",
                "claims": [
                    {
                        "kind": "converse",
                        "status": "proved",
                    }
                ],
            },
        },
    }

    assert _browse_formalization(problem) == [
        "formally-stated",
        "formally-proved",
    ]


def test_browse_formalization_excludes_structural_proof() -> None:
    problem = {
        "status": "solved",
        "formalization": {
            "statement": {
                "status": "statement",
                "claims": [
                    {
                        "kind": "structural",
                        "status": "proved",
                    }
                ],
            },
        },
    }

    assert _browse_formalization(problem) == [
        "formally-stated",
    ]


def test_home_is_compact_faceted_registry(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (output / "index.html").read_text(encoding="utf-8")
    soup = BeautifulSoup(page, "html.parser")

    assert soup.select_one(".stats__grid")
    assert not soup.select(".eyebrow")
    headings = {heading.get_text(" ", strip=True) for heading in soup.select(".browse-group h3")}
    assert headings == {"Channel model", "Features", "Quantity", "Current knowledge"}
    assert "Formal Conjectures" in soup.get_text(" ", strip=True)
    assert "lean" not in page.lower()
    assert "Formally stated" in soup.get_text(" ", strip=True)
    assert "Formally proved" in soup.get_text(" ", strip=True)


def test_typography_uses_a_balanced_scale() -> None:
    css = Path("site/static/styles.css").read_text(encoding="utf-8")
    assert "--title-xl: clamp(2.2rem, 5vw, 3.6rem)" in css
    assert "--text-sm: .84rem" in css
    assert "5.4rem" not in css
    assert "font-size: .72rem" not in css


def test_license_split_is_visible(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (output / "index.html").read_text(encoding="utf-8")
    assert "Apache-2.0" in page
    assert "CC-BY-4.0" in page
