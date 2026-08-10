import json
import re
from pathlib import Path

from bs4 import BeautifulSoup

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
    assert 'href="/CapacityAtlas/' not in home
    assert 'src="/CapacityAtlas/' not in home
    assert 'href="/CapacityAtlas/' not in problem
    assert 'src="/CapacityAtlas/' not in problem


def test_problem_pages_have_edit_links(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (output / "problems" / "binary-symmetric-channel" / "index.html").read_text(
        encoding="utf-8"
    )
    assert "Edit this entry" in page
    assert "data/problems/binary-symmetric-channel.yaml" in page


def test_problem_cards_do_not_include_capacity_formulas(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (output / "problems" / "index.html").read_text(encoding="utf-8")
    soup = BeautifulSoup(page, "html.parser")

    cards = soup.select("[data-problem-card]")
    assert cards
    assert not soup.select("[data-problem-card] .capacity-inline")


def test_model_definitions_keep_prose_outside_inline_math(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (
        output / "problems" / "two-user-discrete-memoryless-mac" / "index.html"
    ).read_text(encoding="utf-8")
    soup = BeautifulSoup(page, "html.parser")

    values = [element.get_text(strip=True) for element in soup.select(".definition-grid__value")]
    assert values == [
        r"Independent encoder inputs \(X_1\in\mathcal X_1\) and "
        r"\(X_2\in\mathcal X_2\).",
        r"A common receiver observes \(Y\in\mathcal Y\).",
        r"A memoryless transition law \(p(y\mid x_1,x_2)\).",
    ]


def test_problem_pages_do_not_expose_undelimited_tex(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")

    for page in (output / "problems").glob("*/index.html"):
        soup = BeautifulSoup(page.read_text(encoding="utf-8"), "html.parser")
        visible_text = soup.get_text(" ", strip=True)
        without_inline_math = re.sub(r"\\\(.*?\\\)", "", visible_text)
        without_math = re.sub(r"\\\[.*?\\\]", "", without_inline_math)
        assert "\\" not in without_math, page


def test_mac_converse_relation_is_a_formula(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    page = (
        output / "problems" / "two-user-discrete-memoryless-mac" / "index.html"
    ).read_text(encoding="utf-8")
    soup = BeautifulSoup(page, "html.parser")
    relation = soup.select(".table-wrap--bounds tbody tr td:nth-child(2)")[1].get_text(
        " ", strip=True
    )

    assert "The same three" not in relation
    assert r"R_1\le I(X_1;Y\mid X_2,Q)" in relation
