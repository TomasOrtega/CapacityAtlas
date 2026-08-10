# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
from urllib.parse import unquote, urlsplit

from bs4 import BeautifulSoup

from capacity_atlas.build import build_site


def _resolve_internal_target(output: Path, source: Path, url: str) -> Path | None:
    parsed = urlsplit(url)
    if parsed.scheme or parsed.netloc or url.startswith(("mailto:", "tel:")):
        return None
    if not parsed.path:
        return source

    decoded = unquote(parsed.path)
    target = output / decoded.lstrip("/") if decoded.startswith("/") else source.parent / decoded
    if decoded.endswith("/") or target.is_dir():
        target = target / "index.html"
    return target.resolve()


def test_every_generated_internal_link_has_a_target(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")
    missing: list[str] = []

    for page in output.rglob("*.html"):
        soup = BeautifulSoup(page.read_text(encoding="utf-8"), "html.parser")
        for element in soup.select("[href], [src]"):
            url = element.get("href") or element.get("src")
            assert isinstance(url, str)
            target = _resolve_internal_target(output, page, url)
            if target is not None and not target.exists():
                missing.append(f"{page.relative_to(output)} -> {url}")

    assert missing == []


def test_generated_pages_have_unique_ids_and_no_template_markers(tmp_path: Path) -> None:
    output = build_site(output=tmp_path / "site")

    for page in output.rglob("*.html"):
        contents = page.read_text(encoding="utf-8")
        assert "{{" not in contents
        assert "{%" not in contents
        soup = BeautifulSoup(contents, "html.parser")
        ids = [element["id"] for element in soup.select("[id]")]
        assert len(ids) == len(set(ids)), page
