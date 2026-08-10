# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

import json
import shutil
from collections import Counter
from datetime import UTC, datetime
from pathlib import Path
from typing import Any
from urllib.parse import quote

from jinja2 import Environment, FileSystemLoader, StrictUndefined, select_autoescape

from .data import json_ready
from .validate import assert_valid


def _base_url(value: str) -> str:
    return "" if not value or value == "/" else "/" + value.strip("/")


def _authors(authors: list[str]) -> str:
    if not authors:
        return ""
    if len(authors) == 1:
        return authors[0]
    if len(authors) == 2:
        return f"{authors[0]} and {authors[1]}"
    return f"{', '.join(authors[:-1])}, and {authors[-1]}"


def build_site(
    root: Path | None = None,
    output: Path | None = None,
    base_url: str | None = None,
) -> Path:
    atlas = assert_valid(root)
    destination = (output or atlas.root / "dist").resolve()
    base = _base_url(str(base_url if base_url is not None else atlas.site.get("base_url", "")))
    if destination.exists():
        shutil.rmtree(destination)
    destination.mkdir(parents=True)

    env = Environment(
        loader=FileSystemLoader(atlas.root / "site" / "templates"),
        autoescape=select_autoescape(["html", "xml"]),
        undefined=StrictUndefined,
        trim_blocks=True,
        lstrip_blocks=True,
    )
    env.filters["authors"] = _authors

    def site_url(path: str = "") -> str:
        clean = path.lstrip("/")
        return f"{base}/{clean}" if clean and base else f"/{clean}" if clean else f"{base}/" or "/"

    def edit_url(problem_id: str) -> str:
        path = atlas.problem_files[problem_id].relative_to(atlas.root).as_posix()
        return f"{atlas.site['repository_url']}/edit/main/{path}"

    def discussion_url(problem: dict[str, Any]) -> str:
        term = f"capacityatlas:{problem['id']}"
        query = quote(term)
        return f"{atlas.site['repository_url']}/discussions?discussions_q={query}"

    env.globals.update(site_url=site_url, edit_url=edit_url, discussion_url=discussion_url)

    tag_values = atlas.tag_values
    problems = sorted(
        atlas.problems,
        key=lambda problem: (
            not problem.get("featured", False),
            problem["title"].lower(),
        ),
    )
    references = atlas.references
    for problem in problems:
        problem.setdefault("abbreviation", "")
        problem.setdefault("featured", False)
        problem.setdefault("parameters", [])
        problem.setdefault("timeline", [])
        problem.setdefault("frontier", None)
        problem["capacity"].setdefault("conditions", "")
        problem["capacity"].setdefault("lower", "")
        problem["capacity"].setdefault("upper", "")
        problem["capacity"].setdefault("conjectured", "")
        problem["capacity"].setdefault("notes", "")
        problem["quantity"].setdefault("criterion", "")
        problem["formalization"].setdefault("proofs", [])
        statement = problem["formalization"]["statement"]
        statement.setdefault("notes", "")
        statement.setdefault("files", [])
        for bound in problem["bounds"]:
            bound.setdefault("conditions", "")
            bound.setdefault("notes", "")
        if problem["frontier"]:
            problem["frontier"].setdefault("subproblems", [])
            for item in problem["frontier"]["subproblems"]:
                item.setdefault("url", "")
        problem["tag_groups"] = [
            {
                "axis": axis_id,
                "label": atlas.tag_axes[axis_id]["label"],
                "values": [tag_values[axis_id][tag_id] for tag_id in problem["tags"][axis_id]],
            }
            for axis_id in atlas.tag_axes
        ]
        all_tags = [tag for selected in problem["tags"].values() for tag in selected]
        problem["search_text"] = " ".join(
            [problem["title"], problem.get("abbreviation", ""), problem["summary"], *all_tags]
        ).lower()
        problem["resolved_references"] = [
            references[ref_id] | {"id": ref_id} for ref_id in problem["references"]
        ]
        problem["discussion_term"] = f"capacityatlas:{problem['id']}"

    status_counts = Counter(problem["status"] for problem in problems)
    stats = {
        "total": len(problems),
        "open": status_counts["open"],
        "partial": status_counts["partially-solved"],
        "solved": status_counts["solved"],
        "statements": sum(
            problem["formalization"]["statement"]["status"] != "none" for problem in problems
        ),
        "proofs": sum(len(problem["formalization"]["proofs"]) for problem in problems),
    }
    facets: dict[str, list[dict[str, Any]]] = {}
    for axis_id, axis in atlas.tag_axes.items():
        counts = Counter(tag for problem in problems for tag in problem["tags"][axis_id])
        facets[axis_id] = [
            value | {"count": counts[value["id"]]}
            for value in axis["values"]
            if counts[value["id"]]
        ]

    giscus = atlas.site.get("social", {}).get("giscus", {})
    giscus_ready = bool(
        atlas.site.get("social", {}).get("discussions_enabled")
        and giscus.get("enabled")
        and giscus.get("repo_id")
        and giscus.get("category_id")
    )
    common = {
        "site": atlas.site,
        "problems": problems,
        "stats": stats,
        "tag_axes": atlas.tag_axes,
        "facets": facets,
        "giscus": giscus,
        "giscus_ready": giscus_ready,
        "build_time": datetime.now(UTC),
    }

    def render(template: str, path: str, **context: Any) -> None:
        target = destination / path
        target.parent.mkdir(parents=True, exist_ok=True)
        request_path = "" if path == "index.html" else path.removesuffix("index.html")
        target.write_text(
            env.get_template(template).render(
                **common, request_path=request_path, **context
            ),
            encoding="utf-8",
        )

    featured = [problem for problem in problems if problem["featured"]]
    recent = sorted(problems, key=lambda p: str(p["updated"]), reverse=True)[:8]
    render("index.html", "index.html", page_id="home", featured=featured, recent=recent)
    render("problems.html", "problems/index.html", page_id="problems")
    render("formalizations.html", "formalizations/index.html", page_id="formalizations")
    render("contribute.html", "contribute/index.html", page_id="contribute")
    render("about.html", "about/index.html", page_id="about")
    render("api.html", "api/index.html", page_id="api")
    render("404.html", "404.html", page_id="404")

    for problem in problems:
        def overlap(other: dict[str, Any]) -> int:
            return sum(
                bool(set(problem["tags"][axis]) & set(other["tags"][axis]))
                for axis in atlas.tag_axes
            )

        related = sorted(
            (
                other
                for other in problems
                if other["id"] != problem["id"] and overlap(other) > 0
            ),
            key=lambda other: (-overlap(other), other["title"]),
        )[:4]
        render(
            "problem.html",
            f"problems/{problem['id']}/index.html",
            page_id="problem",
            page_title=problem["title"],
            page_description=problem["summary"],
            problem=problem,
            related=related,
        )

    shutil.copytree(atlas.root / "site" / "static", destination / "assets", dirs_exist_ok=True)
    api = destination / "api"
    (api / "problems").mkdir(parents=True)
    public = []
    for problem in problems:
        payload = {
            key: value
            for key, value in problem.items()
            if key not in {"tag_groups", "search_text", "resolved_references", "discussion_term"}
        }
        payload["url"] = site_url(f"problems/{problem['id']}/")
        payload = json_ready(payload)
        public.append(payload)
        (api / "problems" / f"{problem['id']}.json").write_text(
            json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )
    (api / "problems.json").write_text(
        json.dumps(public, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (api / "references.json").write_text(
        json.dumps(json_ready(references), indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (api / "tags.json").write_text(
        json.dumps(json_ready(atlas.tag_axes), indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    shutil.copy2(atlas.root / "schema" / "problem.schema.json", api / "problem.schema.json")

    canonical = str(atlas.site["canonical_url"]).rstrip("/")
    paths = ["", "problems/", "formalizations/", "contribute/", "about/", "api/"] + [
        f"problems/{problem['id']}/" for problem in problems
    ]
    sitemap = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<urlset xmlns="http://www.sitemaps.org/sitemap/0.9">',
        *(f"  <url><loc>{canonical}/{path}</loc></url>" for path in paths),
        "</urlset>",
        "",
    ]
    (destination / "sitemap.xml").write_text("\n".join(sitemap), encoding="utf-8")
    (destination / "robots.txt").write_text(
        f"User-agent: *\nAllow: /\nSitemap: {canonical}/sitemap.xml\n", encoding="utf-8"
    )
    (destination / ".nojekyll").touch()
    return destination
