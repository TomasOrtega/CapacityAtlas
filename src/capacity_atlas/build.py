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

FORMALIZATION_RANK = {
    "none": 0,
    "definitions": 1,
    "statement": 2,
    "partial": 3,
    "complete": 4,
}


def _normalise_base_url(base_url: str) -> str:
    if not base_url or base_url == "/":
        return ""
    return "/" + base_url.strip("/")


def _format_author_list(authors: list[str]) -> str:
    if not authors:
        return ""
    if len(authors) == 1:
        return authors[0]
    if len(authors) == 2:
        return f"{authors[0]} and {authors[1]}"
    return f"{', '.join(authors[:-1])}, and {authors[-1]}"


def _problem_search_text(problem: dict[str, Any], category_title: str) -> str:
    parts = [
        problem.get("title", ""),
        problem.get("abbreviation", ""),
        problem.get("summary", ""),
        category_title,
        " ".join(problem.get("tags", [])),
        problem.get("capacity", {}).get("display", ""),
    ]
    return " ".join(str(part) for part in parts if part).lower()


def build_site(
    root: Path | None = None,
    output: Path | None = None,
    base_url: str | None = None,
) -> Path:
    atlas = assert_valid(root)
    output_dir = (output or atlas.root / "dist").resolve()
    configured_base = base_url if base_url is not None else atlas.site.get("base_url", "")
    base = _normalise_base_url(str(configured_base))

    if output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.mkdir(parents=True)

    templates_dir = atlas.root / "site" / "templates"
    environment = Environment(
        loader=FileSystemLoader(templates_dir),
        autoescape=select_autoescape(["html", "xml"]),
        undefined=StrictUndefined,
        trim_blocks=True,
        lstrip_blocks=True,
    )

    def site_url(path: str = "") -> str:
        clean = path.lstrip("/")
        if not clean:
            return f"{base}/" if base else "/"
        return f"{base}/{clean}" if base else f"/{clean}"

    def github_edit_url(problem_id: str) -> str:
        path = atlas.problem_files[problem_id].relative_to(atlas.root).as_posix()
        return f"{atlas.site['repository_url']}/edit/main/{path}"

    def discussion_url(problem: dict[str, Any]) -> str:
        configured = problem.get("discussion", {}).get("url")
        if configured:
            return str(configured)
        title = quote(f"[Discussion] {problem['title']}")
        body = quote(
            f"Discussion for `{problem['id']}` in Capacity Atlas.\n\n"
            "Please cite specific bounds, assumptions, or formalization targets."
        )
        return f"{atlas.site['repository_url']}/issues/new?title={title}&body={body}"

    environment.globals.update(
        site_url=site_url,
        github_edit_url=github_edit_url,
        discussion_url=discussion_url,
        formalization_rank=FORMALIZATION_RANK,
    )
    environment.filters["authors"] = _format_author_list

    categories_by_id = atlas.categories_by_id
    references = atlas.references
    problems = sorted(
        atlas.problems,
        key=lambda item: (not bool(item.get("featured")), item["title"].lower()),
    )
    for problem in problems:
        problem.setdefault("abbreviation", "")
        problem.setdefault("featured", False)
        problem.setdefault("tags", [])
        problem.setdefault("parameters", [])
        problem.setdefault("timeline", [])
        problem.setdefault("frontier", None)
        problem.setdefault("discussion", {})
        problem["capacity"].setdefault("conditions", "")
        problem["capacity"].setdefault("lower", "")
        problem["capacity"].setdefault("upper", "")
        problem["capacity"].setdefault("conjectured", "")
        problem["capacity"].setdefault("notes", "")
        problem["quantity"].setdefault("criterion", "")
        problem["formalization"].setdefault("language", "")
        problem["formalization"].setdefault("notes", "")
        problem["formalization"].setdefault("files", [])
        for bound in problem["bounds"]:
            bound.setdefault("conditions", "")
            bound.setdefault("notes", "")
        if problem["frontier"] is not None:
            problem["frontier"].setdefault("subproblems", [])
            for subproblem in problem["frontier"]["subproblems"]:
                subproblem.setdefault("url", "")
        problem["category_data"] = categories_by_id[problem["category"]]
        problem["search_text"] = _problem_search_text(
            problem, categories_by_id[problem["category"]]["title"]
        )
        resolved = []
        for ref in problem["references"]:
            reference = references[ref] | {"id": ref}
            reference.setdefault("doi", "")
            reference.setdefault("arxiv", "")
            resolved.append(reference)
        problem["resolved_references"] = resolved

    status_counts = Counter(problem["status"] for problem in problems)
    formalization_counts = Counter(
        problem.get("formalization", {}).get("status", "none") for problem in problems
    )
    stats = {
        "total": len(problems),
        "solved": status_counts["solved"],
        "open": status_counts["open"],
        "partial": status_counts["partially-solved"],
        "lean_started": sum(
            count for status, count in formalization_counts.items() if status != "none"
        ),
        "lean_complete": formalization_counts["complete"],
    }
    common: dict[str, Any] = {
        "site": atlas.site,
        "categories": atlas.categories,
        "problems": problems,
        "stats": stats,
        "build_time": datetime.now(UTC),
        "base_url": base,
    }

    def render(template_name: str, destination: str, **context: Any) -> None:
        target = output_dir / destination
        target.parent.mkdir(parents=True, exist_ok=True)
        template = environment.get_template(template_name)
        target.write_text(template.render(**common, **context), encoding="utf-8")

    featured = [problem for problem in problems if problem.get("featured")]
    recent = sorted(problems, key=lambda item: str(item["updated"]), reverse=True)[:6]
    render("index.html", "index.html", featured=featured, recent=recent, page_id="home")
    render("problems.html", "problems/index.html", page_id="problems")
    render("formalizations.html", "formalizations/index.html", page_id="formalizations")
    render("contribute.html", "contribute/index.html", page_id="contribute")
    render("about.html", "about/index.html", page_id="about")
    render("api.html", "api/index.html", page_id="api")
    render("404.html", "404.html", page_id="404")

    for problem in problems:
        related = [
            candidate
            for candidate in problems
            if candidate["id"] != problem["id"]
            and (
                candidate["category"] == problem["category"]
                or set(candidate.get("tags", [])) & set(problem.get("tags", []))
            )
        ][:3]
        render(
            "problem.html",
            f"problems/{problem['id']}/index.html",
            problem=problem,
            related=related,
            page_id="problem",
            page_title=problem["title"],
            page_description=problem["summary"],
        )

    shutil.copytree(atlas.root / "site" / "static", output_dir / "assets", dirs_exist_ok=True)

    api_dir = output_dir / "api"
    api_dir.mkdir(exist_ok=True)
    public_problems = []
    for problem in problems:
        payload = {
            key: value
            for key, value in problem.items()
            if key not in {"category_data", "search_text", "resolved_references"}
        }
        payload["url"] = site_url(f"problems/{problem['id']}/")
        public_problems.append(json_ready(payload))
        problem_api = api_dir / "problems" / f"{problem['id']}.json"
        problem_api.parent.mkdir(parents=True, exist_ok=True)
        problem_api.write_text(
            json.dumps(json_ready(payload), indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )

    (api_dir / "problems.json").write_text(
        json.dumps(public_problems, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (api_dir / "references.json").write_text(
        json.dumps(json_ready(references), indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    shutil.copy2(atlas.root / "schema" / "problem.schema.json", api_dir / "problem.schema.json")

    search_index = [
        {
            "id": problem["id"],
            "title": problem["title"],
            "abbreviation": problem.get("abbreviation"),
            "summary": problem["summary"],
            "status": problem["status"],
            "category": problem["category"],
            "category_title": problem["category_data"]["title"],
            "formalization": problem["formalization"]["status"],
            "tags": problem.get("tags", []),
            "capacity": problem["capacity"]["display"],
            "url": site_url(f"problems/{problem['id']}/"),
            "search_text": problem["search_text"],
        }
        for problem in problems
    ]
    (output_dir / "assets" / "search-index.json").write_text(
        json.dumps(json_ready(search_index), indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )

    canonical = str(atlas.site.get("canonical_url", "")).rstrip("/")
    if canonical:
        urls = [
            "",
            "problems/",
            "formalizations/",
            "contribute/",
            "about/",
            "api/",
            *(f"problems/{problem['id']}/" for problem in problems),
        ]
        sitemap = [
            '<?xml version="1.0" encoding="UTF-8"?>',
            '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">',
            *(f"  <url><loc>{canonical}/{path}</loc></url>" for path in urls),
            "</urlset>",
            "",
        ]
        (output_dir / "sitemap.xml").write_text("\n".join(sitemap), encoding="utf-8")
        (output_dir / "robots.txt").write_text(
            f"User-agent: *\nAllow: /\nSitemap: {canonical}/sitemap.xml\n", encoding="utf-8"
        )

    (output_dir / ".nojekyll").touch()
    return output_dir
