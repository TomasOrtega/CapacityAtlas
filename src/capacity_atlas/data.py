from __future__ import annotations

from datetime import date, datetime
from pathlib import Path
from typing import Any

import yaml

from .model import Atlas


class AtlasDataError(RuntimeError):
    """Raised when atlas source data cannot be loaded."""


def find_root(start: Path | None = None) -> Path:
    current = (start or Path.cwd()).resolve()
    for candidate in (current, *current.parents):
        if (candidate / "pyproject.toml").is_file() and (candidate / "data").is_dir():
            return candidate
    raise AtlasDataError("Could not find the repository root from the current directory.")


def load_yaml(path: Path) -> Any:
    try:
        with path.open("r", encoding="utf-8") as handle:
            return yaml.safe_load(handle)
    except (OSError, yaml.YAMLError) as exc:
        raise AtlasDataError(f"Could not load {path}: {exc}") from exc


def load_atlas(root: Path | None = None) -> Atlas:
    repo_root = (root or find_root()).resolve()
    site = load_yaml(repo_root / "data" / "site.yaml")
    categories_data = load_yaml(repo_root / "data" / "categories.yaml")
    references = load_yaml(repo_root / "data" / "references.yaml")

    if not isinstance(site, dict):
        raise AtlasDataError("data/site.yaml must contain a mapping.")
    if (
        not isinstance(categories_data, dict)
        or not isinstance(categories_data.get("categories"), list)
    ):
        raise AtlasDataError("data/categories.yaml must contain a categories list.")
    if not isinstance(references, dict):
        raise AtlasDataError("data/references.yaml must contain a mapping.")

    problems: list[dict[str, Any]] = []
    problem_files: dict[str, Path] = {}
    for path in sorted((repo_root / "data" / "problems").glob("*.yaml")):
        problem = load_yaml(path)
        if not isinstance(problem, dict):
            raise AtlasDataError(f"{path} must contain a mapping.")
        problem_id = problem.get("id")
        if not isinstance(problem_id, str) or not problem_id:
            raise AtlasDataError(f"{path} must define a non-empty string id.")
        problems.append(problem)
        problem_files[problem_id] = path

    return Atlas(
        root=repo_root,
        site=site,
        categories=categories_data["categories"],
        references=references,
        problems=problems,
        problem_files=problem_files,
    )


def json_ready(value: Any) -> Any:
    """Convert YAML values such as dates into JSON-safe values."""
    if isinstance(value, dict):
        return {str(key): json_ready(item) for key, item in value.items()}
    if isinstance(value, list):
        return [json_ready(item) for item in value]
    if isinstance(value, (date, datetime)):
        return value.isoformat()
    return value
