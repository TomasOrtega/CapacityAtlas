# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

import json
from dataclasses import asdict, is_dataclass
from datetime import date, datetime
from pathlib import Path
from typing import Any

import yaml

from .model import Atlas


def find_root(start: Path | None = None) -> Path:
    current = (start or Path.cwd()).resolve()
    for candidate in (current, *current.parents):
        if (candidate / "data" / "site.yaml").is_file() and (
            candidate / "schema" / "problem.schema.json"
        ).is_file():
            return candidate
    raise FileNotFoundError("could not locate Capacity Atlas repository root")


def load_yaml(path: Path) -> Any:
    with path.open(encoding="utf-8") as handle:
        return yaml.safe_load(handle)


def load_atlas(root: Path | None = None) -> Atlas:
    root = (root or find_root()).resolve()
    site = load_yaml(root / "data" / "site.yaml")
    tags = load_yaml(root / "data" / "tags.yaml")
    references = load_yaml(root / "data" / "references.yaml")

    axes = {axis["id"]: axis for axis in tags["axes"]}
    problems: list[dict[str, Any]] = []
    problem_files: dict[str, Path] = {}
    for path in sorted((root / "data" / "problems").glob("*.yaml")):
        problem = load_yaml(path)
        problems.append(problem)
        problem_files[str(problem.get("id", path.stem))] = path

    return Atlas(
        root=root,
        site=site,
        tag_axes=axes,
        references=references,
        problems=problems,
        problem_files=problem_files,
    )


def json_ready(value: Any) -> Any:
    if is_dataclass(value):
        return json_ready(asdict(value))
    if isinstance(value, dict):
        return {str(key): json_ready(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_ready(item) for item in value]
    if isinstance(value, (date, datetime)):
        return value.isoformat()
    return value
