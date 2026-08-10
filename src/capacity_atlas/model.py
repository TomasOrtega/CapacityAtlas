from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Atlas:
    root: Path
    site: dict[str, Any]
    categories: list[dict[str, Any]]
    references: dict[str, dict[str, Any]]
    problems: list[dict[str, Any]]
    problem_files: dict[str, Path]

    @property
    def problems_by_id(self) -> dict[str, dict[str, Any]]:
        return {problem["id"]: problem for problem in self.problems}

    @property
    def categories_by_id(self) -> dict[str, dict[str, Any]]:
        return {category["id"]: category for category in self.categories}
