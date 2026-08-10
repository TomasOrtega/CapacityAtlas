# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Atlas:
    root: Path
    site: dict[str, Any]
    tag_axes: dict[str, dict[str, Any]]
    references: dict[str, dict[str, Any]]
    problems: list[dict[str, Any]]
    problem_files: dict[str, Path]

    @property
    def problems_by_id(self) -> dict[str, dict[str, Any]]:
        return {problem["id"]: problem for problem in self.problems}

    @property
    def tag_values(self) -> dict[str, dict[str, dict[str, Any]]]:
        return {
            axis_id: {value["id"]: value for value in axis["values"]}
            for axis_id, axis in self.tag_axes.items()
        }
