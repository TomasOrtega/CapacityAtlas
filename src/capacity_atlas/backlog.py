# Copyright 2026 The Capacity Atlas Authors
# SPDX-License-Identifier: Apache-2.0
"""Validate proof-task selection without mistaking context for required targets."""

from typing import Any


def target_claims(entry: dict[str, Any], problem: dict[str, Any]) -> list[dict[str, Any]]:
    """Resolve only explicit campaign targets, rejecting open research by default."""
    if entry["problem"] != problem["id"]:
        raise ValueError("backlog problem identity mismatch")
    selected = entry.get("target_claims", [])
    context = entry.get("context_claims", [])
    if not selected or len(selected) != len(set(selected)):
        raise ValueError("targets must be nonempty and unique")
    if set(selected) & set(context):
        raise ValueError("a claim cannot be both a target and context")
    available = {claim["id"]: claim for claim in problem["formalization"]["claims"]}
    if (set(selected) | set(context)) - available.keys():
        raise ValueError("backlog selects an unknown claim")
    resolved = [available[ident] for ident in selected]
    if any(claim["category"] != "solved" for claim in resolved):
        raise ValueError("published-results targets must be solved literature claims")
    return resolved
