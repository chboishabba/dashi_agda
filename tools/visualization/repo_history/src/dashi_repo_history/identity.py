from __future__ import annotations

from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class IdentityMatch:
    old_id: str
    new_id: str
    evidence: str
    confidence: str


def match_node_identity(
    before_graph: dict[str, Any],
    after_graph: dict[str, Any],
) -> list[IdentityMatch]:
    before = {
        node["symbol_id"]: node
        for node in before_graph.get("nodes", [])
    }
    after = {
        node["symbol_id"]: node
        for node in after_graph.get("nodes", [])
    }

    matches: list[IdentityMatch] = [
        IdentityMatch(node_id, node_id, "exact-semantic-key", "exact")
        for node_id in sorted(set(before) & set(after))
    ]

    removed = {
        node_id: node
        for node_id, node in before.items()
        if node_id not in after
    }
    added = {
        node_id: node
        for node_id, node in after.items()
        if node_id not in before
    }

    old_by_fingerprint: dict[tuple[str, str], list[dict[str, Any]]] = {}
    new_by_fingerprint: dict[tuple[str, str], list[dict[str, Any]]] = {}

    for node in removed.values():
        fingerprint = node.get("fingerprint")
        if fingerprint:
            old_by_fingerprint.setdefault(
                (node["kind"], fingerprint),
                [],
            ).append(node)

    for node in added.values():
        fingerprint = node.get("fingerprint")
        if fingerprint:
            new_by_fingerprint.setdefault(
                (node["kind"], fingerprint),
                [],
            ).append(node)

    for key in sorted(set(old_by_fingerprint) & set(new_by_fingerprint)):
        olds = old_by_fingerprint[key]
        news = new_by_fingerprint[key]

        # Only unique evidence is admitted. Repeated boilerplate stays
        # unresolved rather than producing a speculative identity edge.
        if len(olds) != 1 or len(news) != 1:
            continue

        old = olds[0]
        new = news[0]
        evidence = (
            "source-move"
            if old["label"] == new["label"]
            else "unique-structural-fingerprint"
        )
        matches.append(
            IdentityMatch(
                old_id=old["symbol_id"],
                new_id=new["symbol_id"],
                evidence=evidence,
                confidence="supported",
            )
        )

    return matches


def supported_transfers(
    before_graph: dict[str, Any],
    after_graph: dict[str, Any],
) -> dict[str, str]:
    """Return old->new visual continuity for non-exact supported matches."""

    return {
        match.old_id: match.new_id
        for match in match_node_identity(before_graph, after_graph)
        if match.old_id != match.new_id and match.confidence == "supported"
    }
