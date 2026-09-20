from __future__ import annotations

from dataclasses import asdict, dataclass, field
import hashlib
import json
from typing import Any, Iterable


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def stable_hash(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class SourceSpan:
    path: str
    start_byte: int
    end_byte: int
    start_row: int
    start_column: int
    end_row: int
    end_column: int


@dataclass(frozen=True)
class Symbol:
    symbol_id: str
    label: str
    kind: str
    module: str
    span: SourceSpan

    @classmethod
    def create(
        cls,
        *,
        label: str,
        kind: str,
        module: str,
        span: SourceSpan,
    ) -> "Symbol":
        symbol_id = stable_hash(
            {
                "module": module,
                "label": label,
                "kind": kind,
            }
        )
        return cls(symbol_id, label, kind, module, span)


@dataclass(frozen=True)
class Relation:
    source: str
    target: str
    kind: str
    evidence: SourceSpan | None = None

    @property
    def relation_id(self) -> str:
        return stable_hash(
            {
                "source": self.source,
                "target": self.target,
                "kind": self.kind,
            }
        )


@dataclass
class SemanticGraph:
    nodes: dict[str, Symbol] = field(default_factory=dict)
    edges: dict[str, Relation] = field(default_factory=dict)
    unresolved_references: list[dict[str, Any]] = field(default_factory=list)
    parse_error_files: list[str] = field(default_factory=list)

    @property
    def graph_id(self) -> str:
        return stable_hash(
            {
                "nodes": sorted(self.nodes),
                "edges": sorted(self.edges),
            }
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "graph_id": self.graph_id,
            "nodes": [asdict(v) for _, v in sorted(self.nodes.items())],
            "edges": [
                {
                    **asdict(v),
                    "relation_id": k,
                }
                for k, v in sorted(self.edges.items())
            ],
            "unresolved_references": self.unresolved_references,
            "parse_error_files": self.parse_error_files,
        }


@dataclass(frozen=True)
class GraphDelta:
    added_nodes: tuple[str, ...] = ()
    removed_nodes: tuple[str, ...] = ()
    added_edges: tuple[str, ...] = ()
    removed_edges: tuple[str, ...] = ()

    @classmethod
    def between(cls, before: SemanticGraph, after: SemanticGraph) -> "GraphDelta":
        before_nodes = set(before.nodes)
        after_nodes = set(after.nodes)
        before_edges = set(before.edges)
        after_edges = set(after.edges)
        return cls(
            added_nodes=tuple(sorted(after_nodes - before_nodes)),
            removed_nodes=tuple(sorted(before_nodes - after_nodes)),
            added_edges=tuple(sorted(after_edges - before_edges)),
            removed_edges=tuple(sorted(before_edges - after_edges)),
        )

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class CommitRecord:
    commit: str
    timestamp: int
    parents: tuple[str, ...]
    refs: tuple[str, ...] = ()

    @property
    def shape(self) -> str:
        if not self.parents:
            return "root"
        if len(self.parents) == 1:
            return "linear"
        return "merge"


@dataclass
class SemanticSnapshot:
    commit: str
    graph: SemanticGraph
    base_commit: str | None
    delta: GraphDelta | None

    def to_dict(self) -> dict[str, Any]:
        return {
            "commit": self.commit,
            "base_commit": self.base_commit,
            "graph": self.graph.to_dict(),
            "delta": None if self.delta is None else self.delta.to_dict(),
        }


@dataclass
class Timeline:
    commits: list[CommitRecord]
    snapshots: list[SemanticSnapshot]
    refs: dict[str, str]

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": "dashi.repo-history.v1",
            "commits": [asdict(c) | {"shape": c.shape} for c in self.commits],
            "refs": dict(sorted(self.refs.items())),
            "snapshots": [s.to_dict() for s in self.snapshots],
        }

    def write_json(self, path: str) -> None:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(self.to_dict(), f, indent=2, ensure_ascii=False)


def relations_by_target(relations: Iterable[Relation]) -> dict[str, list[Relation]]:
    out: dict[str, list[Relation]] = {}
    for relation in relations:
        out.setdefault(relation.target, []).append(relation)
    return out
