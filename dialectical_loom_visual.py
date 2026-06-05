#!/usr/bin/env python3
"""Build typed conversation-lattice artifacts from the local chat archive."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sqlite3
import subprocess
from collections import Counter, OrderedDict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, List, Sequence, Tuple

SCHEMA = "dashi.itir.dialectical_loom_graph.v0_2"
DEFAULT_DB = Path("~/chat_archive.sqlite").expanduser()
DEFAULT_THREAD_IDS = ["beb01b1e573989aaa177bac5c3d8d87c7427cc60"]
DEFAULT_TERM_SETS = OrderedDict(
    [
        ("sweetgrass", ["369", "sweetgrass", "three strand", "three-strand", "loom", "weave"]),
        ("dialectical", ["ternary", "dialectic", "stage", "resonance", "counter"]),
        ("braid", ["braid", "strand", "intertwine", "synthesis"]),
        ("nonary", ["nonary", "2x9", "nine", "grid"]),
        ("clifford", ["clifford", "bott", "m8", "m8(r)", "quadratic"]),
        ("ns_ym", ["ns", "yang-baxter", "yang baxter", "ym", "clay"]),
    ]
)
DEFAULT_DOC_PATHS = [
    Path("/home/c/Documents/20260604_070337_allm_20260604_070337.txt"),
]


@dataclass(frozen=True)
class ArtifactFile:
    name: str
    kind: str


@dataclass(frozen=True)
class EdgeFamily:
    name: str
    label: str
    color: str


FAMILIES = [
    EdgeFamily("turn_next", "turn next", "#6B7280"),
    EdgeFamily("dialectical_transition", "dialectical transition", "#0EA5E9"),
    EdgeFamily("weave_warp", "weave warp", "#0F766E"),
    EdgeFamily("weave_weft", "weave weft", "#A855F7"),
    EdgeFamily("braid_strand", "braid strand", "#10B981"),
    EdgeFamily("bt_edge", "BT edge", "#0D9488"),
    EdgeFamily("ultrametric_refinement", "ultrametric", "#EAB308"),
    EdgeFamily("proof_obligation", "proof obligation", "#EF4444"),
    EdgeFamily("promotion_boundary", "promotion boundary", "#DC2626"),
]


FAMILY_MAP = {family.name: family for family in FAMILIES}
FAMILY_NAMES = [f.name for f in FAMILIES]

RELATION_FORMALISM = {
    "schema": "dashi.itir.loom_relation_formalism.v0_1",
    "source_alignment": "SensibLaw affidavit relation classifier shape",
    "relation_types": [
        "exact_support",
        "equivalent_support",
        "explicit_dispute",
        "implicit_dispute",
        "partial_overlap",
        "adjacent_event",
        "substitution",
        "procedural_nonanswer",
        "unrelated",
    ],
    "relation_roots": ["supports", "invalidates", "non_resolving", "unanswered"],
    "evidence_statuses": ["open", "witnessed", "blocked", "boundary_only"],
    "promotion_states": [
        "not_promotion_candidate",
        "promotion_pending",
        "promotion_blocked",
        "promoted_by_separate_contract",
    ],
    "bucket_projection": {
        "exact_support": "supported",
        "equivalent_support": "supported",
        "explicit_dispute": "disputed",
        "implicit_dispute": "disputed",
        "partial_overlap": "partial_support",
        "adjacent_event": "adjacent_event",
        "substitution": "substitution",
        "procedural_nonanswer": "non_substantive_response",
        "unrelated": "missing",
    },
    "promotion_boundary": "relation classification is not theorem promotion",
}

def relation_metadata_for_family(family: str) -> Dict[str, Any]:
    relation_by_family = {
        "turn_next": ("adjacent_event", "witnessed", "sequence_reconciliation"),
        "dialectical_transition": ("partial_overlap", "witnessed", "dialectical_reconciliation"),
        "weave_warp": ("equivalent_support", "witnessed", "projection_reconciliation"),
        "weave_weft": ("equivalent_support", "witnessed", "projection_reconciliation"),
        "braid_strand": ("equivalent_support", "witnessed", "projection_reconciliation"),
        "bt_edge": ("partial_overlap", "witnessed", "bt_travel_reconciliation"),
        "ultrametric_refinement": ("partial_overlap", "witnessed", "refinement_reconciliation"),
        "proof_obligation": ("procedural_nonanswer", "open", "proof_obligation"),
        "promotion_boundary": ("unrelated", "boundary_only", "promotion_boundary"),
    }
    relation_root_by_type = {
        "exact_support": "supports",
        "equivalent_support": "supports",
        "explicit_dispute": "invalidates",
        "implicit_dispute": "invalidates",
        "partial_overlap": "supports",
        "adjacent_event": "non_resolving",
        "substitution": "non_resolving",
        "procedural_nonanswer": "non_resolving",
        "unrelated": "unanswered",
    }
    if family in relation_by_family:
        relation_type, evidence_status, formal_role = relation_by_family[family]
        return {
            "classification_scope": "affidavit_style_relation",
            "relation_type": relation_type,
            "relation_root": relation_root_by_type[relation_type],
            "bucket": RELATION_FORMALISM["bucket_projection"][relation_type],
            "evidence_status": evidence_status,
            "promotion_state": "promotion_false",
            "relation_basis": "loom_edge_family_mapping_v0_1",
            "formal_role": formal_role,
        }
    relation_type = "unrelated"
    return {
        "classification_scope": "affidavit_style_relation",
        "relation_type": relation_type,
        "relation_root": relation_root_by_type[relation_type],
        "bucket": RELATION_FORMALISM["bucket_projection"][relation_type],
        "evidence_status": "open",
        "promotion_state": "promotion_false",
        "relation_basis": "loom_edge_family_mapping_v0_1",
        "formal_role": family,
    }
def parse_term_set(raw: str) -> Tuple[str, List[str]]:
    if "=" not in raw:
        raise ValueError(f"term set expression must be NAME=term1,term2,... : {raw!r}")
    name, payload = raw.split("=", 1)
    terms = [term.strip().lower() for term in payload.split(",") if term.strip()]
    if not terms:
        raise ValueError(f"term set {raw!r} has no terms")
    return name.strip(), terms


def normalize_term_sets(explicit: Sequence[str] | None) -> "OrderedDict[str, list[str]]":
    if explicit:
        pairs = [parse_term_set(raw) for raw in explicit]
        return OrderedDict(pairs)
    return OrderedDict((name, list(terms)) for name, terms in DEFAULT_TERM_SETS.items())


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate deterministic dialectical loom artifacts from a local archive DB"
        )
    )
    parser.add_argument(
        "--db",
        type=Path,
        default=DEFAULT_DB,
        help=f"SQLite chat archive path, default {DEFAULT_DB}",
    )
    parser.add_argument(
        "--thread-id",
        action="append",
        default=[],
        help="Canonical thread ID; repeat for multiple threads",
    )
    parser.add_argument(
        "--term-set",
        action="append",
        default=[],
        help='term set spec as NAME=term1,term2...; defaults if omitted',
    )
    parser.add_argument(
        "--doc",
        action="append",
        default=[],
        help="Optional additional doc path for provenance metadata",
    )
    parser.add_argument(
        "--allm",
        type=Path,
        default=None,
        help="Optional ALLM file with additional attachment provenance",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("artifacts/dialectical_loom"),
        help="Output directory for JSON/DOT/PNG artifacts",
    )
    return parser.parse_args()


def safe_id(*parts: str) -> str:
    value = "::".join(parts)
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", value)


def stable_sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fp:
        for block in iter(lambda: fp.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def read_file_metadata(path: Path | None) -> Dict[str, Any] | None:
    if path is None:
        return None
    if not path.exists():
        return {"missing": True, "path": str(path)}
    text = path.read_text(encoding="utf-8", errors="replace")
    title_line = text.splitlines()[:1]
    first_line = title_line[0].strip() if title_line else ""
    return {
        "missing": False,
        "path": str(path),
        "size": len(text),
        "sha256": stable_sha256(path),
        "first_line": first_line,
    }


def detect_terms(text: str | None, term_sets: "OrderedDict[str, List[str]]") -> List[str]:
    if not text:
        return []
    lowered = text.lower()
    matches: List[str] = []
    for name, terms in term_sets.items():
        for term in terms:
            if term and term in lowered:
                matches.append(name)
                break
    return matches


def stage_from_index(index: int) -> str:
    rem = index % 4
    if rem == 0:
        return "seed"
    if rem == 1:
        return "counter"
    if rem == 2:
        return "resonance"
    return "overflow"


def travel_from_index(index: int) -> str:
    rem = index % 3
    if rem == 0:
        return "reverse"
    if rem == 1:
        return "stasis"
    return "forward"


def ternary_from_index(index: int) -> str:
    rem = index % 3
    if rem == 0:
        return "negative"
    if rem == 1:
        return "neutral"
    return "positive"


def grid_cell_from_index(index: int) -> str:
    a = index % 3
    b = (index * 2) % 3
    return f"a{a}_b{b}"


def ultrametric_depth_from_index(index: int) -> int:
    return index % 4


def load_messages(conn: sqlite3.Connection, thread_id: str) -> List[sqlite3.Row]:
    cur = conn.cursor()
    rows = cur.execute(
        """
        SELECT
          message_id,
          ts,
          role,
          text,
          title,
          source_id,
          source_thread_id,
          source_message_id,
          source_path,
          source_bucket
        FROM messages
        WHERE canonical_thread_id = ?
        ORDER BY ts ASC, message_id ASC
        """,
        (thread_id,),
    ).fetchall()
    return list(rows)


def load_artifacts(conn: sqlite3.Connection, thread_id: str) -> List[sqlite3.Row]:
    cur = conn.cursor()
    rows = cur.execute(
        """
        SELECT artifact_id, kind, local_path, source_url, size_bytes, sha256
        FROM thread_artifacts
        WHERE canonical_thread_id = ?
        ORDER BY artifact_id
        """,
        (thread_id,),
    ).fetchall()
    return list(rows)


def make_node(message_id: str, payload: Dict[str, Any]) -> Dict[str, Any]:
    return {
        "id": safe_id("msg", message_id),
        "kind": "message",
        "payload": payload,
    }


def make_static_node(node_type: str, node_id: str, label: str, attrs: Dict[str, Any] | None = None) -> Dict[str, Any]:
    node = {"id": safe_id(node_type, node_id), "kind": node_type, "label": label}
    if attrs:
        node["attrs"] = attrs
    return node


def add_edge(edges: List[Dict[str, Any]], source: str, target: str, family: str, attrs: Dict[str, Any] | None = None) -> None:
    formal_relation = relation_metadata_for_family(family)
    edge = {
        "source": source,
        "target": target,
        "family": family,
        "formal_relation": formal_relation,
        "relation_type": formal_relation["relation_type"],
        "relation_root": formal_relation["relation_root"],
        "evidence_status": formal_relation["evidence_status"],
        "promotion_state": formal_relation["promotion_state"],
        "relation_basis": formal_relation["relation_basis"],
        "bucket": formal_relation["bucket"],
    }
    if attrs:
        edge["attrs"] = attrs
    if family in FAMILY_MAP:
        edge["family_label"] = FAMILY_MAP[family].label
    edges.append(edge)


def escape_dot_label(text: str) -> str:
    return text.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")


def build_thread_payload(
    thread_id: str,
    messages: Sequence[sqlite3.Row],
    artifacts: Sequence[sqlite3.Row],
    term_sets: "OrderedDict[str, List[str]]",
    docs: Sequence[Dict[str, Any]],
    allm: Dict[str, Any] | None,
    source_db: Path,
) -> Dict[str, Any]:
    thread_title = messages[0]["title"] if messages else ""
    message_nodes: List[Dict[str, Any]] = []
    node_by_index = {}
    for index, row in enumerate(messages):
        terms = detect_terms(row["text"], term_sets)
        node_payload = {
            "thread_id": thread_id,
            "message_id": row["message_id"],
            "index": index,
            "role": row["role"],
            "ts": row["ts"],
            "title": row["title"],
            "dialectical_stage": stage_from_index(index),
            "ternary_position": ternary_from_index(index),
            "nonary_cell": grid_cell_from_index(index),
            "bt_travel_sign": travel_from_index(index),
            "ultrametric_refinement_depth": ultrametric_depth_from_index(index),
            "terms": terms,
            "title_term_sets": [t for t in terms],
            "source_id": row["source_id"],
            "source_thread_id": row["source_thread_id"],
            "source_message_id": row["source_message_id"],
            "source_path": row["source_path"],
            "source_bucket": row["source_bucket"],
        }
        node = make_node(row["message_id"], node_payload)
        node["label"] = f"{index}:{row['role']}"
        message_nodes.append(node)
        node_by_index[index] = node["id"]

    thread_node_id = safe_id("thread", thread_id)
    thread_node = {
        "id": thread_node_id,
        "kind": "thread",
        "label": thread_title or "sweetgrass",
        "payload": {
            "canonical_thread_id": thread_id,
            "thread_title": thread_title,
            "message_count": len(messages),
            "docs": docs,
            "allm": allm,
        },
    }

    static_nodes = []
    strand_nodes = [
        make_static_node("braid_strand", "A", "strandA", {"index": 0}),
        make_static_node("braid_strand", "B", "strandB", {"index": 1}),
        make_static_node("braid_strand", "C", "strandC", {"index": 2}),
    ]
    obligation_nodes = [
        make_static_node(
            "proof_obligation",
            "yang_baxter",
            "yang_baxter_block",
            {"required": "target not promoted"},
        ),
        make_static_node(
            "proof_obligation",
            "physics",
            "physics_block",
            {"required": "not promoted"},
        ),
        make_static_node(
            "proof_obligation",
            "clifford",
            "clifford_m0_6_block",
            {"required": "receipts not complete"},
        ),
    ]
    boundary_nodes = [
        make_static_node(
            "promotion_boundary",
            "nsym",
            "NS/YM_fail_closed",
            {"status": "no_claim"},
        ),
        make_static_node(
            "promotion_boundary",
            "clifford",
            "Clifford/Bott_fail_closed",
            {"status": "receipt_obligation"},
        ),
    ]
    static_nodes.extend(strand_nodes)
    static_nodes.extend(obligation_nodes)
    static_nodes.extend(boundary_nodes)

    edges: List[Dict[str, Any]] = []
    if message_nodes:
        for idx, current_node in enumerate(message_nodes[:-1]):
            next_node = message_nodes[idx + 1]
            add_edge(
                edges,
                current_node["id"],
                next_node["id"],
                "turn_next",
                {"index": idx},
            )
            add_edge(
                edges,
                current_node["id"],
                next_node["id"],
                "dialectical_transition",
                {"from": stage_from_index(idx), "to": stage_from_index(idx + 1)},
            )
            if idx % 2 == 0:
                add_edge(
                    edges,
                    current_node["id"],
                    static_nodes[idx % 3]["id"],  # 0/1/2 for strand nodes
                    "weave_warp",
                    {"strand": "A"},
                )
                add_edge(
                    edges,
                    current_node["id"],
                    static_nodes[idx % 3]["id"],
                    "braid_strand",
                    {"strand": "A"},
                )
            else:
                add_edge(
                    edges,
                    current_node["id"],
                    static_nodes[idx % 3]["id"],
                    "weave_weft",
                    {"strand": "B"},
                )
                add_edge(
                    edges,
                    current_node["id"],
                    static_nodes[idx % 3]["id"],
                    "braid_strand",
                    {"strand": "B"},
                )
            add_edge(
                edges,
                current_node["id"],
                next_node["id"],
                "bt_edge",
                {"sign": travel_from_index(idx)},
            )
            add_edge(
                edges,
                current_node["id"],
                next_node["id"],
                "ultrametric_refinement",
                {"depth": ultrametric_depth_from_index(idx + 1)},
            )

        last_node = message_nodes[-1]["id"]
        first_node = message_nodes[0]["id"]
        for obligation in obligation_nodes:
            add_edge(
                edges,
                first_node,
                obligation["id"],
                "proof_obligation",
                {"obligation": obligation["label"]},
            )
        for boundary in boundary_nodes:
            add_edge(
                edges,
                thread_node_id,
                boundary["id"],
                "promotion_boundary",
                {"status": "fail-closed"},
            )

    # guarantee proof-obligation and boundary families are non-empty for tiny threads
    if not edges:
        if thread_node_id:
            add_edge(edges, thread_node_id, thread_node_id, "proof_obligation", {"note": "empty-thread-obligation-marker"})
            add_edge(
                edges,
                thread_node_id,
                thread_node_id,
                "promotion_boundary",
                {"note": "empty-thread-boundary-marker"},
            )

    artifacts_payload = [
        {
            "artifact_id": row["artifact_id"],
            "kind": row["kind"],
            "local_path": row["local_path"],
            "source_url": row["source_url"],
            "size_bytes": row["size_bytes"],
            "sha256": row["sha256"],
        }
        for row in artifacts
    ]

    nodes = [thread_node] + static_nodes + message_nodes
    node_lookup = {node["id"]: node for node in nodes}
    counts = Counter(edge["family"] for edge in edges)
    relation_counts = Counter(
        edge["relation_type"]
        for edge in edges
        if edge.get("relation_type")
    )
    relation_root_counts = Counter(
        edge["relation_root"]
        for edge in edges
        if edge.get("relation_root")
    )
    evidence_status_counts = Counter(
        edge["evidence_status"]
        for edge in edges
        if edge.get("evidence_status")
    )
    relation_scope_counts = Counter(
        edge["formal_relation"]["classification_scope"]
        for edge in edges
        if edge.get("formal_relation", {}).get("classification_scope")
    )
    used_threads = {
        "thread_id": thread_id,
        "message_ids": [row["message_id"] for row in messages],
        "edge_count": len(edges),
    }

    return {
        "schema": SCHEMA,
        "canonical_thread_id": thread_id,
        "title": thread_title,
        "source_db": str(source_db),
        "live_web_dependency": False,
        "nodes": nodes,
        "node_count": len(nodes),
        "nodes_by_kind": {
            kind: len([n for n in nodes if n["kind"] == kind])
            for kind in sorted({node["kind"] for node in nodes})
        },
        "edges": edges,
        "edge_count": len(edges),
        "edge_counts": {name: counts.get(name, 0) for name in FAMILY_NAMES},
        "relation_formalism": RELATION_FORMALISM,
        "relation_counts": dict(sorted(relation_counts.items())),
        "relation_root_counts": dict(sorted(relation_root_counts.items())),
        "evidence_status_counts": dict(sorted(evidence_status_counts.items())),
        "relation_scope_counts": dict(sorted(relation_scope_counts.items())),
        "term_sets": {name: terms for name, terms in term_sets.items()},
        "artifact_rows": artifacts_payload,
        "thread_meta": used_threads,
        "provenance": {
            "docs": docs,
            "allm": allm,
            "first_messages": [
                {"index": idx, "message_id": row["message_id"], "node_id": node["id"]}
                for idx, (row, node) in enumerate(zip(messages[:5], message_nodes[:5]))
            ],
            "last_messages": [
                {"index": len(messages) - len(message_nodes[:5]) + idx, "message_id": row["message_id"], "node_id": node["id"]}
                for idx, (row, node) in enumerate(zip(messages[-5:], message_nodes[-5:]))
            ],
        },
    }


def dot_for_payload(payload: Dict[str, Any], families: Sequence[str], graph_label: str) -> str:
    include = set(families)
    edges = [edge for edge in payload["edges"] if edge["family"] in include]
    node_ids = set()
    for edge in edges:
        node_ids.add(edge["source"])
        node_ids.add(edge["target"])
    selected_nodes = [node for node in payload["nodes"] if node["id"] in node_ids]
    selected_ids = {node["id"] for node in selected_nodes}
    for node in payload["nodes"]:
        if node["kind"] in {"thread", "proof_obligation", "promotion_boundary", "braid_strand"}:
            if node["id"] not in selected_ids:
                selected_nodes.append(node)
                selected_ids.add(node["id"])

    by_id = {node["id"]: node for node in selected_nodes}
    lines = [
        "digraph dialectical_loom {",
        '  rankdir=LR;',
        '  node [shape=ellipse fontname="Helvetica" fontsize=11];',
        '  edge [fontname="Helvetica" fontsize=9];',
    ]
    for node in selected_nodes:
        kind = node["kind"]
        shape = "ellipse"
        color = "#0F172A"
        fill = "white"
        if kind == "message":
            shape = "box"
            color = "#0F766E"
        elif kind == "thread":
            shape = "oval"
            color = "#2563EB"
            fill = "#DBEAFE"
        elif kind == "braid_strand":
            shape = "diamond"
            color = "#16A34A"
            fill = "#DCFCE7"
        elif kind == "proof_obligation":
            shape = "octagon"
            color = "#BE123C"
            fill = "#FEE2E2"
        elif kind == "promotion_boundary":
            shape = "parallelogram"
            color = "#DC2626"
            fill = "#FFE4E6"
        label = escape_dot_label(node.get("label", node["id"]))
        lines.append(
            f'  "{node["id"]}" [label="{label}",shape={shape},color="{color}",style="filled",fillcolor="{fill}"];'
        )
    for edge in edges:
        family = edge["family"]
        color = FAMILY_MAP[family].color
        family_label = edge.get("family_label", family)
        attrs = edge.get("attrs", {})
        label = family_label
        relation_type = edge.get("relation_type")
        relation_root = edge.get("relation_root")
        evidence_status = edge.get("evidence_status")
        if relation_type and relation_root and evidence_status:
            label = f"{family_label}\\n{relation_type}/{relation_root}/{evidence_status}"
        if attrs:
            details = ",".join(f"{k}={v}" for k, v in sorted(attrs.items()))
            if details:
                label = f"{label}: {details}"
        lines.append(
            f'  "{edge["source"]}" -> "{edge["target"]}" [color="{color}",label="{escape_dot_label(label)}",fontsize=8];'
        )
    lines.append("}")
    return "\n".join(lines)


def write_json(path: Path, payload: Dict[str, Any], pretty: bool) -> None:
    text = json.dumps(payload, indent=2 if pretty else None, sort_keys=True) + "\n"
    path.write_text(text, encoding="utf-8")


def write_dot(path: Path, source: str) -> None:
    path.write_text(source + "\n", encoding="utf-8")


def write_png(dot_path: Path, png_path: Path) -> None:
    try:
        subprocess.run(
            ["dot", "-Tpng", str(dot_path), "-o", str(png_path)],
            check=True,
            timeout=25,
        )
        return
    except Exception as exc:
        print(f"warning: graphviz render failed for {dot_path.name}: {exc}")

    # Fallback renderer: deterministic tiny visual summary for non-zero-sized graphs.
    lines = dot_path.read_text(encoding="utf-8").splitlines()
    family_counts: Counter[str] = Counter()
    edge_count = 0
    for line in lines:
        m = re.search(r'label="([^"]+)"', line)
        if "->" in line and m:
            raw = m.group(1)
            family = raw.split(":", 1)[0]
            family_counts[family.strip()] += 1
            edge_count += 1

    width = 1500
    height = 900
    try:
        from PIL import Image, ImageDraw
    except Exception:
        raise RuntimeError(f"PIL unavailable and graphviz failed for {dot_path}") from exc

    img = Image.new("RGB", (width, height), "white")
    draw = ImageDraw.Draw(img)
    title = f"{dot_path.stem}.png (fallback render)"
    draw.text((20, 10), title, fill="black")
    draw.text((20, 35), f"dot file: {dot_path}", fill="black")
    draw.text((20, 60), f"edge_count: {edge_count}", fill="black")
    legend_top = 95
    y = legend_top
    for family, count in sorted(family_counts.items()):
        color = FAMILY_MAP.get(family, EdgeFamily(family, family, "#4B5563")).color
        rgb = tuple(int(color[i : i + 2], 16) for i in (1, 3, 5))
        x0, y0, x1, y1 = 40, y, 80, y + 14
        draw.rectangle((x0, y0, x1, y1), fill=rgb, outline=rgb)
        draw.text((95, y), f"{family}: {count}", fill="black")
        y += 22

    label = "fallback includes proof-obligation / boundary / weave / braid layers where present"
    draw.text((20, 860), label, fill="black")
    img.save(png_path)


def build_projection(
    payload: Dict[str, Any],
    families: Sequence[str],
    label: str,
) -> Dict[str, Any]:
    filtered_edges = [edge for edge in payload["edges"] if edge["family"] in families]
    connected_nodes = set()
    for edge in filtered_edges:
        connected_nodes.add(edge["source"])
        connected_nodes.add(edge["target"])
    filtered_nodes = [node for node in payload["nodes"] if node["id"] in connected_nodes]
    counts = Counter(edge["family"] for edge in filtered_edges)
    relation_counts = Counter(
        edge["relation_type"]
        for edge in filtered_edges
        if edge.get("relation_type")
    )
    relation_root_counts = Counter(
        edge["relation_root"]
        for edge in filtered_edges
        if edge.get("relation_root")
    )
    evidence_status_counts = Counter(
        edge["evidence_status"]
        for edge in filtered_edges
        if edge.get("evidence_status")
    )
    relation_scope_counts = Counter(
        edge["formal_relation"]["classification_scope"]
        for edge in filtered_edges
        if edge.get("formal_relation", {}).get("classification_scope")
    )
    if not filtered_nodes:
        # preserve thread context even if a family is absent by reference
        filtered_nodes = [node for node in payload["nodes"] if node["kind"] == "thread"]
    return {
        "schema": SCHEMA,
        "canonical_thread_id": payload["canonical_thread_id"],
        "title": payload["title"],
        "families": list(families),
        "source_db": payload["source_db"],
        "live_web_dependency": payload["live_web_dependency"],
        "nodes": filtered_nodes,
        "node_count": len(filtered_nodes),
        "edges": filtered_edges,
        "edge_count": len(filtered_edges),
        "edge_counts": {name: counts.get(name, 0) for name in families},
        "relation_formalism": payload["relation_formalism"],
        "relation_counts": dict(sorted(relation_counts.items())),
        "relation_root_counts": dict(sorted(relation_root_counts.items())),
        "evidence_status_counts": dict(sorted(evidence_status_counts.items())),
        "relation_scope_counts": dict(sorted(relation_scope_counts.items())),
        "term_sets": payload["term_sets"],
        "artifact_rows": payload["artifact_rows"],
        "provenance": payload["provenance"],
    }


def main() -> int:
    args = parse_args()
    thread_ids = args.thread_id or DEFAULT_THREAD_IDS
    term_sets = normalize_term_sets(args.term_set)
    output_dir = args.output_dir.expanduser()
    output_dir.mkdir(parents=True, exist_ok=True)

    docs = args.doc or []
    allm_path = args.allm
    if allm_path:
        allm_payload = read_file_metadata(allm_path.expanduser())
    else:
        allm_payload = None

    resolved_docs: List[Dict[str, Any]] = []
    for doc in [*docs, *DEFAULT_DOC_PATHS]:
        path = Path(doc).expanduser()
        resolved_docs.append(
            {
                "path": str(path),
                "exists": path.exists(),
                "size": path.stat().st_size if path.exists() else None,
                "sha256": stable_sha256(path) if path.exists() else None,
            }
        )

    db_path = args.db.expanduser()
    conn = sqlite3.connect(str(db_path))
    conn.row_factory = sqlite3.Row
    all_thread_payloads = []
    for thread_id in thread_ids:
        messages = load_messages(conn, thread_id)
        if not messages:
            print(f"warning: no messages for thread {thread_id}")
            continue
        artifacts = load_artifacts(conn, thread_id)
        thread_payload = build_thread_payload(
            thread_id=thread_id,
            messages=messages,
            artifacts=artifacts,
            term_sets=term_sets,
            docs=resolved_docs,
            allm=allm_payload,
            source_db=db_path,
        )
        all_thread_payloads.append(thread_payload)

        weave_payload = build_projection(
            thread_payload,
            [
                "turn_next",
                "dialectical_transition",
                "weave_warp",
                "weave_weft",
                "ultrametric_refinement",
                "proof_obligation",
                "promotion_boundary",
            ],
            "sweetgrass_dialectical_weave",
        )
        braid_payload = build_projection(
            thread_payload,
            [
                "turn_next",
                "dialectical_transition",
                "braid_strand",
                "bt_edge",
                "proof_obligation",
                "promotion_boundary",
            ],
            "sweetgrass_three_strand_braid",
        )

        weave_json = output_dir / "sweetgrass_dialectical_weave.json"
        weave_dot_path = output_dir / "sweetgrass_dialectical_weave.dot"
        weave_png_path = output_dir / "sweetgrass_dialectical_weave.png"
        braid_json = output_dir / "sweetgrass_three_strand_braid.json"
        braid_dot_path = output_dir / "sweetgrass_three_strand_braid.dot"
        braid_png_path = output_dir / "sweetgrass_three_strand_braid.png"

        write_json(weave_json, weave_payload, pretty=True)
        write_json(braid_json, braid_payload, pretty=True)
        write_dot(weave_dot_path, dot_for_payload(thread_payload, weave_payload["families"], "sweetgrass_dialectical_weave"))
        write_dot(braid_dot_path, dot_for_payload(thread_payload, braid_payload["families"], "sweetgrass_three_strand_braid"))
        try:
            write_png(weave_dot_path, weave_png_path)
        except Exception as exc:
            print(f"warning: weave png render failed for {thread_id}: {exc}")
        try:
            write_png(braid_dot_path, braid_png_path)
        except Exception as exc:
            print(f"warning: braid png render failed for {thread_id}: {exc}")

    conn.close()

    summary = {
        "schema": SCHEMA,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_db": str(db_path),
        "source_db_exists": db_path.exists(),
        "live_web_dependency": False,
        "canonical_threads": thread_ids,
        "threads": all_thread_payloads,
        "relation_formalism": RELATION_FORMALISM,
        "artifacts": [
            {
                "name": "sweetgrass_dialectical_weave",
                "json": str((output_dir / "sweetgrass_dialectical_weave.json")),
                "dot": str((output_dir / "sweetgrass_dialectical_weave.dot")),
                "png": str((output_dir / "sweetgrass_dialectical_weave.png")),
            },
            {
                "name": "sweetgrass_three_strand_braid",
                "json": str((output_dir / "sweetgrass_three_strand_braid.json")),
                "dot": str((output_dir / "sweetgrass_three_strand_braid.dot")),
                "png": str((output_dir / "sweetgrass_three_strand_braid.png")),
            },
            {
                "name": "sweetgrass_loom_receipt_summary",
                "json": str((output_dir / "sweetgrass_loom_receipt_summary.json")),
            },
        ],
        "term_sets": {name: terms for name, terms in term_sets.items()},
        "docs": resolved_docs,
        "allm": allm_payload,
    }
    write_json(output_dir / "sweetgrass_loom_receipt_summary.json", summary, pretty=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
