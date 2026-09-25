#!/usr/bin/env python3
"""Zero-config Digital-ESD corpus -> candidate world builder.

Normal agent entry point:

    python3 interop_scripts/digital_esd/run_world.py

The runner composes the existing fail-closed Digital-ESD runtimes.  It does not
invent a second screening/parser/evidence ontology.

Observed authority gates remain explicit:
- candidate screening != reviewed screening decision;
- parsed PNF/facets != reviewed canonical evidence;
- reviewed evidence != SourceAuditAdmission.

Everything else is pre-populated into a graph/inspection bundle so an agent can
inspect one artifact rather than manually traversing runtime directories.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


HERE = Path(__file__).resolve().parent
DASHI_ROOT = HERE.parents[1]
DEFAULT_ARTIFACT_ROOT = Path("artifacts/digital-esd/real-eric")


def canonical_digest(value: Any) -> str:
    payload = (json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n").encode()
    return hashlib.sha256(payload).hexdigest()


def read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    value = json.loads(path.read_text(encoding="utf-8"))
    return value if isinstance(value, dict) else {}


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as fh:
        for n, line in enumerate(fh, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{n}: expected object")
            rows.append(row)
    return rows


def read_tsv(path: Path) -> list[dict[str, str]]:
    if not path.exists():
        return []
    with path.open(newline="", encoding="utf-8") as fh:
        return [dict(row) for row in csv.DictReader(fh, delimiter="\t")]


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as fh:
        for row in rows:
            fh.write(json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n")


def resolve_slr_root() -> Path:
    if os.environ.get("SLR_REPO_ROOT"):
        root = Path(os.environ["SLR_REPO_ROOT"]).resolve()
    else:
        root = (DASHI_ROOT.parent / "slr").resolve()
    if not root.exists():
        raise FileNotFoundError(
            f"SLR checkout not found at {root}; set SLR_REPO_ROOT once if it lives elsewhere"
        )
    return root


def resolve_artifact_root(slr_root: Path) -> Path:
    env = os.environ.get("DIGITAL_ESD_ARTIFACT_ROOT")
    if env:
        return Path(env).resolve()
    # The existing dashi wrappers interpret the standard relative path against SLR.
    return (slr_root / DEFAULT_ARTIFACT_ROOT).resolve()


def run(cmd: list[str], *, cwd: Path) -> None:
    print("+", " ".join(cmd), file=sys.stderr)
    subprocess.run(cmd, cwd=cwd, check=True)


def stable_ref(row: dict[str, Any]) -> str:
    for key in (
        "source_identity_reference",
        "sourceIdentityReference",
        "source_ref",
        "source_reference",
    ):
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def add_node(
    nodes: dict[str, dict[str, Any]],
    kind: str,
    key: str,
    *,
    authority: str,
    data: dict[str, Any],
) -> str:
    node_id = f"{kind}:{key}"
    previous = nodes.get(node_id)
    candidate = {
        "id": node_id,
        "kind": kind,
        "authority": authority,
        "data": data,
    }
    if previous is None:
        nodes[node_id] = candidate
    elif previous != candidate:
        # Multiple observations of the same stable node become an explicit bundle.
        merged = dict(previous)
        observations = list(merged.get("observations") or [previous.get("data", {})])
        if data not in observations:
            observations.append(data)
        merged["observations"] = observations
        nodes[node_id] = merged
    return node_id


def add_edge(
    edges: dict[str, dict[str, Any]],
    source: str,
    relation: str,
    target: str,
    *,
    authority: str,
    receipt: str,
) -> None:
    basis = {
        "source": source,
        "relation": relation,
        "target": target,
        "authority": authority,
        "receipt": receipt,
    }
    edge_id = "edge:" + canonical_digest(basis)
    edges[edge_id] = {"id": edge_id, **basis}


def stage_node(nodes: dict[str, dict[str, Any]], ref: str, stage: str, observed: bool) -> str:
    return add_node(
        nodes,
        "stage",
        f"{ref}:{stage}",
        authority="observed-runtime" if observed else "unpaid",
        data={"source_identity_reference": ref, "stage": stage, "observed": observed},
    )


def collect_parser_candidates(parser_rows: list[dict[str, Any]]) -> list[tuple[str, dict[str, Any]]]:
    """Find EvidenceObservation/PNF/facet-like candidate dicts without assuming one parser schema."""
    out: list[tuple[str, dict[str, Any]]] = []
    interesting = {
        "evidence_observations",
        "evidenceObservationCandidates",
        "study_facets",
        "studyFacetCandidates",
        "candidate_facets",
        "pnf",
        "pnf_candidates",
        "document_nodes",
        "nodes",
    }

    def walk(ref: str, value: Any, path: tuple[str, ...]) -> None:
        if isinstance(value, dict):
            for k, v in value.items():
                next_path = path + (str(k),)
                if k in interesting:
                    if isinstance(v, list):
                        for item in v:
                            if isinstance(item, dict):
                                out.append((ref, {"candidate_kind": k, "candidate_path": list(next_path), **item}))
                    elif isinstance(v, dict):
                        out.append((ref, {"candidate_kind": k, "candidate_path": list(next_path), **v}))
                walk(ref, v, next_path)
        elif isinstance(value, list):
            for item in value:
                walk(ref, item, path)

    for row in parser_rows:
        ref = stable_ref(row)
        if ref:
            walk(ref, row, ())
    # De-duplicate exact candidate objects.
    unique: dict[str, tuple[str, dict[str, Any]]] = {}
    for ref, row in out:
        unique[canonical_digest({"ref": ref, "row": row})] = (ref, row)
    return list(unique.values())


def build_world(artifact_root: Path) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]], dict[str, Any]]:
    parse_root = artifact_root / "slr-parse"
    world_root = artifact_root / "world"

    processing = read_jsonl(parse_root / "study-processing-ledger.jsonl")
    assessments = read_jsonl(artifact_root / "candidate_assessments.jsonl")
    hypotheses = read_jsonl(artifact_root / "study_family_hypotheses.jsonl")
    review_packets = read_jsonl(artifact_root / "review" / "review_packets.jsonl")
    retrieval_residual = read_jsonl(parse_root / "fulltext-retrieval-residual.jsonl")
    materialisation = read_jsonl(parse_root / "materialization-receipts.jsonl")
    handoff = read_jsonl(parse_root / "slr-handoff-receipts.jsonl")
    parse_receipts = read_jsonl(parse_root / "slr-parse-receipts.jsonl")
    review_receipts = read_jsonl(parse_root / "slr-review-receipts.jsonl")
    audit_receipts = read_jsonl(parse_root / "source-audit-receipts.jsonl")

    parser_rows: list[dict[str, Any]] = []
    for candidate in (
        parse_root / "parser" / "verified.jsonl",
        parse_root / "parser" / "parser-output.jsonl",
    ):
        parser_rows.extend(read_jsonl(candidate))

    nodes: dict[str, dict[str, Any]] = {}
    edges: dict[str, dict[str, Any]] = {}

    processing_by_ref = {stable_ref(row): row for row in processing if stable_ref(row)}

    for ref, row in processing_by_ref.items():
        source_node = add_node(
            nodes,
            "source",
            ref,
            authority="denominator",
            data={
                "source_identity_reference": ref,
                "metadata_revision_reference": row.get("metadata_revision_reference"),
                "screening_decision": row.get("screening_decision"),
            },
        )
        stages = [
            ("screened", bool(row.get("screened"))),
            ("retained", bool(row.get("retained"))),
            ("verified-fulltext", bool(row.get("verified"))),
            ("materialised", bool(row.get("materialised"))),
            ("slr-handoff", bool(row.get("handoff"))),
            ("parsed", bool(row.get("parsed"))),
            ("reviewed-evidence", bool(row.get("reviewed"))),
            ("source-audit-admission", bool(row.get("admitted"))),
        ]
        last = source_node
        for stage, observed in stages:
            node = stage_node(nodes, ref, stage, observed)
            add_edge(edges, last, "processing-stage", node, authority="observed-runtime", receipt=str(row.get("row_receipt_reference") or ""))
            last = node

    for row in assessments:
        ref = stable_ref(row)
        if not ref:
            continue
        nid = add_node(nodes, "screening-candidate", canonical_digest(row), authority="candidate", data=row)
        add_edge(edges, f"source:{ref}", "has-screening-candidate", nid, authority="candidate", receipt=str(row.get("assessment_reference") or ""))

    for row in hypotheses:
        ref = stable_ref(row)
        if not ref:
            continue
        nid = add_node(nodes, "study-family-hypothesis", canonical_digest(row), authority="candidate", data=row)
        add_edge(edges, f"source:{ref}", "has-study-family-hypothesis", nid, authority="candidate", receipt=str(row.get("hypothesis_reference") or ""))

    for ref, candidate in collect_parser_candidates(parser_rows):
        cid = canonical_digest({"source": ref, "candidate": candidate})
        nid = add_node(nodes, "semantic-candidate", cid, authority="candidate", data={
            "source_identity_reference": ref,
            "candidate_only": True,
            "creates_semantic_authority": False,
            **candidate,
        })
        add_edge(edges, f"source:{ref}", "has-semantic-candidate", nid, authority="candidate", receipt=cid)

    for rows, kind, relation, authority in (
        (materialisation, "materialisation-receipt", "materialised-as", "observed-runtime"),
        (handoff, "slr-handoff-receipt", "handed-to-slr-by", "observed-runtime"),
        (parse_receipts, "parse-receipt", "parsed-by", "observed-runtime"),
        (review_receipts, "reviewed-evidence-receipt", "reviewed-by", "reviewed"),
        (audit_receipts, "source-audit-receipt", "admitted-by", "admitted"),
    ):
        for row in rows:
            ref = stable_ref(row)
            if not ref:
                continue
            rid = canonical_digest(row)
            nid = add_node(nodes, kind, rid, authority=authority, data=row)
            add_edge(edges, f"source:{ref}", relation, nid, authority=authority, receipt=rid)

    unresolved_review = [row for row in review_packets if str(row.get("current_decision") or row.get("decision") or "unresolved") == "unresolved"]

    parsed_unreviewed = [
        row for row in processing
        if bool(row.get("parsed")) and not bool(row.get("reviewed"))
    ]
    reviewed_unadmitted = [
        row for row in processing
        if bool(row.get("reviewed")) and not bool(row.get("admitted"))
    ]

    semantic_candidates = [node for node in nodes.values() if node["kind"] == "semantic-candidate"]

    inspection = {
        "schema": "digital-esd-agent-world-inspection-v1",
        "artifact_root": str(artifact_root),
        "world_root": str(world_root),
        "summary": {
            "processing_records": len(processing),
            "graph_nodes": len(nodes),
            "graph_edges": len(edges),
            "semantic_candidates": len(semantic_candidates),
            "screening_review_packets_pending": len(unresolved_review),
            "retrieval_residual_count": len(retrieval_residual),
            "parsed_unreviewed_count": len(parsed_unreviewed),
            "reviewed_unadmitted_count": len(reviewed_unadmitted),
        },
        "authority_gates": {
            "screening_candidate_auto_promotes": False,
            "semantic_candidate_auto_promotes": False,
            "reviewed_evidence_auto_creates_source_audit_admission": False,
        },
        "next_actions": {
            "screening_review": unresolved_review[:100],
            "semantic_review_source_refs": [stable_ref(r) for r in parsed_unreviewed[:100]],
            "source_audit_source_refs": [stable_ref(r) for r in reviewed_unadmitted[:100]],
            "retrieval_residual": retrieval_residual[:100],
        },
    }

    world = {
        "schema": "digital-esd-candidate-world-v1",
        "authority": "mixed-candidate-and-observed",
        "artifact_root": str(artifact_root),
        "node_count": len(nodes),
        "edge_count": len(edges),
        "node_file": str(world_root / "nodes.jsonl"),
        "edge_file": str(world_root / "edges.jsonl"),
        "inspection_file": str(world_root / "agent-inspection.json"),
        "world_digest": canonical_digest({
            "nodes": sorted(nodes),
            "edges": sorted(edges),
        }),
        "important_boundary": "candidate graph structure may be automated; semantic/source authority requires explicit receipts",
    }
    return world, list(nodes.values()), list(edges.values()), inspection


def main() -> int:
    slr_root = resolve_slr_root()
    artifact_root = resolve_artifact_root(slr_root)
    artifact_root.mkdir(parents=True, exist_ok=True)

    loop = HERE / "run_screen_review_retrieve_parse_loop.py"
    decisions = artifact_root / "review" / "completed-decisions.jsonl"
    reviewed_ledger = artifact_root / "screening_ledger_reviewed.tsv"
    base_ledger = artifact_root / "screening_ledger.tsv"

    if loop.exists() and (reviewed_ledger.exists() or base_ledger.exists()):
        if decisions.exists() and decisions.stat().st_size > 0:
            run([
                sys.executable,
                str(loop),
                "advance",
                "--artifact-root",
                str(artifact_root),
                "--slr-root",
                str(slr_root),
                "--decisions",
                str(decisions),
                "--parse-verified",
            ], cwd=DASHI_ROOT)
        else:
            run([
                sys.executable,
                str(loop),
                "prepare-review",
                "--artifact-root",
                str(artifact_root),
                "--slr-root",
                str(slr_root),
            ], cwd=DASHI_ROOT)

    world, nodes, edges, inspection = build_world(artifact_root)
    world_root = artifact_root / "world"
    world_root.mkdir(parents=True, exist_ok=True)
    write_jsonl(world_root / "nodes.jsonl", nodes)
    write_jsonl(world_root / "edges.jsonl", edges)
    (world_root / "agent-inspection.json").write_text(
        json.dumps(inspection, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    (world_root / "world.json").write_text(
        json.dumps(world, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )

    print(json.dumps({
        "world": str(world_root / "world.json"),
        "inspection": str(world_root / "agent-inspection.json"),
        "nodes": len(nodes),
        "edges": len(edges),
        **inspection["summary"],
    }, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
