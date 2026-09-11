#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

SCHEMA = "slr-gwb-candidate-world-v1"
TARGET_SCHEMA = "sl.candidate_world_model.v0_1"
CERT_SCHEMA = "sensiblaw.gwb-full-certification-receipt.v0_1"
PROJECTION_SCHEMA = "sensiblaw.gwb-source-projection.v0_1"


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--certification", type=Path, required=True)
    p.add_argument("--projection-manifest", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    cert = load(args.certification)
    projection = load(args.projection_manifest)

    if cert.get("schema_version") != CERT_SCHEMA:
        raise SystemExit(f"unexpected certification schema: {cert.get('schema_version')!r}")
    if projection.get("schema_version") != PROJECTION_SCHEMA:
        raise SystemExit(f"unexpected projection schema: {projection.get('schema_version')!r}")
    if not bool((cert.get("invariants") or {}).get("full_gate_pass", False)):
        raise SystemExit("GWB certification full gate is not paid")
    metrics = cert.get("metrics") or {}
    if int(metrics.get("parity_failed", -1)) != 0:
        raise SystemExit("GWB certification has parity failures")
    if bool(metrics.get("published", True)):
        raise SystemExit("GWB certification indicates publication")

    cert_docs = cert.get("per_document") or []
    proj_docs = projection.get("documents") or []
    if len(cert_docs) != len(proj_docs) or len(cert_docs) != int(cert.get("document_count", -1)):
        raise SystemExit("GWB document-count mismatch")

    projected_manifest_sha = sha256_file(args.projection_manifest)
    expected_manifest_sha = str(cert.get("projection_manifest_sha256", ""))
    if expected_manifest_sha and projected_manifest_sha != expected_manifest_sha:
        raise SystemExit("projection manifest SHA does not match certification")

    projection_by_ordinal = {int(d["document_ordinal"]): d for d in proj_docs}
    claims: list[dict[str, Any]] = []
    relations: list[dict[str, Any]] = []
    provenance: list[dict[str, Any]] = []
    source_families: set[str] = set()
    total_sentences = 0

    for doc in cert_docs:
        ordinal = int(doc["document_ordinal"])
        proj = projection_by_ordinal.get(ordinal)
        if not isinstance(proj, dict):
            raise SystemExit(f"missing projection document {ordinal}")
        if str(doc.get("projected_sha256", "")) != str(proj.get("projected_sha256", "")):
            raise SystemExit(f"projected SHA mismatch for document {ordinal}")
        if int(doc.get("projected_bytes", -1)) != int(proj.get("projected_bytes", -2)):
            raise SystemExit(f"projected byte mismatch for document {ordinal}")

        sentence_start = int(doc["sentence_id_start"])
        sentence_end = int(doc["sentence_id_end_exclusive"])
        if sentence_end < sentence_start:
            raise SystemExit(f"invalid sentence range document {ordinal}")
        if sentence_end - sentence_start != int(doc.get("sentences", -1)):
            raise SystemExit(f"sentence accounting mismatch document {ordinal}")
        total_sentences += sentence_end - sentence_start

        family_refs = [str(x) for x in (proj.get("family_refs") or [])]
        source_families.update(family_refs)
        source_sha = str(proj.get("source_sha256", ""))
        projected_sha = str(proj.get("projected_sha256", ""))
        source_kind = str(proj.get("source_kind", ""))
        projector = str(proj.get("projector", ""))
        doc_anchor = f"gwb-document:{ordinal}"
        source_anchor = f"source-sha256:{source_sha}"
        projected_anchor = f"projection-sha256:{projected_sha}"

        provenance.append({
            "provenance_id": doc_anchor,
            "provenance_kind": "gwb_source_projection_receipt",
            "document_ordinal": ordinal,
            "source_sha256": source_sha,
            "projected_sha256": projected_sha,
            "source_kind": source_kind,
            "projector": projector,
            "family_refs": family_refs,
            "source_bytes": int(proj.get("source_bytes", 0)),
            "projected_bytes": int(proj.get("projected_bytes", 0)),
            "sentence_id_start": sentence_start,
            "sentence_id_end_exclusive": sentence_end,
            "paragraph_id_start": int(doc.get("paragraph_id_start", 0)),
            "paragraph_id_end_exclusive": int(doc.get("paragraph_id_end_exclusive", 0)),
            "raw_or_projected_text_embedded": False,
        })

        previous_id = ""
        for sentence_id in range(sentence_start, sentence_end):
            node_id = f"gwb-sentence:{sentence_id}"
            claims.append({
                "node_id": node_id,
                "node_kind": "document_sentence_candidate",
                "label": f"GWB document {ordinal} sentence {sentence_id}",
                "status": "candidate",
                "source_anchor_ids": [doc_anchor, source_anchor, projected_anchor],
                "conflict_ids": [],
                "promotion_status": "candidate_only",
                "residual": {
                    "canonical_claim_identity": "unpaid",
                    "speaker_or_quote_gold": "unpaid",
                    "world_semantics": "unpaid",
                    "claim_truth_promoted": False,
                },
                "metadata": {
                    "schema": SCHEMA,
                    "document_ordinal": ordinal,
                    "sentence_id": sentence_id,
                    "source_kind": source_kind,
                    "family_refs": family_refs,
                    "projected_sha256": projected_sha,
                    "direct_reference_parity_certified": True,
                    "raw_text_embedded": False,
                    "candidate_only": True,
                    "semantic_promotion": False,
                },
            })
            if previous_id:
                relations.append({
                    "relation_id": f"gwb-sentence-adjacency:{sentence_id - 1}:{sentence_id}",
                    "source_id": previous_id,
                    "target_id": node_id,
                    "relation_kind": "same_document_next_sentence_candidate",
                    "status": "candidate",
                    "source_anchor_ids": [doc_anchor, projected_anchor],
                    "promotion_status": "candidate_only",
                    "residual": {"discourse_or_causal_relation": "not-asserted"},
                    "metadata": {
                        "schema": SCHEMA,
                        "document_ordinal": ordinal,
                        "structural_adjacency_only": True,
                        "semantic_promotion": False,
                    },
                })
            previous_id = node_id

    certified_sentences = int(metrics.get("sentences", -1))
    if total_sentences != certified_sentences:
        raise SystemExit(f"global sentence accounting mismatch: {total_sentences} != {certified_sentences}")
    if int(metrics.get("parity_checked", -1)) != certified_sentences:
        raise SystemExit("parity_checked does not equal certified sentences")

    model_id = f"gwb-slr-world:{projected_manifest_sha[:16]}"
    out = {
        "schema_version": TARGET_SCHEMA,
        "model_id": model_id,
        "lane_family": "slr_document_corpus",
        "model_status": "candidate",
        "source_mode": "gwb_certified_projection_receipt",
        "entities": [],
        "claims": claims,
        "relations": relations,
        "events": [],
        "timelines": [],
        "authority_surfaces": [],
        "provenance_graph": provenance,
        "conflicts": [],
        "residuals": [],
        "update_rules": [{
            "rule_id": "gwb-evidence-append-only-v1",
            "rule_kind": "append_only_evidence_refinement",
            "description": "Later claim/source/world evidence may contract sentence candidates without rewriting certified source/projection provenance.",
            "semantic_promotion": False,
        }],
        "projections": [{
            "projection_id": SCHEMA,
            "projection_kind": "gwb_certification_to_candidate_world",
            "status": "candidate",
            "source_certification_schema": CERT_SCHEMA,
            "source_projection_schema": PROJECTION_SCHEMA,
            "semantic_promotion": False,
        }],
        "external_graph_views": [],
        "external_bridge_candidates": [],
        "external_bridge_decisions": [],
        "external_pressure_results": [],
        "metadata": {
            "adapter_schema": SCHEMA,
            "schema": SCHEMA,
            "profile_ref": cert.get("profile_ref", projection.get("profile_ref", "")),
            "certification_authority": cert.get("authority", ""),
            "projection_authority": projection.get("authority", ""),
            "projection_manifest_sha256": projected_manifest_sha,
            "source_family_refs": sorted(source_families),
            "document_count": len(cert_docs),
            "certified_sentence_count": certified_sentences,
            "certified_paragraph_count": int(metrics.get("paragraphs", 0)),
            "parity_failed": int(metrics.get("parity_failed", -1)),
            "published": bool(metrics.get("published", True)),
            "parser_relative_ratio": metrics.get("parser_relative_ratio"),
            "raw_or_projected_text_embedded": False,
            "canonical_claim_identity_attached": False,
            "speaker_quote_gold_attached": False,
            "world_constraints_attached": False,
            "candidate_only": True,
            "semantic_promotion": False,
        },
        "summary": {
            "sentence_candidate_count": len(claims),
            "sentence_adjacency_relation_count": len(relations),
            "provenance_document_count": len(provenance),
            "source_family_count": len(source_families),
            "canonical_claim_reference_count": 0,
        },
        "status_counts": {
            "candidate": len(claims) + len(relations),
            "conflicted": 0,
        },
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "SLR_GWB_CANDIDATE_WORLD_RECEIPT "
        f"schema={SCHEMA} target={TARGET_SCHEMA} documents={len(cert_docs)} "
        f"sentences={len(claims)} relations={len(relations)} provenance={len(provenance)} "
        f"parity_failed={metrics.get('parity_failed')} published={str(bool(metrics.get('published', True))).lower()} "
        "raw_text_embedded=false canonical_claim_identity=false world_constraints=false "
        "candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
