#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

SCHEMA = "slr-article-pnf-semantic-weld-v1"


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def _document_surface(document_ref: str) -> tuple[str, str]:
    parts = document_ref.split(":")
    if len(parts) >= 4 and parts[0] == "wiki":
        return parts[1], parts[2]
    return "", ""


def weld_article_pnf(closure: dict[str, Any], article: dict[str, Any]) -> dict[str, Any]:
    if closure.get("schema") != "slr-semantic-world-closure-v1":
        raise ValueError("unexpected semantic closure schema")
    if article.get("schema") != "slr-wikipedia-article-pnf-world-producer-v1":
        raise ValueError("unexpected article producer schema")
    if bool(closure.get("semantic_promotion", False)) or bool(article.get("semantic_promotion", False)):
        raise ValueError("refusing semantically promoted input")

    canonical: dict[str, dict[str, Any]] = {
        str(row.get("atom_id", "")): dict(row)
        for row in closure.get("canonical_atoms") or []
        if isinstance(row, dict) and row.get("atom_id")
    }
    surfaces = [dict(row) for row in closure.get("surfaces") or [] if isinstance(row, dict)]
    surface_by_id = {str(row.get("surface_id", "")): row for row in surfaces}
    evidence_surfaces: dict[str, list[str]] = {}
    for sid, surface in surface_by_id.items():
        for aid in surface.get("observed_atom_ids") or []:
            evidence_surfaces.setdefault(str(aid), []).append(sid)

    weld_by_claim = {
        str(row.get("claim_candidate_id", "")): dict(row)
        for row in article.get("qid_pnf_weld_candidates") or []
        if isinstance(row, dict) and row.get("claim_candidate_id")
    }
    added = 0
    for candidate in article.get("pnf_candidates") or []:
        if not isinstance(candidate, dict):
            continue
        cid = str(candidate.get("claim_candidate_id", ""))
        document_ref = str(candidate.get("document_ref", ""))
        if not cid or not document_ref:
            continue
        weld = weld_by_claim.get(cid) or {}
        qid = str(weld.get("qid", ""))
        doc_qid, language = _document_surface(document_ref)
        if not qid:
            qid = doc_qid
        if not qid or not language:
            continue
        atom_id = f"pnf:{cid}"
        canonical[atom_id] = {
            "atom_id": atom_id,
            "kind": "pnf-candidate",
            "subject_qid": qid,
            "document_ref": document_ref,
            "sentence_index": int(candidate.get("sentence_index", 0) or 0),
            "sentence_text_sha256": str(candidate.get("sentence_text_sha256", "")),
            "subject_terms": list(candidate.get("subject_terms") or []),
            "predicate_lemmas": list(candidate.get("predicate_lemmas") or []),
            "object_terms": list(candidate.get("object_terms") or []),
            "negated": bool(candidate.get("negated", False)),
            "surface_qid_identity_paid": bool(weld.get("surface_qid_identity_paid", False)),
            "span_entity_identity_paid": bool(weld.get("span_entity_identity_paid", False)),
            "qid_property_weld_paid": bool(weld.get("qid_property_weld_paid", False)),
            "claim_semantic_equivalence_paid": bool(weld.get("claim_semantic_equivalence_paid", False)),
            "parser_output_is_ontology_truth": False,
            "claim_truth_promoted": False,
            "evidence_class": "revision-pinned-spacy-pnf-candidate",
            "candidate_only": True,
            "semantic_promotion": False,
        }
        sid = f"{qid}:{language}"
        source_surface = surface_by_id.get(sid)
        if source_surface is not None and source_surface.get("status") == "observed":
            observed = set(str(x) for x in source_surface.get("observed_atom_ids") or [])
            observed.add(atom_id)
            source_surface["observed_atom_ids"] = sorted(observed)
            evidence_surfaces.setdefault(atom_id, []).append(sid)
        added += 1

    closure_ids = set(str(x) for x in closure.get("surface_semantic_closure_atom_ids") or [])
    closure_ids.update(aid for aid, atom in canonical.items() if atom.get("kind") == "pnf-candidate" and evidence_surfaces.get(aid))

    gaps: list[dict[str, Any]] = []
    propagated: list[dict[str, Any]] = []
    for surface in surfaces:
        sid = str(surface.get("surface_id", ""))
        qid = str(surface.get("qid", ""))
        language = str(surface.get("language", ""))
        if surface.get("status") != "observed":
            gaps.append({
                "surface_id": sid,
                "qid": qid,
                "language": language,
                "gap_kind": "missing-surface",
                "missing_atom_ids": [],
                "candidate_only": True,
                "semantic_promotion": False,
            })
            continue
        observed = set(str(x) for x in surface.get("observed_atom_ids") or [])
        missing: list[str] = []
        for aid in sorted(closure_ids):
            atom = canonical.get(aid) or {}
            atom_qid = str(atom.get("qid", "")) if atom.get("kind") == "qid" else str(atom.get("subject_qid", ""))
            if atom_qid == qid and aid not in observed:
                missing.append(aid)
                propagated.append({
                    "target_surface_id": sid,
                    "target_language": language,
                    "atom_id": aid,
                    "source_surface_ids": sorted(set(evidence_surfaces.get(aid, []))),
                    "available_to_target_consumer": True,
                    "target_surface_asserted": False,
                    "translation_equivalence_paid": False,
                    "claim_semantic_equivalence_paid": False,
                    "candidate_only": True,
                    "semantic_promotion": False,
                })
        gaps.append({
            "surface_id": sid,
            "qid": qid,
            "language": language,
            "gap_kind": "semantic-atom-gap",
            "missing_atom_ids": missing,
            "candidate_only": True,
            "semantic_promotion": False,
        })

    summary = dict(closure.get("summary") or {})
    summary["canonical_atoms"] = len(canonical)
    summary["surface_closure_atoms"] = len(closure_ids)
    summary["semantic_gap_atoms"] = sum(len(x.get("missing_atom_ids") or []) for x in gaps)
    summary["propagated_views"] = len(propagated)
    summary["article_pnf_atoms_added"] = added

    out = dict(closure)
    out["canonical_atoms"] = [canonical[k] for k in sorted(canonical)]
    out["surface_semantic_closure_atom_ids"] = sorted(closure_ids)
    out["surfaces"] = surfaces
    out["gaps"] = gaps
    out["propagated_views"] = propagated
    out["summary"] = summary
    out["article_pnf_world_weld_schema"] = SCHEMA
    out["article_pnf_creates_claim_truth"] = False
    out["parser_output_creates_ontology_truth"] = False
    out["cross_language_propagation_rewrites_source"] = False
    out["candidate_only"] = True
    out["semantic_promotion"] = False
    return out


def self_check() -> int:
    closure = {
        "schema": "slr-semantic-world-closure-v1",
        "canonical_atoms": [],
        "surface_semantic_closure_atom_ids": [],
        "surfaces": [],
        "summary": {},
        "semantic_promotion": False,
    }
    article = {
        "schema": "slr-wikipedia-article-pnf-world-producer-v1",
        "pnf_candidates": [],
        "qid_pnf_weld_candidates": [],
        "semantic_promotion": False,
    }
    out = weld_article_pnf(closure, article)
    assert out["article_pnf_creates_claim_truth"] is False
    assert out["parser_output_creates_ontology_truth"] is False
    assert out["cross_language_propagation_rewrites_source"] is False
    print(
        "SLR_ARTICLE_PNF_SEMANTIC_WELD_SELF_CHECK "
        f"schema={SCHEMA} passed=true article_pnf_creates_claim_truth=false "
        "parser_output_creates_ontology_truth=false cross_language_propagation_rewrites_source=false "
        "candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--closure", type=Path)
    p.add_argument("--article-pnf", type=Path)
    p.add_argument("--output", type=Path)
    p.add_argument("--self-check", action="store_true")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_check:
        return self_check()
    if not args.closure or not args.article_pnf or not args.output:
        raise SystemExit("--closure, --article-pnf and --output are required")
    out = weld_article_pnf(load(args.closure), load(args.article_pnf))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    s = out.get("summary") or {}
    print(
        "SLR_ARTICLE_PNF_SEMANTIC_WELD_RECEIPT "
        f"schema={SCHEMA} article_pnf_atoms_added={int(s.get('article_pnf_atoms_added', 0))} "
        f"canonical_atoms={int(s.get('canonical_atoms', 0))} semantic_gap_atoms={int(s.get('semantic_gap_atoms', 0))} "
        f"propagated_views={int(s.get('propagated_views', 0))} article_pnf_creates_claim_truth=false "
        "parser_output_creates_ontology_truth=false cross_language_propagation_rewrites_source=false "
        "candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
