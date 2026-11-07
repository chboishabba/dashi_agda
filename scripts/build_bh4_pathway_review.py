#!/usr/bin/env python3
"""Project existing BH4 ontology receipts into a reversible read-only review worklist.

DASHI implementation. Reuses the existing ontology/PNF and ITIR-US-17,
WIKI-US-01..04 user-story boundaries; this is NOT an SLR S29, ITIR MCP,
Wikidata or GO-CAM native API, and does not perform a live ontology edit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

INPUT_SCHEMA = "dashi.bh4-pathway-ontology-interop.v1"
OUTPUT_SCHEMA = "dashi.bh4-pathway-review-worklist.v1"
STORIES = ["ITIR-US-01", "ITIR-US-02", "ITIR-US-17",
           "WIKI-US-01", "WIKI-US-02", "WIKI-US-03", "WIKI-US-04"]


def _id(kind: str, owner: str, code: str) -> str:
    raw = json.dumps([kind, owner, code], separators=(",", ":"), ensure_ascii=False)
    return "bh4-review:" + hashlib.sha256(raw.encode("utf-8")).hexdigest()[:24]


def _coord(value: dict) -> str:
    if not isinstance(value, dict) or not value.get("namespace") or not value.get("identifier"):
        raise ValueError("missing typed external coordinate")
    return str(value["namespace"]) + ":" + str(value["identifier"])


def _hold(kind: str, owner: str, reason: str, *, refs: list[str],
          witness: str, next_action: str, source_role: str) -> dict:
    if not all(isinstance(x, str) and x for x in refs):
        raise ValueError("empty or malformed reopen reference")
    return {
        "id": _id(kind, owner, reason),
        "kind": kind,
        "subject": owner,
        "diagnostic_origin": reason,
        "source_role": source_role,
        "source_reopen_refs": refs,
        "exact_witness_required": witness,
        "next_action": next_action,
        "classification": "active-missing-evidence",
        "repair_disposition": "hold-for-review",
        "consumer_adequate": False,
        "edited_external_ontology": False,
        "establishes_claim_truth": False,
        "establishes_flux_payment": False,
    }


def build(pathway: dict, *, source_receipts: dict | None = None) -> dict:
    if pathway.get("schema") != INPUT_SCHEMA or pathway.get("authority") != "navigation-and-hypothesis-only":
        raise ValueError("unexpected or promoted pathway")
    boundary = pathway.get("promotion_boundary") or {}
    if not boundary or any(v is not False for v in boundary.values()):
        raise ValueError("pathway must have complete non-promoting boundary")
    reactions = pathway.get("reactions")
    species = pathway.get("species")
    if not isinstance(reactions, list) or not isinstance(species, list):
        raise ValueError("pathway has no finite matrix carriers")
    if source_receipts is not None and source_receipts.get("schema") != "dashi.bh4-source-reopen-packet.v1":
        raise ValueError("source receipt packet has wrong schema")
    # Source packet is a *reference index*, not a source authentication verdict.
    source_index = {}
    for row in (source_receipts or {}).get("sources", []):
        if not all(row.get(field) for field in
                   ("source_id", "source_revision", "snapshot_digest", "content_locator")):
            raise ValueError("source envelope missing revision, digest or locator")
        if row.get("visibility") not in ("public", "internal", "restricted"):
            raise ValueError("source envelope missing explicit visibility")
        key = row["source_id"]
        if key in source_index:
            raise ValueError("duplicate source envelope")
        source_index[key] = row

    work = []
    seen = set()

    def add(*args, **kwargs):
        item = _hold(*args, **kwargs)
        if item["id"] in seen:
            raise ValueError("duplicate obligation identity")
        seen.add(item["id"])
        work.append(item)

    for row in pathway.get("author_hypothesis_edges", []):
        if row.get("status") != "source-reconstruction-candidate" or row.get("independent_primary_text_verification") is not False:
            raise ValueError("unreviewed author hypothesis promotion")
        sid = row.get("source_id")
        owner = ":".join([str(sid), str(row.get("subject")), str(row.get("predicate")), str(row.get("object"))])
        if not sid or not row.get("source_locator") or not row.get("repo_reconstruction_owner"):
            raise ValueError("author edge missing attribution")
        packet = source_index.get(sid)
        refs = [str(row["source_locator"]), str(row["repo_reconstruction_owner"])]
        if packet:
            if packet["visibility"] == "public":
                refs += [str(packet["content_locator"]), str(packet["source_revision"]),
                         str(packet["snapshot_digest"])]
            else:
                # Retain an opaque source handle; the receiving authorized
                # inspector may resolve it inside SLR, never in public export.
                refs.append("restricted-source-handle:" + str(sid))
        add("author-source", owner, "original-passage-not-authenticated",
            refs=refs,
            witness="primary source revision + exact passage/figure and source-to-edge correspondence",
            next_action="Open original Kitzerow passage; separate the recorded source claim from the DASHI reconstruction",
            source_role="Kitzerow creator claim (not established biochemical mechanism)")

    for row in reactions:
        rid = _coord(row.get("coordinate"))
        if row["coordinate"]["namespace"] != "rhea" or not row.get("participants"):
            raise ValueError("malformed finite reaction")
        if row.get("flux_interval") is not None or row.get("same_object_payment") is not False:
            raise ValueError("source-unpaid reaction was promoted")
        refs = [rid, str(row.get("source_receipt") or "source-receipt-unavailable")]
        if row.get("compartment") is None:
            add("context", rid, "reaction-compartment-not-paid", refs=refs,
                witness="isoform, cellular/tissue compartment, state and sample/time correspondence",
                next_action="Find compartment-resolved reaction/isoform evidence; do not copy another tissue's location",
                source_role="external Rhea/UniProt/primary physiology")
        if row.get("rate_law") is None:
            add("reaction-flux", rid, "reaction-kinetics-not-paid", refs=refs,
                witness="same-assay identity, enzyme abundance, normalization, kinetics-to-flux translation",
                next_action="Inspect SABIO/primary kinetics and existing BH4 joint payment ledger",
                source_role="primary kinetics / assay context")
        if row.get("physiological_direction_paid") is not True:
            add("direction", rid, "in-vivo-direction-unresolved", refs=refs,
                witness="same-state directionality and chemical thermodynamics",
                next_action="Adjudicate curated Rhea direction against physiological conditions",
                source_role="Rhea reaction orientation vs measured biological flow")

    for row in species:
        species_id = _coord(row.get("coordinate"))
        if row.get("external_exchange_interval") is not None:
            raise ValueError("unpaid exchange interval was promoted")
        refs = [species_id, "BH4OpenMetabolicNetworkAdapterExact"]
        if row.get("compartment") is None:
            add("context", species_id, "species-compartment-not-paid", refs=refs,
                witness="sample, chemical form, compartment, tissue, time and pH/microspecies equivalence",
                next_action="Inspect actual compartment assignments before constructing species-in-compartment identities",
                source_role="Rhea/ChEBI and physical sample")
        add("exchange-flux", species_id, "source-sink-rate-unresolved", refs=refs,
            witness="same-state transporter/turnover or time-resolved exchange rate",
            next_action="Acquire transport/source/sink evidence; do not infer rates from metabolite presence",
            source_role="primary transport/turnover study")

    for row in pathway.get("unparsed_external_annotation_fields", []):
        rid = row.get("rhea_id")
        key = str(rid) + ":" + str(row.get("source_field"))
        add("ontology-mapping", key, "unparsed-source-annotation", refs=[
            str(rid or "rhea-id-unavailable"), str(row.get("source_field") or "field-unavailable"),
            str(row.get("source_value") or "raw-value-unavailable")],
            witness="source revision + full original field and validated typed target identity",
            next_action="Inspect source TSV field; propose mapping for specialist review, do not invent an external ID",
            source_role="Rhea REST cross-reference")

    for row in pathway.get("ontology_cross_references", []):
        owner = _coord(row.get("reaction")) + "=>" + _coord(row.get("target"))
        if row.get("same_biological_event_verified") is not False or row.get("flux_paid") is not False:
            raise ValueError("ontology cross-reference promoted without an independent bridge")
        add("ontology-mapping", owner, "cross-ontology-event-identity-unresolved",
            refs=[_coord(row["reaction"]), _coord(row["target"]),
                  str(row.get("source_receipt") or "rhea-rest-receipt-unavailable")],
            witness="source revision, mapping relation, taxon, event direction, evidence and context match",
            next_action="Request reviewed mapping classification (exact/broader/narrower/overlap/disjoint/bridge/abstain)",
            source_role=str(row.get("source_owner") or "external biological ontology"))

    for row in pathway.get("excluded_nonfinite_reactions", []):
        rid = str(row.get("rhea_id") or "unidentified")
        add("chemistry", rid, "non-finite-reaction-residual",
            refs=[rid, str(row.get("reason") or "representation-unresolved")],
            witness="typed polymer/R-group/residue representation with source-checked stoichiometry",
            next_action="Reopen original Rhea reaction; extend existing representation, never add synthetic zero column",
            source_role="Rhea participant model")

    work.sort(key=lambda row: (row["kind"], row["subject"], row["id"]))
    families = dict(sorted(Counter(row["kind"] for row in work).items()))
    # Human-readable first. No source text is invented or published.
    return {
        "schema": OUTPUT_SCHEMA,
        "authority": "read-only-candidate-review",
        "product_role": "portable contract for SLR/ITIR/Dioxus; not an S29 persistence receipt",
        "user_story_refs": STORIES,
        "orientation": {
            "subject": "Kitzerow BH4 candidate pathway network",
            "what_is_known": {
                "finite_reactions": len(reactions),
                "indexed_species": len(species),
                "ontology_cross_references": len(pathway.get("ontology_cross_references", [])),
                "candidate_author_edges": len(pathway.get("author_hypothesis_edges", [])),
            },
            "what_is_not_known": "No complete source-verified author graph, compartment-matched flux or clinical causal result",
            "disclosure_route": ["Orient", "Project", "Why?", "Source", "Meaning", "Follow", "Next unresolved"],
        },
        "obligations": work,
        "obligation_family_counts": families,
        "external_source_envelopes_supplied": len(source_index),
        "restricted_source_envelopes_not_exposed": sum(
            row["visibility"] != "public" for row in source_index.values()),
        "source_packet_hashes_independently_authenticated": False,
        "candidate_publication_allowed": False,
        "evidence_mode": "external claims, source text and review status are independent",
        "promotion_boundary": {
            "read_only": True, "mutates_wikidata": False, "mutates_slr": False,
            "candidate_repair_is_authorized_edit": False,
            "wiki_or_ontology_reference_is_primary_evidence": False,
            "source_digest_authenticates_historical_claim": False,
            "diagnostic_proves_disease_mechanism": False,
            "missing_flux_is_zero": False,
        }
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pathway", type=Path, required=True)
    ap.add_argument("--source-receipts", type=Path)
    ap.add_argument("-o", "--output", type=Path, required=True)
    args = ap.parse_args()
    packet = json.loads(args.pathway.read_text(encoding="utf-8"))
    source = json.loads(args.source_receipts.read_text(encoding="utf-8")) if args.source_receipts else None
    result = build(packet, source_receipts=source)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, sort_keys=True, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({"schema": OUTPUT_SCHEMA, "obligations": len(result["obligations"]),
                      "families": result["obligation_family_counts"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
