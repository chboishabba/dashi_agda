#!/usr/bin/env python3
"""Build deterministic BH4 xPollenation neighbourhoods.

This joins already-acquired Rhea/ChEBI, SABIO adjudication, PDBe/SIFTS and
Wikimedia identity receipts into typed navigation/enrichment edges. It does
not perform acquisition and it never promotes a relation into flux payment.
The output is designed to be packaged as an ITIR `shared-shard-artifact/v1`
then mirrored to file/HF/IPFS without changing semantic identity.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path
from typing import Any

SCHEMA = "dashi.bh4-xpollenation.v1"
NEIGHBOURHOOD_SCHEMA = "dashi.xpollenation-neighbourhood/v1"
AUTHORITY = "navigation-enrichment-only"


def _text(value: Any) -> str:
    return str(value or "").strip()


def _edge_id(subject_ns: str, subject_id: str, relation: str, object_ns: str, object_id: str, source_ref: str) -> str:
    stable = "\n".join((subject_ns, subject_id, relation, object_ns, object_id, source_ref))
    return "xpe:" + hashlib.sha256(stable.encode("utf-8")).hexdigest()[:24]


def _edge(
    *,
    subject_ns: str,
    subject_id: str,
    relation: str,
    object_ns: str,
    object_id: str,
    source_ref: str,
    source_revision: str,
    acquisition_receipt: str,
    status: str,
    same_object_claimed: bool = False,
    same_object_verified: bool = False,
) -> dict[str, Any]:
    if same_object_verified and not same_object_claimed:
        raise ValueError("same-object verification requires an explicit same-object claim")
    return {
        "edgeId": _edge_id(subject_ns, subject_id, relation, object_ns, object_id, source_ref),
        "subject": {"namespace": subject_ns, "identifier": subject_id},
        "relation": relation,
        "object": {"namespace": object_ns, "identifier": object_id},
        "sourceRef": source_ref,
        "sourceRevision": source_revision,
        "acquisitionReceipt": acquisition_receipt,
        "status": status,
        "sameObjectClaimed": same_object_claimed,
        "sameObjectVerified": same_object_verified,
        "contextEquivalent": False,
        "promotionAllowed": False,
    }


def _protein_links(rhea: dict) -> dict[str, list[dict]]:
    out: dict[str, list[dict]] = defaultdict(list)
    for row in rhea.get("protein_reaction_links", []):
        rid = _text(row.get("rhea_id"))
        acc = _text(row.get("accession"))
        if rid and acc:
            out[rid].append(row)
    return out


def _reaction_rows(rhea: dict) -> dict[str, dict]:
    return {_text(row.get("rhea_id")): row for row in rhea.get("reactions", []) if _text(row.get("rhea_id"))}


def _sabio_rows(adjudication: dict) -> dict[str, list[dict]]:
    out: dict[str, list[dict]] = defaultdict(list)
    for row in adjudication.get("rows", []):
        for rid in row.get("finite_matrix_rhea_ids", []) or []:
            rid = _text(rid)
            if rid:
                out[rid].append(row)
    return out


def _sifts_by_accession(sifts: dict) -> dict[str, dict]:
    return {_text(row.get("accession")): row for row in sifts.get("results", []) if _text(row.get("accession"))}


def _wikimedia_by_accession(wikimedia: dict) -> dict[str, dict]:
    return {
        _text(row.get("uniprot_accession")): row
        for row in wikimedia.get("members", [])
        if _text(row.get("uniprot_accession"))
    }


def build(
    reaction_ids: list[str],
    *,
    rhea: dict,
    adjudication: dict,
    sifts: dict | None = None,
    wikimedia: dict | None = None,
) -> dict[str, Any]:
    links = _protein_links(rhea)
    reactions = _reaction_rows(rhea)
    sabio = _sabio_rows(adjudication)
    sifts_by_acc = _sifts_by_accession(sifts or {})
    wikimedia_by_acc = _wikimedia_by_accession(wikimedia or {})
    neighbourhoods: list[dict[str, Any]] = []

    for rid in sorted(set(_text(x) for x in reaction_ids if _text(x))):
        edges: list[dict[str, Any]] = []
        accessions: set[str] = set()

        for link in links.get(rid, []):
            acc = _text(link.get("accession"))
            if not acc:
                continue
            accessions.add(acc)
            edges.append(
                _edge(
                    subject_ns="rhea",
                    subject_id=rid,
                    relation="catalysed-by",
                    object_ns="uniprot",
                    object_id=acc,
                    source_ref="Rhea/UniProt panel cross-reference",
                    source_revision=_text(rhea.get("rhea_release_reference")) or _text(rhea.get("schema")),
                    acquisition_receipt=_text(rhea.get("source_uniprot_panel")) or _text(rhea.get("schema")),
                    status="identity-paid",
                )
            )

        reaction = reactions.get(rid, {})
        for participant in reaction.get("participants", []) or []:
            chebi = _text(participant.get("chebi_id"))
            if not chebi:
                continue
            edges.append(
                _edge(
                    subject_ns="rhea",
                    subject_id=rid,
                    relation="reaction-participant",
                    object_ns="chebi",
                    object_id=chebi,
                    source_ref=_text(reaction.get("participant_query")) or "Rhea RDF participant receipt",
                    source_revision=_text(rhea.get("rhea_release_reference")) or _text(rhea.get("schema")),
                    acquisition_receipt=_text(reaction.get("participant_sparql_response_sha256")) or rid,
                    status="identity-paid",
                )
            )

        for row in sabio.get(rid, []):
            acc = _text(row.get("accession"))
            if acc:
                accessions.add(acc)
            entry = _text(row.get("entry_id")) or "unknown-entry"
            parameter = _text(row.get("parameter_name")) or _text(row.get("parameter_type")) or "parameter"
            object_id = f"{entry}::{acc}::{parameter}"
            edges.append(
                _edge(
                    subject_ns="rhea",
                    subject_id=rid,
                    relation="kinetic-parameter-for",
                    object_ns="sabio",
                    object_id=object_id,
                    source_ref="SABIO parameter candidate mapped through exact UniProt panel",
                    source_revision=_text(adjudication.get("schema")),
                    acquisition_receipt=entry,
                    status="discovered",
                )
            )

        for acc in sorted(accessions):
            sifts_row = sifts_by_acc.get(acc, {})
            for structure in sifts_row.get("structures", []) or []:
                pdb_id = _text(structure.get("pdb_id"))
                if not pdb_id or int(structure.get("matching_segment_count") or 0) <= 0:
                    continue
                edges.append(
                    _edge(
                        subject_ns="uniprot",
                        subject_id=acc,
                        relation="protein-structure-of",
                        object_ns="pdb",
                        object_id=pdb_id,
                        source_ref="PDBe/SIFTS _pdbx_sifts_unp_segments",
                        source_revision=_text((sifts or {}).get("schema")),
                        acquisition_receipt=_text(structure.get("raw_sha256")) or pdb_id,
                        status="identity-paid",
                    )
                )

            wiki = wikimedia_by_acc.get(acc, {})
            if wiki.get("identity_status") == "verified":
                for match in wiki.get("exact_p352_matches", []) or []:
                    qid = _text(match.get("protein_qid"))
                    if not qid or match.get("exact_p352_match") is not True:
                        continue
                    edges.append(
                        _edge(
                            subject_ns="uniprot",
                            subject_id=acc,
                            relation="curated-cross-reference",
                            object_ns="wikidata-qid",
                            object_id=qid,
                            source_ref="Wikidata exact P352 UniProt match",
                            source_revision=_text(match.get("wikidata_lastrevid")) or _text((wikimedia or {}).get("panel_schema")),
                            acquisition_receipt=_text(match.get("wikidata_entity_response_sha256")) or qid,
                            status="identity-paid",
                            same_object_claimed=True,
                            same_object_verified=True,
                        )
                    )

        dedup = {edge["edgeId"]: edge for edge in edges}
        ordered_edges = [dedup[key] for key in sorted(dedup)]
        neighbourhoods.append(
            {
                "schema": NEIGHBOURHOOD_SCHEMA,
                "subject": {"namespace": "rhea", "identifier": rid},
                "edges": ordered_edges,
                "authority": AUTHORITY,
                "establishesProof": False,
                "establishesPayment": False,
            }
        )

    return {
        "schema": SCHEMA,
        "reaction_count": len(neighbourhoods),
        "finite_reaction_ids": [item["subject"]["identifier"] for item in neighbourhoods],
        "neighbourhoods": neighbourhoods,
        "promotion_boundary": {
            "cross_domain_edge_creates_flux_bound": False,
            "qid_adjacency_creates_assay_applicability": False,
            "pdb_mapping_creates_catalytic_mechanism": False,
            "sabio_association_creates_flux_payment": False,
            "rhea_identity_collapses_isoform_context": False,
            "oeis_match_creates_biochemical_identity": False,
            "artifact_cid_creates_kinetic_admissibility": False,
        },
    }


def _read(path: Path | None) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path else {}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--matrix", type=Path, required=True)
    parser.add_argument("--rhea", type=Path, required=True)
    parser.add_argument("--adjudication", type=Path, required=True)
    parser.add_argument("--sifts", type=Path)
    parser.add_argument("--wikimedia", type=Path)
    parser.add_argument("-o", "--output", type=Path, required=True)
    parser.add_argument("--neighbourhood-dir", type=Path)
    args = parser.parse_args()

    matrix = _read(args.matrix)
    result = build(
        [str(x) for x in matrix.get("reaction_index", [])],
        rhea=_read(args.rhea),
        adjudication=_read(args.adjudication),
        sifts=_read(args.sifts),
        wikimedia=_read(args.wikimedia),
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if args.neighbourhood_dir:
        args.neighbourhood_dir.mkdir(parents=True, exist_ok=True)
        for item in result["neighbourhoods"]:
            rid = item["subject"]["identifier"].replace(":", "-")
            (args.neighbourhood_dir / f"{rid}.json").write_text(
                json.dumps(item, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
