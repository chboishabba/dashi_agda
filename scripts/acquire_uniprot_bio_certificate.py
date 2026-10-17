#!/usr/bin/env python3
"""Acquire UniProtKB JSON records and emit bounded provenance certificates.

Single-accession mode is preserved:

    python3 scripts/acquire_uniprot_bio_certificate.py P09417

The Kitzerow/BH4 panel can be acquired in one reproducible pass:

    python3 scripts/acquire_uniprot_bio_certificate.py --kitzerow-bh4-panel -o panel.json

Every record keeps its own raw-response SHA-256 and release headers.  A panel
with one failed accession remains explicitly partial; failures are never silently
promoted to acquired records.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path


KITZEROW_BH4_PANEL = [
    {"symbol": "GCH1", "accession": "P30793", "sector": "BH4 synthesis / regulation"},
    {"symbol": "GCHFR", "accession": "P30047", "sector": "GCH1 feedback regulation"},
    {"symbol": "PTS", "accession": "Q03393", "sector": "BH4 synthesis"},
    {"symbol": "SPR", "accession": "P35270", "sector": "BH4 synthesis"},
    {"symbol": "PCBD1", "accession": "P61457", "sector": "BH4 recycling"},
    {"symbol": "QDPR", "accession": "P09417", "sector": "BH4 recycling"},
    {"symbol": "NOS1", "accession": "P29475", "sector": "NOS / neuronal"},
    {"symbol": "NOS2", "accession": "P35228", "sector": "NOS / inducible"},
    {"symbol": "NOS3", "accession": "P29474", "sector": "NOS / endothelial"},
    {"symbol": "PAH", "accession": "P00439", "sector": "aromatic amino-acid hydroxylase"},
    {"symbol": "TH", "accession": "P07101", "sector": "aromatic amino-acid hydroxylase"},
    {"symbol": "TPH1", "accession": "P17752", "sector": "aromatic amino-acid hydroxylase"},
    {"symbol": "TPH2", "accession": "Q8IWU9", "sector": "aromatic amino-acid hydroxylase"},
    {"symbol": "AGMO", "accession": "Q6ZNB7", "sector": "ether-lipid cleavage"},
    {"symbol": "TSC2", "accession": "P49815", "sector": "NO downstream / TSC2-mTOR"},
    {"symbol": "MTOR", "accession": "P42345", "sector": "NO downstream / TSC2-mTOR"},
]


def fetch_uniprot(accession: str) -> tuple[bytes, dict[str, str]]:
    url = f"https://rest.uniprot.org/uniprotkb/{accession}?format=json"
    request = urllib.request.Request(
        url,
        headers={
            "Accept": "application/json",
            "User-Agent": "DASHI-external-biology-acquisition/1.1",
        },
    )
    with urllib.request.urlopen(request, timeout=60) as response:
        raw = response.read()
        headers = {key.lower(): value for key, value in response.headers.items()}
    return raw, headers


def select_cross_references(record: dict) -> list[dict[str, object]]:
    keep = {
        "PDB",
        "AlphaFoldDB",
        "InterPro",
        "GO",
        "Rhea",
        "Reactome",
        "Ensembl",
        "RefSeq",
        "ChEBI",
    }
    selected: list[dict[str, object]] = []
    for xref in record.get("uniProtKBCrossReferences", []):
        database = xref.get("database")
        if database in keep:
            selected.append(
                {
                    "database": database,
                    "id": xref.get("id"),
                    "properties": xref.get("properties", []),
                }
            )
    return selected


def build_certificate(accession: str, raw: bytes, headers: dict[str, str]) -> dict:
    record = json.loads(raw)
    sequence = record.get("sequence", {})
    return {
        "certificate_schema": "dashi.external-biology.uniprot.v1",
        "acquired_at_utc": datetime.now(timezone.utc).isoformat(),
        "request": f"https://rest.uniprot.org/uniprotkb/{accession}?format=json",
        "raw_sha256": hashlib.sha256(raw).hexdigest(),
        "http_release": headers.get("x-uniprot-release"),
        "http_release_date": headers.get("x-uniprot-release-date"),
        "primary_accession": record.get("primaryAccession"),
        "entry_name": record.get("uniProtkbId"),
        "entry_type": record.get("entryType"),
        "entry_audit": record.get("entryAudit", {}),
        "organism": record.get("organism", {}),
        "sequence": {
            "length": sequence.get("length"),
            "mol_weight": sequence.get("molWeight"),
            "crc64": sequence.get("crc64"),
            "md5": sequence.get("md5"),
        },
        "cross_references": select_cross_references(record),
        "promotion_boundary": {
            "database_assertion_creates_biological_truth": False,
            "reviewed_status_implies_direct_experimental_proof": False,
            "cross_reference_creates_same_object_identity": False,
            "certificate_creates_downstream_applicability": False,
            "certificate_creates_measured_compartment_flux": False,
            "certificate_creates_whole_model_confirmation": False,
        },
    }


def acquire_one(accession: str) -> dict:
    raw, headers = fetch_uniprot(accession)
    return build_certificate(accession, raw, headers)


def acquire_panel() -> tuple[dict, int]:
    acquired: list[dict] = []
    failures: list[dict[str, str]] = []
    for member in KITZEROW_BH4_PANEL:
        accession = member["accession"]
        try:
            certificate = acquire_one(accession)
            acquired.append({**member, "certificate": certificate})
        except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, json.JSONDecodeError) as exc:
            failures.append({**member, "error": str(exc)})

    release_set = sorted(
        {
            item["certificate"].get("http_release")
            for item in acquired
            if item["certificate"].get("http_release")
        }
    )
    panel = {
        "panel_schema": "dashi.external-biology.uniprot-panel.v1",
        "panel_id": "kitzerow-bh4-nos-aaah-agmo-tsc2-mtor",
        "requested_members": len(KITZEROW_BH4_PANEL),
        "acquired_members": len(acquired),
        "failed_members": len(failures),
        "complete": not failures,
        "release_set": release_set,
        "members": acquired,
        "failures": failures,
        "promotion_boundary": {
            "complete_panel_creates_whole_model_confirmation": False,
            "isolated_reaction_nodes_create_allocator_flux": False,
            "panel_identity_creates_compartment_identity": False,
        },
    }
    return panel, 0 if not failures else 3


def render(payload: dict, output: Path | None) -> None:
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("accession", nargs="?", help="UniProtKB accession, e.g. P09417")
    parser.add_argument(
        "--kitzerow-bh4-panel",
        action="store_true",
        help="Acquire the 16-member BH4/NOS/AAAH/AGMO/TSC2/MTOR panel",
    )
    parser.add_argument("-o", "--output", type=Path, help="Write certificate JSON here; default stdout")
    args = parser.parse_args()

    if args.kitzerow_bh4_panel and args.accession:
        parser.error("choose either one accession or --kitzerow-bh4-panel")
    if not args.kitzerow_bh4_panel and not args.accession:
        parser.error("provide an accession or --kitzerow-bh4-panel")

    if args.kitzerow_bh4_panel:
        payload, exit_code = acquire_panel()
        render(payload, args.output)
        return exit_code

    accession = args.accession.strip().upper()
    try:
        certificate = acquire_one(accession)
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, json.JSONDecodeError) as exc:
        print(f"UniProt acquisition failed for {accession}: {exc}", file=sys.stderr)
        return 2

    render(certificate, args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
