#!/usr/bin/env python3
"""Acquire bounded Rhea/ChEBI reaction certificates for the BH4 lane.

This script is deliberately reaction-identity/stoichiometry facing. It does not
infer kinetics, cellular flux, compartment state, allocator competition or
disease mechanism. Rhea's REST table is the primary acquisition source.

Modes:
  --qdpr
      acquire and validate the exact QDPR/RHEA:32253 microspecies fixture.
  --from-uniprot-panel PATH
      read the already-acquired 16-member UniProt panel, enumerate every Rhea
      cross-reference without re-keying proteins manually, and acquire exact
      Rhea equation/ChEBI-ID rows with per-response SHA-256 receipts.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import sys
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

RHEA_TABLE = "https://www.rhea-db.org/rhea/"
USER_AGENT = "DASHI-rhea-chebi-acquisition/1.0 (https://github.com/chboishabba/dashi_agda)"

QDPR_EXPECTED = {
    "generic_rhea_id": "RHEA:17869",
    "directed_rhea_id": "RHEA:17871",
    "specific_directed_rhea_id": "RHEA:32253",
    "participants": [
        {"side": "substrate", "chebi_id": "CHEBI:43120", "broader_chebi_id": "CHEBI:20680", "name": "(6R)-L-erythro-6,7-dihydrobiopterin", "formula": "C9H13N5O3", "charge": 0},
        {"side": "substrate", "chebi_id": "CHEBI:57945", "broader_chebi_id": "CHEBI:57945", "name": "NADH", "formula": "C21H27N7O14P2", "charge": -2},
        {"side": "substrate", "chebi_id": "CHEBI:15378", "broader_chebi_id": "CHEBI:15378", "name": "H+", "formula": "H", "charge": 1},
        {"side": "product", "chebi_id": "CHEBI:59560", "broader_chebi_id": "CHEBI:15372", "name": "(6R)-L-erythro-5,6,7,8-tetrahydrobiopterin", "formula": "C9H15N5O3", "charge": 0},
        {"side": "product", "chebi_id": "CHEBI:57540", "broader_chebi_id": "CHEBI:57540", "name": "NAD+", "formula": "C21H26N7O14P2", "charge": -1},
    ],
}


def _get(url: str) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=60) as response:
        return response.read()


def fetch_rhea_row(rhea_id: str) -> dict:
    numeric = rhea_id.replace("RHEA:", "")
    params = urllib.parse.urlencode(
        {
            "query": f"id:{numeric}",
            "columns": "rhea-id,equation,chebi,chebi-id,ec,pubmed",
            "format": "tsv",
            "limit": "10",
        }
    )
    raw = _get(f"{RHEA_TABLE}?{params}")
    rows = list(csv.DictReader(io.StringIO(raw.decode("utf-8")), delimiter="\t"))
    exact = [row for row in rows if row.get("Reaction identifier") == rhea_id]
    if len(exact) != 1:
        raise RuntimeError(f"expected exactly one {rhea_id} row, got {len(exact)}")
    return {"row": exact[0], "raw_sha256": hashlib.sha256(raw).hexdigest()}


def acquire_qdpr() -> dict:
    generic = fetch_rhea_row(QDPR_EXPECTED["generic_rhea_id"])
    directed = fetch_rhea_row(QDPR_EXPECTED["directed_rhea_id"])
    specific = fetch_rhea_row(QDPR_EXPECTED["specific_directed_rhea_id"])
    specific_ids = set(
        item.strip()
        for item in specific["row"].get("ChEBI identifier", "").split(";")
        if item.strip()
    )
    expected_exact = {p["chebi_id"] for p in QDPR_EXPECTED["participants"]}
    missing = sorted(expected_exact - specific_ids)
    return {
        "schema": "dashi.rhea-chebi-bh4.v1",
        "acquired_at_utc": datetime.now(timezone.utc).isoformat(),
        "rhea_release_reference": "Rhea release 142 (2026-09-02); SPARQL release 2026_03",
        "reaction": QDPR_EXPECTED,
        "generic": generic,
        "directed": directed,
        "specific": specific,
        "specific_chebi_expected": sorted(expected_exact),
        "specific_chebi_missing_from_rest_row": missing,
        "specific_chebi_fixture_paid": not missing,
        "promotion_boundary": promotion_boundary(),
    }


def promotion_boundary() -> dict:
    return {
        "reaction_identity_creates_kinetics": False,
        "chemical_balance_creates_measured_flux": False,
        "reaction_identity_creates_allocator_competition": False,
        "reaction_identity_creates_disease_mechanism": False,
    }


def extract_panel_rhea(panel: dict) -> list[dict]:
    links: list[dict] = []
    for member in panel.get("members", []):
        cert = member.get("certificate", {})
        for xref in cert.get("cross_references", []):
            if xref.get("database") != "Rhea":
                continue
            rid = str(xref.get("id", "")).strip()
            if rid and not rid.startswith("RHEA:"):
                rid = f"RHEA:{rid}"
            if rid:
                links.append({"symbol": member.get("symbol"), "accession": member.get("accession"), "rhea_id": rid})
    return links


def acquire_panel(panel_path: Path) -> tuple[dict, int]:
    panel = json.loads(panel_path.read_text(encoding="utf-8"))
    links = extract_panel_rhea(panel)
    unique_ids = sorted({link["rhea_id"] for link in links})
    reactions: list[dict] = []
    errors: list[dict] = []
    for rid in unique_ids:
        try:
            reactions.append({"rhea_id": rid, **fetch_rhea_row(rid)})
        except Exception as exc:  # keep partial acquisition explicit
            errors.append({"rhea_id": rid, "error": str(exc)})
    return {
        "schema": "dashi.rhea-chebi-bh4-panel.v1",
        "acquired_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_uniprot_panel": str(panel_path),
        "protein_reaction_links": links,
        "unique_rhea_ids_requested": len(unique_ids),
        "rhea_rows_acquired": len(reactions),
        "rhea_rows_failed": len(errors),
        "complete_reaction_identity_acquisition": not errors,
        "reactions": reactions,
        "errors": errors,
        "qdpr_specific_fixture": QDPR_EXPECTED,
        "promotion_boundary": promotion_boundary(),
    }, (0 if not errors else 3)


def render(payload: dict, output: Path | None) -> None:
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--qdpr", action="store_true", help="acquire the QDPR Rhea/ChEBI witness")
    mode.add_argument("--from-uniprot-panel", type=Path, metavar="PATH", help="acquire all Rhea xrefs found in the exact UniProt panel certificate")
    parser.add_argument("-o", "--output", type=Path)
    args = parser.parse_args()
    if args.qdpr:
        payload = acquire_qdpr()
        render(payload, args.output)
        return 0 if payload["specific_chebi_fixture_paid"] else 3
    payload, code = acquire_panel(args.from_uniprot_panel)
    render(payload, args.output)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
