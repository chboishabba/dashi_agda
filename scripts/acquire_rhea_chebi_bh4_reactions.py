#!/usr/bin/env python3
"""Acquire bounded Rhea/ChEBI reaction certificates for the BH4 lane.

This script is deliberately reaction-identity/stoichiometry facing. It does not
infer kinetics, cellular flux, compartment state, allocator competition or
disease mechanism.

The REST table pins the public row/equation and raw response. Rhea SPARQL pins
reaction sides, participant coefficients and the Rhea compound formula/charge
coordinates used for chemical balancing. Panel membership comes only from the
already-acquired UniProt certificate.

Public Rhea endpoints occasionally time out under batch acquisition. Network
reads therefore use a bounded three-attempt exponential-backoff retry. Exhausted
retries remain explicit acquisition errors; they never become missing chemistry.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import sys
import time
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

RHEA_TABLE = "https://www.rhea-db.org/rhea/"
RHEA_SPARQL = "https://sparql.rhea-db.org/sparql"
USER_AGENT = "DASHI-rhea-chebi-acquisition/1.2 (https://github.com/chboishabba/dashi_agda)"
NETWORK_ATTEMPTS = 3
NETWORK_BACKOFF_SECONDS = 1.0

QDPR_EXPECTED = {
    "generic_rhea_id": "RHEA:17869",
    "directed_rhea_id": "RHEA:17871",
    "specific_directed_rhea_id": "RHEA:32253",
    "participants": [
        {"side": "substrate", "coefficient": 1, "chebi_id": "CHEBI:43120", "broader_chebi_id": "CHEBI:20680", "name": "(6R)-L-erythro-6,7-dihydrobiopterin", "formula": "C9H13N5O3", "charge": 0},
        {"side": "substrate", "coefficient": 1, "chebi_id": "CHEBI:57945", "broader_chebi_id": "CHEBI:57945", "name": "NADH", "formula": "C21H27N7O14P2", "charge": -2},
        {"side": "substrate", "coefficient": 1, "chebi_id": "CHEBI:15378", "broader_chebi_id": "CHEBI:15378", "name": "H+", "formula": "H", "charge": 1},
        {"side": "product", "coefficient": 1, "chebi_id": "CHEBI:59560", "broader_chebi_id": "CHEBI:15372", "name": "(6R)-L-erythro-5,6,7,8-tetrahydrobiopterin", "formula": "C9H15N5O3", "charge": 0},
        {"side": "product", "coefficient": 1, "chebi_id": "CHEBI:57540", "broader_chebi_id": "CHEBI:57540", "name": "NAD+", "formula": "C21H26N7O14P2", "charge": -1},
    ],
}


def _retry(operation, label: str):
    last_exc: Exception | None = None
    for attempt in range(1, NETWORK_ATTEMPTS + 1):
        try:
            return operation()
        except Exception as exc:
            last_exc = exc
            if attempt >= NETWORK_ATTEMPTS:
                break
            time.sleep(NETWORK_BACKOFF_SECONDS * (2 ** (attempt - 1)))
    raise RuntimeError(f"{label} failed after {NETWORK_ATTEMPTS} attempts: {last_exc}") from last_exc


def _get(url: str) -> bytes:
    def operation() -> bytes:
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        with urllib.request.urlopen(request, timeout=60) as response:
            return response.read()
    return _retry(operation, f"Rhea GET {url}")


def _sparql(query: str) -> tuple[dict, str]:
    data = urllib.parse.urlencode({"query": query, "format": "json"}).encode("utf-8")

    def operation() -> bytes:
        request = urllib.request.Request(
            RHEA_SPARQL,
            data=data,
            headers={
                "User-Agent": USER_AGENT,
                "Accept": "application/sparql-results+json",
                "Content-Type": "application/x-www-form-urlencoded",
            },
        )
        with urllib.request.urlopen(request, timeout=60) as response:
            return response.read()

    raw = _retry(operation, "Rhea SPARQL POST")
    return json.loads(raw), hashlib.sha256(raw).hexdigest()


def _binding(row: dict, name: str) -> str | None:
    value = row.get(name, {}).get("value")
    return value if isinstance(value, str) else None


def _chebi_id(uri: str | None) -> str | None:
    if not uri:
        return None
    marker = "CHEBI_"
    if marker in uri:
        return "CHEBI:" + uri.rsplit(marker, 1)[1]
    return uri if uri.startswith("CHEBI:") else None


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


def fetch_rhea_participants(rhea_id: str) -> dict:
    numeric = rhea_id.replace("RHEA:", "")
    query = f"""
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
PREFIX rh: <http://rdf.rhea-db.org/>
SELECT ?side ?coefficient ?participant ?compound ?chebi ?name ?formula ?charge
WHERE {{
  BIND(rh:{numeric} AS ?root)
  {{
    SELECT ?root (MIN(?d) AS ?dir) WHERE {{
      OPTIONAL {{ ?root rh:directionalReaction ?d . }}
    }} GROUP BY ?root
  }}
  BIND(COALESCE(?dir, ?root) AS ?reaction)
  {{ ?reaction rh:substrates ?reactionSide . BIND("substrate" AS ?side) }}
  UNION
  {{ ?reaction rh:products ?reactionSide . BIND("product" AS ?side) }}
  ?contains rdfs:subPropertyOf rh:contains .
  ?contains rh:coefficient ?coefficient .
  ?reactionSide ?contains ?participant .
  ?participant rh:compound ?compound .
  OPTIONAL {{ ?compound rh:chebi ?chebi . }}
  OPTIONAL {{ ?compound rh:name ?name . }}
  OPTIONAL {{ ?compound rh:formula ?formula . }}
  OPTIONAL {{ ?compound rh:charge ?charge . }}
}}
ORDER BY ?side ?participant
"""
    payload, raw_sha = _sparql(query)
    participants: list[dict] = []
    for row in payload.get("results", {}).get("bindings", []):
        coefficient = _binding(row, "coefficient")
        charge = _binding(row, "charge")
        participants.append(
            {
                "side": _binding(row, "side"),
                "coefficient": coefficient,
                "participant_uri": _binding(row, "participant"),
                "compound_uri": _binding(row, "compound"),
                "chebi_id": _chebi_id(_binding(row, "chebi")),
                "name": _binding(row, "name"),
                "formula": _binding(row, "formula"),
                "charge": charge,
            }
        )
    formula_charge_ready = bool(participants) and all(
        p["side"] in {"substrate", "product"}
        and p["coefficient"] is not None
        and p["formula"] is not None
        and p["charge"] is not None
        for p in participants
    )
    return {
        "participants": participants,
        "participant_sparql_response_sha256": raw_sha,
        "formula_charge_ready": formula_charge_ready,
        "participant_query": "Rhea RDF: substrates/products + coefficient + compound formula/charge",
    }


def acquire_reaction(rhea_id: str) -> dict:
    return {"rhea_id": rhea_id, **fetch_rhea_row(rhea_id), **fetch_rhea_participants(rhea_id)}


def promotion_boundary() -> dict:
    return {
        "reaction_identity_creates_kinetics": False,
        "chemical_balance_creates_measured_flux": False,
        "reaction_identity_creates_allocator_competition": False,
        "reaction_identity_creates_disease_mechanism": False,
        "formula_charge_receipt_solves_electronic_structure": False,
        "network_retry_exhaustion_means_reaction_absent": False,
    }


def acquire_qdpr() -> dict:
    generic = acquire_reaction(QDPR_EXPECTED["generic_rhea_id"])
    directed = acquire_reaction(QDPR_EXPECTED["directed_rhea_id"])
    specific = acquire_reaction(QDPR_EXPECTED["specific_directed_rhea_id"])
    specific_ids = {p.get("chebi_id") for p in specific["participants"] if p.get("chebi_id")}
    expected_exact = {p["chebi_id"] for p in QDPR_EXPECTED["participants"]}
    missing = sorted(expected_exact - specific_ids)
    return {
        "schema": "dashi.rhea-chebi-bh4.v2",
        "acquired_at_utc": datetime.now(timezone.utc).isoformat(),
        "rhea_release_reference": "Rhea release 142 (2026-09-02); SPARQL release 2026_03",
        "reaction": QDPR_EXPECTED,
        "generic": generic,
        "directed": directed,
        "specific": specific,
        "specific_chebi_expected": sorted(expected_exact),
        "specific_chebi_missing_from_sparql": missing,
        "specific_chebi_fixture_paid": not missing and specific["formula_charge_ready"],
        "promotion_boundary": promotion_boundary(),
    }


def extract_panel_rhea(panel: dict) -> list[dict]:
    links: list[dict] = []
    for member in panel.get("members", []):
        cert = member.get("certificate", {})
        for xref in cert.get("cross_references", []):
            if xref.get("database") != "Rhea":
                continue
            rid = str(xref.get("id", "")).strip()
            if not rid or "COMP" in rid:
                continue
            if not rid.startswith("RHEA:"):
                rid = f"RHEA:{rid}"
            if rid.replace("RHEA:", "").isdigit():
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
            reactions.append(acquire_reaction(rid))
        except Exception as exc:
            errors.append({"rhea_id": rid, "error": str(exc)})
    formula_ready = sum(bool(row.get("formula_charge_ready")) for row in reactions)
    return {
        "schema": "dashi.rhea-chebi-bh4-panel.v2",
        "acquired_at_utc": datetime.now(timezone.utc).isoformat(),
        "rhea_release_reference": "Rhea release 142 (2026-09-02); SPARQL release 2026_03",
        "source_uniprot_panel": str(panel_path),
        "network_retry_policy": {"attempts": NETWORK_ATTEMPTS, "initial_backoff_seconds": NETWORK_BACKOFF_SECONDS, "exponential": True},
        "protein_reaction_links": links,
        "unique_rhea_ids_requested": len(unique_ids),
        "rhea_rows_acquired": len(reactions),
        "rhea_rows_failed": len(errors),
        "formula_charge_ready_reactions": formula_ready,
        "formula_charge_residual_reactions": len(reactions) - formula_ready,
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