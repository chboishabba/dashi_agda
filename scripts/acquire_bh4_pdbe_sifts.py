#!/usr/bin/env python3
"""Acquire bounded PDBe/SIFTS structure-mapping receipts for the BH4 panel.

PDB identifiers are inherited from the exact UniProt panel. For a bounded number
of structures per protein, the script fetches PDBe updated mmCIF files and
extracts `_pdbx_sifts_unp_segments` rows, which map PDB segments to UniProt.
A mapping is structural provenance only; it does not create catalytic-site or
functional-mechanism evidence.

The output carries machine-computed coverage totals so later formal promotion
does not rely on hand-summed console diagnostics.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shlex
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

PDBe_UPDATED_CIF = "https://www.ebi.ac.uk/pdbe/entry-files/download/{pdb}_updated.cif"
USER_AGENT = "DASHI-BH4-PDBe-SIFTS/1.1 (https://github.com/chboishabba/dashi_agda)"


def get(url: str) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "text/plain,*/*"})
    with urllib.request.urlopen(req, timeout=90) as response:
        return response.read()


def pdb_ids(member: dict) -> list[str]:
    cert = member.get("certificate", {})
    ids = []
    for xref in cert.get("cross_references", []):
        if xref.get("database") == "PDB" and xref.get("id"):
            ids.append(str(xref["id"]).lower())
    return sorted(set(ids))


def extract_sifts_segments(text: str, accession: str) -> list[dict]:
    lines = text.splitlines()
    out: list[dict] = []
    i = 0
    prefix = "_pdbx_sifts_unp_segments."
    while i < len(lines):
        if lines[i].strip() != "loop_":
            i += 1
            continue
        i += 1
        headers = []
        while i < len(lines) and lines[i].strip().startswith("_"):
            headers.append(lines[i].strip())
            i += 1
        if not headers or not all(h.startswith(prefix) for h in headers):
            continue
        short = [h[len(prefix):] for h in headers]
        while i < len(lines):
            raw = lines[i].strip()
            if not raw or raw == "#" or raw == "loop_" or raw.startswith("_"):
                break
            values = shlex.split(raw, posix=True)
            if len(values) == len(headers):
                row = dict(zip(short, values))
                if accession in values or accession in raw:
                    out.append(row)
            i += 1
    return out


def summarize(results: list[dict], errors: list[dict]) -> dict:
    structures_examined = sum(len(row.get("structures", [])) for row in results)
    segment_count = sum(
        int(structure.get("matching_segment_count", 0))
        for row in results
        for structure in row.get("structures", [])
    )
    with_pdb = [row for row in results if row.get("uniprot_pdb_ids")]
    without_pdb = [row for row in results if not row.get("uniprot_pdb_ids")]
    with_segments = [
        row for row in results
        if any(int(s.get("matching_segment_count", 0)) > 0 for s in row.get("structures", []))
    ]
    without_segments = [row for row in results if row not in with_segments]
    return {
        "proteins_requested": len(results),
        "proteins_with_uniprot_pdb_links": len(with_pdb),
        "proteins_without_uniprot_pdb_links": len(without_pdb),
        "proteins_without_uniprot_pdb_link_ids": [
            {"symbol": row.get("symbol"), "accession": row.get("accession")}
            for row in without_pdb
        ],
        "proteins_with_matching_sifts_segments": len(with_segments),
        "proteins_without_matching_sifts_segments": len(without_segments),
        "structures_examined": structures_examined,
        "matching_sifts_segment_count": segment_count,
        "error_count": len(errors),
    }


def acquire(panel_path: Path, max_pdb_per_protein: int) -> tuple[dict, int]:
    panel = json.loads(panel_path.read_text(encoding="utf-8"))
    results, errors = [], []
    for member in panel.get("members", []):
        accession = str(member.get("accession", "")).strip()
        symbol = member.get("symbol")
        structures = pdb_ids(member)
        selected = structures if max_pdb_per_protein < 0 else structures[:max_pdb_per_protein]
        mappings = []
        for pdb in selected:
            url = PDBe_UPDATED_CIF.format(pdb=pdb)
            try:
                raw = get(url)
                text = raw.decode("utf-8", errors="replace")
                segments = extract_sifts_segments(text, accession)
                mappings.append({
                    "pdb_id": pdb.upper(),
                    "url": url,
                    "raw_sha256": hashlib.sha256(raw).hexdigest(),
                    "has_pdbx_sifts_unp_segments": "_pdbx_sifts_unp_segments." in text,
                    "matching_uniprot_segments": segments,
                    "matching_segment_count": len(segments),
                })
            except Exception as exc:
                errors.append({"symbol": symbol, "accession": accession, "pdb_id": pdb.upper(), "error": str(exc)})
        results.append({
            "symbol": symbol,
            "accession": accession,
            "uniprot_pdb_ids": [p.upper() for p in structures],
            "pdb_ids_examined": [p.upper() for p in selected],
            "structures": mappings,
            "matching_segment_count": sum(m.get("matching_segment_count", 0) for m in mappings),
        })
    summary = summarize(results, errors)
    return {
        "schema": "dashi.bh4-pdbe-sifts.v2",
        "acquired_at_utc": datetime.now(timezone.utc).isoformat(),
        "source": "PDBe updated PDBx/mmCIF with SIFTS _pdbx_sifts_unp_segments",
        "source_panel": str(panel_path),
        "max_pdb_per_protein": max_pdb_per_protein,
        "summary": summary,
        "results": results,
        "errors": errors,
        "promotion_boundary": {
            "structure_mapping_creates_catalytic_mechanism": False,
            "residue_mapping_creates_functional_perturbation": False,
            "pdb_coverage_creates_same_object_cell_state": False,
            "structure_mapping_creates_disease_mechanism": False,
        },
        "source_coordinates": {
            "SIFTS": "_pdbx_sifts_unp_segments",
            "uniprot_pdb": "UniProt PDB cross-references from exact panel",
            "pdb_chain_uniprot": "SIFTS mapping semantics represented in updated mmCIF",
        },
    }, (0 if not errors else 3)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--panel", type=Path, required=True)
    parser.add_argument("--max-pdb-per-protein", type=int, default=3, help="-1 means all UniProt-linked PDB entries")
    parser.add_argument("-o", "--output", type=Path)
    args = parser.parse_args()
    payload, code = acquire(args.panel, args.max_pdb_per_protein)
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
