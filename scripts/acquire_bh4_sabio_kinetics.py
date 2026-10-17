#!/usr/bin/env python3
"""Acquire bounded SABIO-RK kinetic-law candidates for the BH4 protein panel.

The output is evidence discovery, not a flux-bound manifest. SABIO kinetic
constants may be in vitro, condition-specific, mutant-specific, or otherwise
non-transferable to the joint in-vivo BH4 state. Nothing here sets a
REACTION_FLUX bound automatically.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timezone
from pathlib import Path

BASE = "https://sabiork.h-its.org/sabioRestWebServices"
USER_AGENT = "DASHI-BH4-SABIO/1.0 (https://github.com/chboishabba/dashi_agda)"
PUBMED_RE = re.compile(r"pubmed(?:\.ncbi\.nlm\.nih\.gov/|/)(\d+)", re.I)


def get(url: str) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "*/*"})
    with urllib.request.urlopen(req, timeout=90) as response:
        return response.read()


def panel_members(panel: dict) -> list[dict]:
    rows = []
    for member in panel.get("members", []):
        accession = str(member.get("accession", "")).strip()
        if accession:
            rows.append({"symbol": member.get("symbol"), "accession": accession})
    return rows


def entry_ids(accession: str) -> tuple[list[int], str]:
    q = f'UniProtKB_AC:"{accession}"'
    params = urllib.parse.urlencode({"format": "txt", "q": q})
    raw = get(f"{BASE}/searchKineticLaws/entryIDs?{params}")
    text = raw.decode("utf-8", errors="replace").strip()
    ids = []
    for line in text.splitlines():
        line = line.strip()
        if line.isdigit():
            ids.append(int(line))
    return sorted(set(ids)), hashlib.sha256(raw).hexdigest()


def kinetic_sbml(ids: list[int]) -> tuple[bytes, str]:
    params = urllib.parse.urlencode({
        "kinlawids": ",".join(str(x) for x in ids),
        "normalized": "true",
        "annotation": "miriam",
    })
    raw = get(f"{BASE}/kineticLaws?{params}")
    return raw, hashlib.sha256(raw).hexdigest()


def parse_parameters(raw: bytes) -> list[dict]:
    root = ET.fromstring(raw)
    out: list[dict] = []
    for element in root.iter():
        local = element.tag.rsplit("}", 1)[-1]
        if local not in {"parameter", "localParameter"}:
            continue
        if "value" not in element.attrib:
            continue
        out.append({
            "id": element.attrib.get("id"),
            "name": element.attrib.get("name"),
            "value": element.attrib.get("value"),
            "units": element.attrib.get("units"),
            "constant": element.attrib.get("constant"),
        })
    return out


def parse_pubmed(raw: bytes) -> list[str]:
    text = raw.decode("utf-8", errors="replace")
    return sorted(set(PUBMED_RE.findall(text)))


def acquire_member(symbol: str | None, accession: str) -> dict:
    ids, search_sha = entry_ids(accession)
    row = {
        "symbol": symbol,
        "accession": accession,
        "query": f'UniProtKB_AC:"{accession}"',
        "entry_ids": ids,
        "entry_id_search_raw_sha256": search_sha,
        "entry_count": len(ids),
        "parameters": [],
        "pubmed_ids": [],
        "sbml_raw_sha256": None,
        "status": "no-entries" if not ids else "acquired",
    }
    if ids:
        raw, sha = kinetic_sbml(ids)
        row["sbml_raw_sha256"] = sha
        row["parameters"] = parse_parameters(raw)
        row["pubmed_ids"] = parse_pubmed(raw)
    return row


def acquire(panel_path: Path) -> tuple[dict, int]:
    panel = json.loads(panel_path.read_text(encoding="utf-8"))
    results, errors = [], []
    for member in panel_members(panel):
        try:
            results.append(acquire_member(member["symbol"], member["accession"]))
        except Exception as exc:
            errors.append({**member, "error": str(exc)})
    with_entries = [row for row in results if row["entry_count"]]
    return {
        "schema": "dashi.bh4-sabio-kinetics.v1",
        "acquired_at_utc": datetime.now(timezone.utc).isoformat(),
        "source": "SABIO-RK REST web services",
        "source_panel": str(panel_path),
        "query_field": "UniProtKB_AC",
        "proteins_requested": len(panel_members(panel)),
        "proteins_with_entries": len(with_entries),
        "kinetic_entry_count": sum(row["entry_count"] for row in results),
        "results": results,
        "errors": errors,
        "promotion_boundary": {
            "kinetic_parameters_create_flux_bounds": False,
            "in_vitro_parameters_create_in_vivo_state": False,
            "cross_condition_parameters_create_same_object_state": False,
            "sabio_entry_creates_disease_mechanism": False,
        },
    }, (0 if not errors else 3)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--panel", type=Path, required=True, help="exact UniProt BH4 panel certificate")
    parser.add_argument("-o", "--output", type=Path)
    args = parser.parse_args()
    payload, code = acquire(args.panel)
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
