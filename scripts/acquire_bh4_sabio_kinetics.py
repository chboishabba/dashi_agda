#!/usr/bin/env python3
"""Acquire bounded SABIO-RK kinetic-law candidates for the BH4 protein panel.

The output is evidence discovery, not a flux-bound manifest. SABIO kinetic
constants may be in vitro, condition-specific, mutant-specific, or otherwise
non-transferable to the joint in-vivo BH4 state. Nothing here sets a
REACTION_FLUX bound automatically.

SABIO's documented web-service surface supports both GET and POST.  In 2026 an
HTTP-200 response can nevertheless be the browser SPA shell rather than the
requested plain-text/XML payload.  This acquirer therefore treats HTML as a
protocol failure, retries entry-ID search with POST, and finally falls back to
the documented direct SBML search.  HTML is never interpreted as "zero data".
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
USER_AGENT = "DASHI-BH4-SABIO/1.1 (https://github.com/chboishabba/dashi_agda)"
PUBMED_RE = re.compile(r"pubmed(?:\.ncbi\.nlm\.nih\.gov/|/)(\d+)", re.I)


def request(url: str, *, data: bytes | None = None, accept: str = "*/*") -> tuple[bytes, dict]:
    headers = {"User-Agent": USER_AGENT, "Accept": accept}
    if data is not None:
        headers["Content-Type"] = "application/x-www-form-urlencoded"
    req = urllib.request.Request(url, data=data, headers=headers, method="POST" if data is not None else "GET")
    with urllib.request.urlopen(req, timeout=90) as response:
        raw = response.read()
        return raw, {
            "status": int(response.status),
            "content_type": response.headers.get("Content-Type"),
            "final_url": response.geturl(),
            "raw_sha256": hashlib.sha256(raw).hexdigest(),
        }


def looks_like_html(raw: bytes) -> bool:
    head = raw[:8192].decode("utf-8", errors="ignore").lower()
    return (
        "<!doctype html" in head
        or "<html" in head
        or '<div id="shell"' in head
        or "<div id='shell'" in head
    )


def looks_like_xml(raw: bytes) -> bool:
    head = raw.lstrip()[:512].decode("utf-8", errors="ignore").lower()
    return head.startswith("<?xml") or "<sbml" in head


def panel_members(panel: dict) -> list[dict]:
    rows = []
    for member in panel.get("members", []):
        accession = str(member.get("accession", "")).strip()
        if accession:
            rows.append({"symbol": member.get("symbol"), "accession": accession})
    return rows


def parse_entry_ids(raw: bytes) -> list[int]:
    text = raw.decode("utf-8", errors="replace").strip()
    ids = []
    for line in text.splitlines():
        line = line.strip()
        if line.isdigit():
            ids.append(int(line))
    return sorted(set(ids))


def entry_ids(accession: str) -> tuple[list[int] | None, list[dict]]:
    """Return IDs, or None when the entry-ID endpoint never produced data format."""
    q = f'UniProtKB_AC:"{accession}"'
    encoded = urllib.parse.urlencode({"format": "txt", "q": q})
    diagnostics: list[dict] = []

    # POST first: SABIO documents both GET and POST, and POST avoids the current
    # SPA rewrite observed for some GET entry-ID requests.
    raw, meta = request(
        f"{BASE}/searchKineticLaws/entryIDs",
        data=encoded.encode("utf-8"),
        accept="text/plain,application/xml;q=0.9,*/*;q=0.1",
    )
    diagnostics.append({"method": "POST", **meta, "html_shell": looks_like_html(raw)})
    if not looks_like_html(raw):
        return parse_entry_ids(raw), diagnostics

    raw, meta = request(
        f"{BASE}/searchKineticLaws/entryIDs?{encoded}",
        accept="text/plain,application/xml;q=0.9,*/*;q=0.1",
    )
    diagnostics.append({"method": "GET", **meta, "html_shell": looks_like_html(raw)})
    if not looks_like_html(raw):
        return parse_entry_ids(raw), diagnostics

    return None, diagnostics


def kinetic_sbml(ids: list[int]) -> tuple[bytes, dict]:
    params = urllib.parse.urlencode({
        "kinlawids": ",".join(str(x) for x in ids),
        "normalized": "true",
        "annotation": "miriam",
    })
    raw, meta = request(f"{BASE}/kineticLaws?{params}", accept="application/xml,text/xml,*/*;q=0.1")
    if looks_like_html(raw) or not looks_like_xml(raw):
        raise RuntimeError("SABIO kineticLaws returned non-SBML payload")
    return raw, meta


def direct_search_sbml(accession: str) -> tuple[bytes, dict]:
    q = f'UniProtKB_AC:"{accession}"'
    encoded = urllib.parse.urlencode({"q": q, "normalized": "true", "annotation": "miriam"})

    raw, meta = request(
        f"{BASE}/searchKineticLaws/sbml",
        data=encoded.encode("utf-8"),
        accept="application/xml,text/xml,*/*;q=0.1",
    )
    meta = {"method": "POST", **meta, "html_shell": looks_like_html(raw)}
    if not looks_like_html(raw) and looks_like_xml(raw):
        return raw, meta

    raw, meta2 = request(
        f"{BASE}/searchKineticLaws/sbml?{encoded}",
        accept="application/xml,text/xml,*/*;q=0.1",
    )
    meta2 = {"method": "GET", **meta2, "html_shell": looks_like_html(raw)}
    if looks_like_html(raw) or not looks_like_xml(raw):
        raise RuntimeError(
            "SABIO entry-ID and direct-SBML endpoints returned browser/non-SBML payloads; "
            f"POST diagnostic={meta}; GET diagnostic={meta2}"
        )
    return raw, meta2


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


def count_kinetic_laws(raw: bytes) -> int:
    root = ET.fromstring(raw)
    return sum(1 for element in root.iter() if element.tag.rsplit("}", 1)[-1] == "kineticLaw")


def parse_pubmed(raw: bytes) -> list[str]:
    text = raw.decode("utf-8", errors="replace")
    return sorted(set(PUBMED_RE.findall(text)))


def acquire_member(symbol: str | None, accession: str) -> dict:
    ids, search_diagnostics = entry_ids(accession)
    row = {
        "symbol": symbol,
        "accession": accession,
        "query": f'UniProtKB_AC:"{accession}"',
        "entry_ids": ids or [],
        "entry_count": 0,
        "parameters": [],
        "pubmed_ids": [],
        "sbml_raw_sha256": None,
        "search_diagnostics": search_diagnostics,
        "acquisition_mode": None,
        "status": None,
    }

    if ids is not None:
        if not ids:
            row["acquisition_mode"] = "entry-ids"
            row["status"] = "no-entries"
            return row
        raw, sbml_meta = kinetic_sbml(ids)
        row["entry_count"] = len(ids)
        row["acquisition_mode"] = "entry-ids+kineticLaws"
        row["sbml_response"] = sbml_meta
    else:
        # Crucially, SPA HTML is not evidence of zero SABIO records.
        raw, sbml_meta = direct_search_sbml(accession)
        row["entry_count"] = count_kinetic_laws(raw)
        row["acquisition_mode"] = "direct-search-sbml"
        row["sbml_response"] = sbml_meta

    row["sbml_raw_sha256"] = hashlib.sha256(raw).hexdigest()
    row["parameters"] = parse_parameters(raw)
    row["pubmed_ids"] = parse_pubmed(raw)
    row["status"] = "acquired" if row["entry_count"] else "no-entries"
    return row


def acquire(panel_path: Path) -> tuple[dict, int]:
    panel = json.loads(panel_path.read_text(encoding="utf-8"))
    results, errors = [], []
    members = panel_members(panel)
    for member in members:
        try:
            results.append(acquire_member(member["symbol"], member["accession"]))
        except Exception as exc:
            errors.append({**member, "error": str(exc)})
    with_entries = [row for row in results if row["entry_count"]]
    html_shell_observed = any(
        any(d.get("html_shell") for d in row.get("search_diagnostics", []))
        for row in results
    )
    return {
        "schema": "dashi.bh4-sabio-kinetics.v2",
        "acquired_at_utc": datetime.now(timezone.utc).isoformat(),
        "source": "SABIO-RK REST web services",
        "source_panel": str(panel_path),
        "query_field": "UniProtKB_AC",
        "proteins_requested": len(members),
        "proteins_completed": len(results),
        "proteins_with_entries": len(with_entries),
        "kinetic_entry_count": sum(row["entry_count"] for row in results),
        "kinetic_parameter_count": sum(len(row["parameters"]) for row in results),
        "html_shell_observed": html_shell_observed,
        "results": results,
        "errors": errors,
        "promotion_boundary": {
            "html_shell_means_zero_entries": False,
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
