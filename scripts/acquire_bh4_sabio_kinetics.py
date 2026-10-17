#!/usr/bin/env python3
"""Acquire bounded SABIO-RK kinetic-law candidates for the BH4 protein panel.

Primary 2026 API:
  https://sabio.h-its.org/export-api/sabio/kinlaw-entry/json

The current browser frontend no longer serves the historical
`/sabioRestWebServices/*` payloads. The export API returns a JSON envelope with
`meta` and `data`; this acquirer validates that envelope, follows pagination,
and preserves the raw entry objects plus byte-level response hashes.

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
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

EXPORT_URL = "https://sabio.h-its.org/export-api/sabio/kinlaw-entry/json"
USER_AGENT = "DASHI-BH4-SABIO/1.2 (https://github.com/chboishabba/dashi_agda)"
PUBMED_RE = re.compile(r"(?:pubmed[^0-9]{0,24}|pmid[^0-9]{0,8})([0-9]{5,9})", re.I)


def get_json(url: str) -> tuple[dict, dict]:
    req = urllib.request.Request(
        url,
        headers={"User-Agent": USER_AGENT, "Accept": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=90) as response:
        raw = response.read()
        content_type = response.headers.get("Content-Type")
        final_url = response.geturl()
        status = int(response.status)
    head = raw[:4096].decode("utf-8", errors="ignore").lower()
    if "<html" in head or '<div id="shell"' in head or "<!doctype html" in head:
        raise RuntimeError(f"SABIO export API returned HTML payload: {final_url}")
    try:
        payload = json.loads(raw.decode("utf-8"))
    except Exception as exc:
        raise RuntimeError(f"SABIO export API returned non-JSON payload: {final_url}: {exc}") from exc
    if not isinstance(payload, dict) or not isinstance(payload.get("meta"), dict) or not isinstance(payload.get("data"), list):
        raise RuntimeError(
            "SABIO export API response does not match required export-envelope {meta: object, data: array}"
        )
    return payload, {
        "status": status,
        "content_type": content_type,
        "final_url": final_url,
        "raw_sha256": hashlib.sha256(raw).hexdigest(),
        "raw_byte_count": len(raw),
    }


def panel_members(panel: dict) -> list[dict]:
    rows = []
    for member in panel.get("members", []):
        accession = str(member.get("accession", "")).strip()
        if accession:
            rows.append({"symbol": member.get("symbol"), "accession": accession})
    return rows


def meta_int(meta: dict, *keys: str) -> int | None:
    for key in keys:
        value = meta.get(key)
        try:
            if value is not None:
                return int(value)
        except (TypeError, ValueError):
            pass
    return None


def extract_pubmed_ids(value: Any) -> list[str]:
    text = json.dumps(value, sort_keys=True, ensure_ascii=False)
    return sorted(set(PUBMED_RE.findall(text)))


def count_parameter_objects(value: Any) -> int:
    """Conservatively count explicit parameter-like objects without schema invention."""
    count = 0
    if isinstance(value, dict):
        lower_keys = {str(k).lower() for k in value}
        looks_parameter = (
            bool(lower_keys & {"parameter", "parametername", "parameter_name", "parametertype", "parameter_type"})
            and bool(lower_keys & {"value", "startvalue", "endvalue", "lower", "upper"})
        )
        if looks_parameter:
            count += 1
        for child in value.values():
            count += count_parameter_objects(child)
    elif isinstance(value, list):
        for child in value:
            count += count_parameter_objects(child)
    return count


def entry_identifier(entry: Any) -> str | None:
    if not isinstance(entry, dict):
        return None
    for key in ("kinlaw_id", "kinlawId", "kinLawID", "entry_id", "entryId", "id"):
        if entry.get(key) is not None:
            return str(entry[key])
    return None


def export_query(accession: str, page_size: int = 1000) -> tuple[list[Any], list[dict], dict]:
    query = f'UniProtKB_AC:"{accession}"'
    page = 1
    rows: list[Any] = []
    responses: list[dict] = []
    first_meta: dict | None = None
    expected_total: int | None = None

    while True:
        params = urllib.parse.urlencode({"q": query, "page": page, "pageSize": page_size})
        payload, receipt = get_json(f"{EXPORT_URL}?{params}")
        meta = payload["meta"]
        data = payload["data"]
        if first_meta is None:
            first_meta = dict(meta)
            expected_total = meta_int(meta, "total_count", "totalCount", "total")
        responses.append({"page": page, "row_count": len(data), **receipt})
        rows.extend(data)

        total_pages = meta_int(meta, "total_pages", "totalPages", "pages")
        if total_pages is not None:
            if page >= total_pages:
                break
        elif expected_total is not None:
            if len(rows) >= expected_total:
                break
        elif len(data) < page_size:
            break
        else:
            raise RuntimeError("SABIO export envelope lacks a usable pagination terminator")
        page += 1
        if page > 1000:
            raise RuntimeError("SABIO export pagination exceeded 1000 pages")

    if expected_total is not None and len(rows) != expected_total:
        raise RuntimeError(
            f"SABIO export envelope row mismatch: total_count={expected_total}, acquired={len(rows)}"
        )
    return rows, responses, first_meta or {}


def acquire_member(symbol: str | None, accession: str) -> dict:
    rows, responses, meta = export_query(accession)
    entry_ids = [x for x in (entry_identifier(row) for row in rows) if x is not None]
    return {
        "symbol": symbol,
        "accession": accession,
        "query": f'UniProtKB_AC:"{accession}"',
        "acquisition_mode": "export-envelope",
        "entry_count": len(rows),
        "entry_ids": entry_ids,
        "kinetic_parameter_object_count": sum(count_parameter_objects(row) for row in rows),
        "pubmed_ids": extract_pubmed_ids(rows),
        "export_meta": meta,
        "response_receipts": responses,
        "entry_top_level_keys": sorted({str(k) for row in rows if isinstance(row, dict) for k in row}),
        "entries": rows,
        "status": "acquired" if rows else "no-entries",
    }


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
    return {
        "schema": "dashi.bh4-sabio-kinetics.v3",
        "acquired_at_utc": datetime.now(timezone.utc).isoformat(),
        "source": "SABIO-RK kinetic-law export API",
        "export_api": EXPORT_URL,
        "source_panel": str(panel_path),
        "query_field": "UniProtKB_AC",
        "proteins_requested": len(members),
        "proteins_completed": len(results),
        "proteins_with_entries": len(with_entries),
        "kinetic_entry_count": sum(row["entry_count"] for row in results),
        "kinetic_parameter_count": sum(row["kinetic_parameter_object_count"] for row in results),
        "results": results,
        "errors": errors,
        "promotion_boundary": {
            "legacy_rest_spa_means_zero_entries": False,
            "export_envelope_identity_creates_flux_bounds": False,
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
