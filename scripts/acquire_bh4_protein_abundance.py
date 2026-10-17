#!/usr/bin/env python3
"""Acquire exact-UniProt human protein abundance context from ProteomicsDB.

This is an evidence-acquisition lane, not a flux converter. ProteomicsDB
NORMALIZED_INTENSITY/iBAQ values are retained with tissue/sample provenance but
never promoted to molar enzyme concentration without an independently paid
mass/volume calibration and same-state tissue/compartment bridge.
"""
from __future__ import annotations

import argparse, hashlib, json, urllib.error, urllib.parse, urllib.request
from datetime import datetime, timezone
from pathlib import Path

BASE = "https://www.proteomicsdb.org/proteomicsdb/logic/api/proteinexpression.xsodata"
USER_AGENT = "DASHI-BH4-abundance/1.0"


def members(panel: dict) -> list[dict]:
    out = []
    for m in panel.get("members", []):
        cert = m.get("certificate") or {}
        acc = m.get("accession") or cert.get("primary_accession")
        if acc:
            out.append({"symbol": m.get("symbol"), "accession": acc, "mol_weight": (cert.get("sequence") or {}).get("mol_weight")})
    return out


def endpoint(accession: str, ms_level: int) -> str:
    params = (
        f"InputParams(PROTEINFILTER='{accession}',MS_LEVEL={ms_level},"
        "TISSUE_ID_SELECTION='',TISSUE_CATEGORY_SELECTION='tissue;fluid;cell line',"
        "SCOPE_SELECTION=1,GROUP_BY_TISSUE=1,CALCULATION_METHOD=0,EXP_ID=-1)/Results"
    )
    select = "UNIQUE_IDENTIFIER,TISSUE_ID,TISSUE_NAME,TISSUE_SAP_SYNONYM,SAMPLE_ID,SAMPLE_NAME,EXPERIMENT_ID,EXPERIMENT_NAME,PROJECT_ID,PROJECT_NAME,NORMALIZED_INTENSITY,MIN_NORMALIZED_INTENSITY,MAX_NORMALIZED_INTENSITY,SAMPLES"
    return f"{BASE}/{params}?$select={urllib.parse.quote(select, safe=',')}&$format=json"


def fetch_json(url: str) -> tuple[dict, str]:
    req = urllib.request.Request(url, headers={"Accept":"application/json","User-Agent":USER_AGENT})
    with urllib.request.urlopen(req, timeout=45) as resp:
        raw = resp.read()
    return json.loads(raw), hashlib.sha256(raw).hexdigest()


def rows(payload: dict) -> list[dict]:
    if isinstance(payload.get("d"), dict):
        return list(payload["d"].get("results") or [])
    return list(payload.get("results") or payload.get("value") or [])


def acquire(panel: dict) -> dict:
    results, errors = [], []
    for m in members(panel):
        observed = []
        for ms in (1, 2):
            url = endpoint(m["accession"], ms)
            try:
                payload, digest = fetch_json(url)
                for r in rows(payload):
                    observed.append({
                        "ms_level": ms,
                        "request": url,
                        "raw_sha256": digest,
                        "tissue_id": r.get("TISSUE_ID"),
                        "tissue_name": r.get("TISSUE_NAME"),
                        "tissue_synonym": r.get("TISSUE_SAP_SYNONYM"),
                        "sample_id": r.get("SAMPLE_ID"),
                        "sample_name": r.get("SAMPLE_NAME"),
                        "experiment_id": r.get("EXPERIMENT_ID"),
                        "experiment_name": r.get("EXPERIMENT_NAME"),
                        "project_id": r.get("PROJECT_ID"),
                        "project_name": r.get("PROJECT_NAME"),
                        "normalized_intensity": r.get("NORMALIZED_INTENSITY"),
                        "min_normalized_intensity": r.get("MIN_NORMALIZED_INTENSITY"),
                        "max_normalized_intensity": r.get("MAX_NORMALIZED_INTENSITY"),
                        "sample_count": r.get("SAMPLES"),
                        "abundance_candidate_creates_enzyme_concentration": False,
                        "same_tissue_required": True,
                    })
            except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, json.JSONDecodeError) as exc:
                errors.append({"symbol":m["symbol"],"accession":m["accession"],"ms_level":ms,"error":str(exc)})
        results.append({**m, "observations": observed, "observation_count": len(observed)})
    return {
        "schema":"dashi.bh4-protein-abundance-context.v1",
        "source":"ProteomicsDB proteinexpression.xsodata; exact UniProt accession; iBAQ grouped by tissue",
        "acquired_at_utc":datetime.now(timezone.utc).isoformat(),
        "proteins_requested":len(results),
        "proteins_with_observations":sum(bool(r["observations"]) for r in results),
        "observation_count":sum(r["observation_count"] for r in results),
        "results":results,
        "errors":errors,
        "promotion_boundary":{
            "abundance_candidate_creates_enzyme_concentration":False,
            "normalized_intensity_creates_molar_abundance":False,
            "same_tissue_required":True,
            "same_compartment_time_required":True,
            "protein_abundance_creates_reaction_flux":False,
        },
    }


def main() -> int:
    p=argparse.ArgumentParser(); p.add_argument("--panel",type=Path,required=True); p.add_argument("-o","--output",type=Path,required=True); a=p.parse_args()
    out=acquire(json.loads(a.panel.read_text(encoding="utf-8")))
    a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({k:out[k] for k in ("schema","proteins_requested","proteins_with_observations","observation_count")},indent=2))
    return 0 if not out["errors"] else 2

if __name__ == "__main__": raise SystemExit(main())
