#!/usr/bin/env python3
"""Acquire RefMet/human-study context for the 29 finite BH4 species.

Metabolomics Workbench can establish metabolite identity and human-study
occurrence/context. It does not by itself measure membrane exchange or transport
flux. Those remain separate payment obligations.
"""
from __future__ import annotations

import argparse, hashlib, json, urllib.error, urllib.parse, urllib.request
from datetime import datetime, timezone
from pathlib import Path

BASE = "https://www.metabolomicsworkbench.org/rest"
UA = "DASHI-BH4-exchange-context/1.0"


def fetch(url: str) -> tuple[object, str]:
    req=urllib.request.Request(url,headers={"Accept":"application/json","User-Agent":UA})
    with urllib.request.urlopen(req,timeout=45) as resp: raw=resp.read()
    return json.loads(raw), hashlib.sha256(raw).hexdigest()


def participant_metadata(rhea: dict) -> dict[str,dict]:
    out={}
    for rxn in rhea.get("reactions",[]):
        for p in rxn.get("participants",[]):
            key=str(p.get("chebi_id") or p.get("compound_uri") or p.get("name") or "")
            if key and key not in out:
                out[key]={"chebi_id":p.get("chebi_id"),"name":p.get("name"),"formula":p.get("formula"),"charge":p.get("charge")}
    return out


def listish(payload: object) -> list[dict]:
    if isinstance(payload,list): return [x for x in payload if isinstance(x,dict)]
    if isinstance(payload,dict):
        for k in ("results","data","study","studies"):
            v=payload.get(k)
            if isinstance(v,list): return [x for x in v if isinstance(x,dict)]
        if payload: return [payload]
    return []


def is_human(row: dict) -> bool:
    text=" ".join(str(row.get(k) or "") for k in ("subject_species","species","SUBJECT_SPECIES","study_title","STUDY_TITLE")).lower()
    return "homo sapiens" in text or "human" in text


def acquire(matrix: dict, rhea: dict) -> dict:
    meta=participant_metadata(rhea); rows=[]; errors=[]
    for species in matrix.get("species_index",[]):
        m=meta.get(str(species),{}); name=m.get("name")
        rec={"species":species,**m,"refmet_matches":[],"human_studies":[],"exchange_flux_requires_transport_or_turnover_evidence":True}
        if name:
            encoded=urllib.parse.quote(str(name),safe="")
            ref_url=f"{BASE}/refmet/name/{encoded}/all"
            try:
                payload,digest=fetch(ref_url); rec["refmet_request"]=ref_url; rec["refmet_raw_sha256"]=digest; rec["refmet_matches"]=listish(payload)
            except (urllib.error.URLError,urllib.error.HTTPError,TimeoutError,json.JSONDecodeError) as exc:
                errors.append({"species":species,"stage":"refmet","error":str(exc)})
            # Study lookup is navigation/context only. We deliberately do not
            # interpret study signal intensity or concentration as transport.
            study_url=f"{BASE}/study/refmet_name/{encoded}/summary"
            try:
                payload,digest=fetch(study_url); rec["study_request"]=study_url; rec["study_raw_sha256"]=digest; rec["human_studies"]=[x for x in listish(payload) if is_human(x)]
            except (urllib.error.URLError,urllib.error.HTTPError,TimeoutError,json.JSONDecodeError) as exc:
                errors.append({"species":species,"stage":"human-study","error":str(exc)})
        rows.append(rec)
    return {
        "schema":"dashi.bh4-exchange-context.v1",
        "source":"Metabolomics Workbench REST / RefMet",
        "acquired_at_utc":datetime.now(timezone.utc).isoformat(),
        "species_requested":len(rows),
        "species_with_refmet_match":sum(bool(r["refmet_matches"]) for r in rows),
        "species_with_human_study_context":sum(bool(r["human_studies"]) for r in rows),
        "species":rows,
        "errors":errors,
        "promotion_boundary":{
            "concentration_context_creates_exchange_flux":False,
            "human_study_occurrence_creates_exchange_flux":False,
            "refmet_identity_creates_transport_mechanism":False,
            "exchange_flux_requires_transport_or_turnover_evidence":True,
            "same_compartment_time_required":True,
        },
    }


def main() -> int:
    p=argparse.ArgumentParser(); p.add_argument("--matrix",type=Path,required=True); p.add_argument("--rhea",type=Path,required=True); p.add_argument("-o","--output",type=Path,required=True); a=p.parse_args()
    out=acquire(json.loads(a.matrix.read_text(encoding="utf-8")),json.loads(a.rhea.read_text(encoding="utf-8")))
    a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({k:out[k] for k in ("schema","species_requested","species_with_refmet_match","species_with_human_study_context")},indent=2))
    return 0 if not out["errors"] else 2

if __name__ == "__main__": raise SystemExit(main())
