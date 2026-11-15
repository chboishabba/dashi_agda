#!/usr/bin/env python3
"""Discover, fetch, and SHA-256 pin the ORIGINAL 2017-06-17 MMS burst CDFs.

Primary event selection (NOT guessed): 2017-06-17 20:24:03..20:24:11 UTC,
DOI 10.1029/2020GL088761, DOI 10.1029/2022GL098445. The MMS1 original
2022 paper used GSE->LMN axes; do not use an unrelated MMS2 LMN matrix.
PySPEDAS docs: https://pyspedas.readthedocs.io/en/stable/mms.html

This source script defaults to OFFLINE PLAN. --execute queries actual burst
availability, selects the dated segment(s), downloads FGM/EDP/FPI L2 files into
--cache, hashes all *selected* raw CDFs. --verify consumes the pinned receipt
and fails on any replaced or missing file; never invent an archive checksum.
It does NOT claim calibrated J.E' until instrument flags/time/interpolation,
electron-ion moments, unit transforms and original LMN coordinates are checked.

Install in pinned environment: pip install pyspedas cdflib
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path

DATE = "2017-06-17"
EVENT_START="2017-06-17/20:24:03"
EVENT_END="2017-06-17/20:24:11"
DAY = ["2017-06-17", "2017-06-18"]
DOIS = ["10.1029/2020GL088761", "10.1029/2022GL098445"]
PRODUCTS = ("fgm", "edp_dce", "des-moms", "dis-moms")


def sha256(path):
    h=hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024*1024),b""):
            h.update(block)
    return h.hexdigest()


def overlaps(start,end,event_start=EVENT_START,event_end=EVENT_END):
    def stamp(value):
        if isinstance(value,(float,int)):
            return float(value)
        # time_string from PySPEDAS is UTC calendar time with optional fraction.
        s=str(value).replace("/"," ").replace("Z","").replace("T"," ")
        return datetime.fromisoformat(s).replace(tzinfo=timezone.utc).timestamp()
    return stamp(start) < stamp(event_end) and stamp(end) > stamp(event_start)


def eprime_and_work(j_nA_m2,e_mV_m,ve_km_s,b_nT):
    """Returns J.E' [nW/m^3]. J and ve are actual FPI-derived vectors,
    never inferred from the magnetic field alone.
    E'[mV/m]= E[mV/m] + 1e-3*(ve[km/s] cross B[nT]).
    J[nA/m2]*E'[mV/m]*1e-3 -> nW/m3.
    """
    cross=[ve_km_s[1]*b_nT[2]-ve_km_s[2]*b_nT[1],
           ve_km_s[2]*b_nT[0]-ve_km_s[0]*b_nT[2],
           ve_km_s[0]*b_nT[1]-ve_km_s[1]*b_nT[0]]
    ep=[float(e_mV_m[i])+1e-3*cross[i] for i in range(3)]
    je=1e-3*sum(float(j_nA_m2[i])*ep[i] for i in range(3))
    return ep,je


def verify_pinned(receipt,cache):
    r=json.loads(Path(receipt).read_text())
    if r["event_UTC"]["start"] != EVENT_START or r["event_UTC"]["end"]!=EVENT_END:
        raise ValueError("Refusing an unrelated MMS burst event")
    paths=r["cdf_files"]
    if not paths:
        raise ValueError("No CDFs in receipt")
    for row in paths:
        rel=Path(row["relative_path"])
        if rel.is_absolute() or ".." in rel.parts: raise ValueError("bad path")
        f=Path(cache)/rel
        if not f.is_file() or sha256(f)!=row["sha256"]:
            raise ValueError("missing or mutated original CDF: "+str(f))
    return {"verified":len(paths),"source_replay":str(receipt)}


def acquire(cache,probe):
    try:
        import pyspedas
        from pyspedas.projects.mms import (mms_load_burst_intervals,
            mms_load_fgm, mms_load_edp, mms_load_fpi)
    except ImportError as ex:
        raise SystemExit("PySPEDAS missing: use pip install pyspedas") from ex

    cache=Path(cache).resolve()
    cache.mkdir(parents=True, exist_ok=True)
    os.environ["MMS_DATA_DIR"]=str(cache)
    starts,ends=mms_load_burst_intervals(trange=DAY,probe=probe)
    if len(starts)!=len(ends): raise AssertionError("bad burst interval response")
    chosen=[]
    for a,b in zip(starts,ends):
        # Accept numpy scalar epochs as float, or PySPEDAS time_string times.
        if overlaps(float(a),float(b)):
            chosen.append([pyspedas.time_string(a),pyspedas.time_string(b)])
    if not chosen:
        raise RuntimeError("No observed SDC burst interval overlaps published event")

    # Query the explicit event-window, not the whole calendar day.
    span=[EVENT_START,EVENT_END]
    # Preserve downloaded complete original CDFs: no time_clip truncation.
    for product in PRODUCTS:
        kw=dict(trange=span,probe=probe,data_rate="brst",level="l2",
                latest_version=True,time_clip=False)
        if product=="fgm": mms_load_fgm(**kw)
        elif product=="edp_dce": mms_load_edp(datatype="dce",**kw)
        else: mms_load_fpi(datatype=product,**kw)

    found=[]
    for f in sorted(cache.rglob("*.cdf")):
        name=f.name.lower()
        if not name.startswith("mms"+probe+"_") or "_brst_l2_" not in name:
            continue
        if "20170617" not in name: continue
        if not any(k in name for k in ("_fgm_","_edp_","_fpi_")): continue
        found.append({"relative_path":str(f.relative_to(cache)),
                      "sha256":sha256(f),"bytes":f.stat().st_size})
    found_types={key:any(key.replace("edp_dce","edp").replace("des-moms","des").replace("dis-moms","dis") in z["relative_path"].lower()
                         for z in found) for key in PRODUCTS}
    if not all(found_types.values()):
        raise RuntimeError("Incomplete correlated FGM/EDP/DES/DIS CDF: "+str(found_types))
    return {
        "schema":"dashi.mms.primary-raw-burst.v1",
        "attribution":"MMS mission; original 2017 event analyses DOI "+", ".join(DOIS),
        "event_UTC":{"start":EVENT_START,"end":EVENT_END},
        "spacecraft":"MMS"+probe,
        "burst_intervals_from_SDC":chosen,
        "products_complete_for_requested_window":found_types,
        "cdf_files":found,
        "kernel_or_physical_validation":False,
        "open":"CDF quality flags, calibration, variable epoch matching, interpolated J=ne(Vi−Ve), measured J.E', original LMN and uncertainties",
    }


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache",default="data/mms_20170617")
    parser.add_argument("--probe",choices=list("1234"),default="1")
    parser.add_argument("--execute",action="store_true")
    parser.add_argument("--receipt",help="JSON receipt path; write in execute mode")
    parser.add_argument("--verify",help="Verify a previous exact per-CDF digest receipt")
    a=parser.parse_args()
    if a.verify:
        print(json.dumps(verify_pinned(a.verify,a.cache),indent=2))
    elif a.execute:
        result=acquire(a.cache,a.probe)
        if not a.receipt: raise SystemExit("--receipt mandatory in --execute mode")
        Path(a.receipt).write_text(json.dumps(result,indent=2)+"\n")
        print(json.dumps(result,indent=2))
    else:
        print(json.dumps({"status":"plan-only; no raw CDF downloaded",
            "source_event":[EVENT_START,EVENT_END],
            "probe":a.probe,"four_products":list(PRODUCTS),
            "next":"--execute --receipt /tmp/ksw668_mms1_cdf_sha.json"},indent=2))


if __name__=="__main__":
    main()
