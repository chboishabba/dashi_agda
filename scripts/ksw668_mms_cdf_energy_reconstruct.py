#!/usr/bin/env python3
"""KSW 668 empirical A1/B1: same-spacecraft MMS1 original J·E' from hashed CDF.

Data: original MMS spacecraft public FGM, EDP-DCE, FPI DES/DIS MOMS Level-2.
Original event 17 June 2017 20:24:03–20:24:11 UTC, independent Lu et al.
(2020), DOI 10.1029/2020GL088761; Xiong et al. (2022),
DOI 10.1029/2022GL098445.  SDC instrument variable names in MMS CMAD.

This is *not* a measurement until original CDF timestamps, flags, spacecraft
and units are accepted. It never infers current from B alone, never joins
different spacecraft, and never calls electron-frame J·E' laboratory J·E.
It computes J = e*(n_i*v_i - n_e*v_e) on a common electron epoch with FPI
ion sampling tolerance and E' = E + v_e cross B in GSE.

Reconstruction is explicitly CONDITIONAL: single-population electron and ion
moments, quasi-neutrality NOT presumed (independent n_e and n_i), no electron
pressure-divergence term, possible instrumental timing/saturation flags.
The compared source paper may use a different current construction
(e.g. curlometer from 4 spacecraft); a same-author-method weld is still open.
"""
from __future__ import annotations
import argparse,hashlib,json,math
from pathlib import Path

EVENT_START="2017-06-17T20:24:03"
EVENT_END="2017-06-17T20:24:11"
Q_E=1.602176634e-19 # C (exact SI)
PROBE="1"
PRODUCTS={
 "fgm":"_fgm_brst_l2_",
 "edp":"_edp_brst_l2_dce_",
 "des":"_fpi_brst_l2_des-moms_",
 "dis":"_fpi_brst_l2_dis-moms_",
}

def sha256(path):
    h=hashlib.sha256()
    with Path(path).open("rb") as f:
        for chunk in iter(lambda:f.read(1<<20),b""):h.update(chunk)
    return h.hexdigest()


def resolve_files(raw_receipt,cache):
    r=json.loads(Path(raw_receipt).read_text(encoding="utf-8"))
    if r.get("spacecraft")!="MMS1":raise ValueError("Expected same spacecraft MMS1")
    if r.get("event_UTC")!={"start":"2017-06-17/20:24:03",
                              "end":"2017-06-17/20:24:11"}:
        raise ValueError("Wrong source event")
    candidates={}
    for entry in r.get("cdf_files",[]):
        path=Path(entry["relative_path"])
        if path.is_absolute() or ".." in path.parts:raise ValueError("Path traversal")
        full=Path(cache)/path
        if not full.is_file() or sha256(full)!=entry["sha256"]:
            raise ValueError("Raw CDF SHA-256 mismatch "+str(full))
        for name,fragment in PRODUCTS.items():
            if fragment in full.name.lower():
                candidates.setdefault(name,[]).append(full)
    if any(not candidates.get(name) for name in PRODUCTS):
        raise ValueError("Missing original FGM/EDP/FPI DES/DIS CDF product")
    return candidates


def load_frames(files,name,variable,flag_variable=None):
    """Returns original timestamp/coordinate paired rows, no inferred gaps.

    A CDF may have >1 contiguous versioned burst segments; verify that input
    has only one quality-qualified row at each timestamp before interpolation.
    """
    import numpy as np
    from cdflib import CDF, cdfepoch
    tchunks=[];vchunks=[];flagged=[]
    for path in files:
        c=CDF(str(path))
        try:
            arr=np.asarray(c.varget(variable),dtype=float)
            attribs=c.varattsget(variable)
            dep=attribs.get("DEPEND_0")
            if isinstance(dep,(list,tuple)):dep=dep[0]
            if not dep:raise ValueError(f"{path.name}:{variable} missing DEPEND_0")
            t=np.asarray(cdfepoch.to_datetime(c.varget(dep)),dtype="datetime64[ns]")
            if len(arr)!=len(t):raise ValueError("CDF variable/epoch shape mismatch")
            if arr.ndim!=2 or arr.shape[1]<3:
                raise ValueError("CDF expected GSE three-vector")
            if flag_variable:
                flag=np.asarray(c.varget(flag_variable))
                if len(flag)!=len(t):raise ValueError("CDF flag time mismatch")
                flagged.append(flag)
            tchunks.append(t);vchunks.append(arr[:,:3])
        finally:
            c.close()
    stamps=np.concatenate(tchunks)
    values=np.concatenate(vchunks)
    valid=np.isfinite(values).all(axis=1)&(np.abs(values)<1e20).all(axis=1)
    # In MMS FGM CDF, field is Nx4 with total norm as 4th column; reject
    # only invalid first 3, preserve the native vector field.
    order=np.argsort(stamps)
    stamps=stamps[order];values=values[order];valid=valid[order]
    if np.any(np.diff(stamps.astype("int64"))<=0):
        raise ValueError("Duplicate/unsorted CDF timestamps across source segments")
    return stamps,values,valid


def nearest_at(times,values,valid,query,max_s):
    import numpy as np
    ix=np.searchsorted(times,query)
    left=np.clip(ix-1,0,len(times)-1);right=np.clip(ix,0,len(times)-1)
    distleft=np.abs(times[left].astype("int64")-query.astype("int64"))
    distright=np.abs(times[right].astype("int64")-query.astype("int64"))
    best=np.where(distleft<=distright,left,right)
    delta=np.minimum(distleft,distright)*1e-9
    keep=(delta<=max_s)&valid[best]
    return values[best],delta,keep


def electron_frame_energy(E_mV_m,B_nT,ne_cm3,ni_cm3,ve_km_s,vi_km_s):
    import numpy as np
    E=np.asarray(E_mV_m,dtype=float)
    B=np.asarray(B_nT,dtype=float)
    ne=np.asarray(ne_cm3,dtype=float)
    ni=np.asarray(ni_cm3,dtype=float)
    ve=np.asarray(ve_km_s,dtype=float)
    vi=np.asarray(vi_km_s,dtype=float)
    if np.any(ne<0) or np.any(ni<0):raise ValueError("Negative physical source density")
    # Electron and ion current, n[cm^-3] v[km/s]:
    # 1e6/m^3 * 1e3 m/s * e C * 1e9 nA/A = e * 1e18 nA/m^2.
    JnA=(Q_E*1e18)*(ni[...,None]*vi-ne[...,None]*ve)
    Eprime=E+1e-3*np.cross(ve,B)
    electric_work=1e-3*np.einsum("...i,...i->...",JnA,Eprime)
    lab_work=1e-3*np.einsum("...i,...i->...",JnA,E)
    return JnA,Eprime,electric_work,lab_work


def get_scalar(files,variable):
    import numpy as np
    from cdflib import CDF,cdfepoch
    times=[];value=[]
    for f in files:
        c=CDF(str(f))
        try:
            a=np.asarray(c.varget(variable),dtype=float).reshape(-1)
            at=c.varattsget(variable)
            dep=at.get("DEPEND_0")
            if isinstance(dep,(list,tuple)):dep=dep[0]
            t=np.asarray(cdfepoch.to_datetime(c.varget(dep)),dtype="datetime64[ns]")
            if len(a)!=len(t):raise ValueError("scalar timestamp mismatch")
            times.append(t);value.append(a)
        finally:c.close()
    stamps=np.concatenate(times)
    values=np.concatenate(value)
    order=np.argsort(stamps)
    stamps=stamps[order];values=values[order]
    if np.any(np.diff(stamps.astype("int64"))<=0):raise ValueError("duplicate FPI density time")
    return stamps,values,np.isfinite(values)&(values>0)&(values<1e20)


def reconstruct(cache,receipt,edp_s=0.004,fgm_s=0.03,ion_s=0.20):
    import numpy as np
    cdfs=resolve_files(receipt,cache)
    v=dict(
      B=f"mms1_fgm_b_gse_brst_l2",
      E=f"mms1_edp_dce_gse_brst_l2",
      ne=f"mms1_des_numberdensity_brst",
      ni=f"mms1_dis_numberdensity_brst",
      ve=f"mms1_des_bulkv_gse_brst",
      vi=f"mms1_dis_bulkv_gse_brst",
    )
    te,ve,eok=load_frames(cdfs["des"],"des",v["ve"])
    ti,vi,iok=load_frames(cdfs["dis"],"dis",v["vi"])
    tn,ned,nok=get_scalar(cdfs["des"],v["ne"])
    tm,nid,mok=get_scalar(cdfs["dis"],v["ni"])
    tE,elec,Eok=load_frames(cdfs["edp"],"edp",v["E"])
    tB,mag,Bok=load_frames(cdfs["fgm"],"fgm",v["B"])
    lo=np.datetime64(EVENT_START,"ns")
    hi=np.datetime64(EVENT_END,"ns")
    sample=(te>=lo)&(te<hi)&eok
    t=te[sample]
    if not len(t):raise RuntimeError("No calibrated electron epochs in source event")
    B,Bdelta,Bvalid=nearest_at(tB,mag,Bok,t,fgm_s)
    E,Edelta,Evalid=nearest_at(tE,elec,Eok,t,edp_s)
    I,Idelta,Ivalid=nearest_at(ti,vi,iok,t,ion_s)
    NE,NEdelta,NEvalid=nearest_at(tn,ned[:,None],nok,t,0.020)
    NI,NIdelta,NIvalid=nearest_at(tm,nid[:,None],mok,t,ion_s)
    keep=Bvalid&Evalid&Ivalid&NEvalid&NIvalid
    if not np.any(keep):raise RuntimeError("No valid same-epoch FGM/EDP/FPI join")
    J,Ep,W,lab=electron_frame_energy(
        E[keep],B[keep],NE[keep,0],NI[keep,0],ve[sample][keep],I[keep])
    if not np.all(np.isfinite(W)):
        raise RuntimeError("Nonfinite source J.E' values")
    return {
      "schema":"dashi.ksw668.mms-original-gse-work-v1",
      "source_DOIs":["10.1029/2020GL088761","10.1029/2022GL098445"],
      "cdf_receipt":str(receipt),
      "event_utc":[EVENT_START,EVENT_END],
      "input_original_units":{"E":"mV/m","B":"nT","ne/ni":"cm^-3","ve/vi":"km/s"},
      "derived_units":{"J":"nA/m^2","Eprime":"mV/m","work":"nW/m^3"},
      "tested_epochs_before_quality_join":int(len(t)),
      "same_epoch_valid":int(np.sum(keep)),
      "valid_fraction":float(np.mean(keep)),
      "median_jeprime_nW_m3":float(np.median(W)),
      "min_jeprime_nW_m3":float(np.min(W)),
      "max_jeprime_nW_m3":float(np.max(W)),
      "fraction_jeprime_negative":float(np.mean(W<0)),
      "median_lab_je_nW_m3":float(np.median(lab)),
      "temporal_align_max_seconds":{"EDP":edp_s,"FGM":fgm_s,"FPI_ion":ion_s},
      "original_uncertainty_and_quality_flags":"NOT IMPLEMENTED: DO NOT PROMOTE TO ACCEPTED OBSERVATION",
      "same_paper_current_method_verified":False,
      "L2_species_errorflags_verified":False,
      "comparison_to_ideal_fourier_state_verified":False,
      "status":"PRELIMINARY UNFLAGGED DIAGNOSTIC; exact CDF bytes required",
    }


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--cache",type=Path,required=True)
    ap.add_argument("--raw-receipt",type=Path,required=True)
    ap.add_argument("--out",type=Path)
    args=ap.parse_args()
    r=reconstruct(args.cache,args.raw_receipt)
    txt=json.dumps(r,sort_keys=True,indent=2)+"\n"
    if args.out:args.out.write_text(txt)
    print(txt)


if __name__=="__main__":
    main()
