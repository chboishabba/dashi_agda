#!/usr/bin/env python3
"""P0/B2 four-spacecraft original MMS FGM CDF ephemeris -> position at event.

Official MMS FGM L2 burst files embed ancillary source ephemeris:
  mms#_fgm_r_gse_brst_l2, native km, Epoch_state in TT2000.
See MMS FGM Data Products Guide 2016, section 2.9.2/2.9.3, Table 5.
Primary source FGM guide:
https://lasp.colorado.edu/mms/sdc/public/datasets/fields/
MMS SDC official burst instrument rate 128Hz, ephemeris typically 30s.
Position is LINEARLY INTERPOLATED between ACTUAL original ephemeris
timestamps that bracket each requested event time. No extrapolation and
no fill values. Source geodesy/spatial interpolation/model error are
explicitly not supplied by the L2 ephemeris bracket itself.

Requires user-supplied original downloaded CDF bytes and actual SHA256
for each of MMS1..MMS4 (independent original source identification must
be verified upstream). No GPS, plasma current or calibrated E/B is
fabricated. This does not itself reconstruct a measured boundary.
"""
import argparse,hashlib,json,re
from pathlib import Path

EVENT_DATE="2017-06-17"
EXPECTED=("mms1","mms2","mms3","mms4")
NAME=re.compile(r"^(mms[1-4])_fgm_brst_l2_(20170617\d{6})_v\d+\.\d+\.\d+\.cdf$",re.I)

def sha256(path):
    h=hashlib.sha256()
    with Path(path).open("rb") as f:
        for b in iter(lambda:f.read(1<<20),b""):h.update(b)
    return h.hexdigest()

def verify_manifest(path):
    payload=json.loads(Path(path).read_text(encoding="utf-8"))
    if payload.get("schema")!="dashi.ksw668.mms4-original-fgm-ephemeris-input.v1":
        raise ValueError("Wrong original MMS4 FGM ephemeris provenance schema")
    entries=payload.get("files",[])
    if len(entries)!=4 or set(x.get("spacecraft","").lower() for x in entries)!=set(EXPECTED):
        raise ValueError("Exactly one MMS1-4 FGM CDF for each probe is required")
    result={}
    for item in entries:
        spacecraft=item["spacecraft"].lower()
        full=Path(item["path"])
        filename=full.name
        match=NAME.fullmatch(filename)
        if not match or match.group(1).lower()!=spacecraft:
            raise ValueError("Wrong original FGM spacecraft/file/event name: "+filename)
        if not full.is_file():raise ValueError("Original FGM CDF bytes absent: "+str(full))
        digest=item.get("sha256","").lower()
        if not re.fullmatch("[0-9a-f]{64}",digest) or digest!=sha256(full):
            raise ValueError("Original FGM file SHA256 mismatch: "+str(full))
        result[spacecraft]={"path":str(full),"sha256":digest}
    return result

def original_position_from_FGM(path,spacecraft,event_times,max_gap_s=120):
    import numpy as np
    from cdflib import CDF,cdfepoch
    from datetime import datetime,timezone
    c=CDF(str(path))
    try:
        variable=spacecraft+"_fgm_r_gse_brst_l2"
        vars_=c.cdf_info().zVariables
        if variable not in vars_:
            raise ValueError("Original burst FGM L2 lacks GSE ephemeris "+variable)
        raw=c.varget(variable)
        att=c.varattsget(variable)
        ep=att.get("DEPEND_0","Epoch_state")
        if isinstance(ep,(tuple,list)):ep=ep[0]
        if ep not in vars_:
            if "Epoch_state" in vars_:ep="Epoch_state"
            else:raise ValueError("Missing original ephemeris dependent time variable")
        t=np.asarray(cdfepoch.to_datetime(c.varget(ep)),dtype="datetime64[ns]")
        pos=np.asarray(raw,dtype=float)
        if pos.ndim!=2 or pos.shape[0]!=len(t) or pos.shape[1]<3:
            raise ValueError("Source original ephemeris shape or time count wrong")
        pos=pos[:,:3] # Fourth FGM support field is |r| in km.
        if np.any(~np.isfinite(pos)) or np.any(np.abs(pos)>1e10):
            raise ValueError("Source FGM ephemeris is nonfinite/fill contaminated")
        if len(t)<2 or np.any(np.diff(t.astype("int64"))<=0):
            raise ValueError("Missing ascending original spacecraft ephemeris samples")
        observations=[]
        for isotime in event_times:
            event=datetime.fromisoformat(isotime.replace("Z","+00:00"))
            if event.tzinfo is None:raise ValueError("Event time must be UTC")
            utc=event.astimezone(timezone.utc)
            if utc.date().isoformat()!=EVENT_DATE or not (
                    "20:24:03" <= utc.strftime("%H:%M:%S") <= "20:24:11"):
                raise ValueError("Outside selected original 2017 source interval")
            q=np.datetime64(utc.replace(tzinfo=None),"ns")
            i=np.searchsorted(t,q,side="right")
            if i==0 or i>=len(t):
                raise ValueError("Original FGM ephemeris does not bracket event time")
            left=int(t[i-1].astype("int64"));right=int(t[i].astype("int64"))
            gap=(right-left)*1e-9
            if gap<=0 or gap>max_gap_s:
                raise ValueError("Original FGM ephemeris has unacceptable bracketing gap")
            alpha=(int(q.astype("int64"))-left)/(right-left)
            if not 0<=alpha<=1:raise ValueError("Invalid original ephemeris interpolation")
            r=(1-alpha)*pos[i-1]+alpha*pos[i]
            observations.append({
                "time_utc":isotime,
                "r_GSE_km":[float(x) for x in r],
                "source_left_utc":str(t[i-1]),
                "source_right_utc":str(t[i]),
                "source_bracket_seconds":gap,
                "source_epoch_variable":ep,
                "source_position_variable":variable,
                "interpolation":"linear in original native GSE km",
                "original_uncertainty_beyond_interpolation":True,
            })
        return observations
    finally:c.close()

def run(manifest,source_times):
    files=verify_manifest(manifest)
    result={}
    for spacecraft,file in sorted(files.items()):
        result[spacecraft]={
           "path":file["path"],"sha256":file["sha256"],
           "positions":original_position_from_FGM(
               file["path"],spacecraft,source_times)}
    return {
      "schema":"dashi.ksw668.mms4-ephemeris-original-fgm-bracket.v1",
      "source":"MMS Science Data Center FGM L2; FGM Data Products Guide Table 5",
      "selected_event":"2017-06-17T20:24:03Z to 20:24:11Z",
      "source_original_Epoch_state_brackets":True,
      "source_FGM_CDF_SHA256_consistency":True,
      "source_official_SDC_origin_independently_attested":False,
      "time_queries":source_times,
      "data":result,
      "real_MMS4_boundary_source_E_B_J_ready":False,
      "source_spacecraft_position_model_error_qualified":False
    }

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--manifest",type=Path,required=True)
    p.add_argument("--times",nargs="+",default=[
       "2017-06-17T20:24:04Z","2017-06-17T20:24:08Z"])
    p.add_argument("--out",type=Path)
    a=p.parse_args()
    receipt=run(a.manifest,a.times)
    txt=json.dumps(receipt,indent=2,sort_keys=True)+"\n"
    if a.out:a.out.write_text(txt)
    print(txt)
