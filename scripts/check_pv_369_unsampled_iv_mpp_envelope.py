#!/usr/bin/env python3
"""Certified CONDITIONAL finite-sampling envelope for PV terminal MPP.

For any continuous nonnegative nonincreasing steady-state J(V) on EVERY
interval [V_i,V_{i+1}], V_i J(V_i) <= maximum_{all V} VJ(V)
<= max_i V_{i+1} J(V_i). Sampled monotonicity does NOT prove the
physical curve between samples is monotone. Require a separately supported
source-level monotonicity/steady-state certificate; output never certifies
that source. This handles unsampled MPP, unlike a piecewise-linear proxy.

The interval brackets are tightened for simultaneous absolute relative
V/J measurement errors and per-channel converter eta bounds. Entire raw
per-junction IV files MUST match an ordered SHA256 list from the exact P5
measured-data receipt. No silent resampling/interpolation and no replacing
P5's signed auxiliary/drive/recovery ledger. No independent certification.
"""
import argparse
import csv
import hashlib
import json
import math
from pathlib import Path

def number(x,name,minimum=0.,maximum=None):
    if isinstance(x,bool) or not isinstance(x,(int,float)) or not math.isfinite(x):
        raise ValueError(name+" not finite numeric")
    if x<minimum or (maximum is not None and x>maximum):
        raise ValueError(name+" out of range")
    return float(x)

def iv_load(path):
    rows=[]
    with open(path,encoding="utf-8-sig",newline="") as file:
        rr=csv.reader(file)
        head=next(rr,None)
        if head is None or len(head)!=2:raise ValueError("two IV columns required")
        for row in rr:
            if not row:continue
            if len(row)!=2:raise ValueError("IV row width mismatch")
            rows.append([number(float(row[0]),"voltage"),number(float(row[1]),"current")])
    if len(rows)<3:raise ValueError("at least 3 IV samples required")
    for i,(v,j) in enumerate(rows):
        if i==0 and v!=0:raise ValueError("JV sweep must start at short circuit")
        if i>0 and (v<=rows[i-1][0] or j>rows[i-1][1]+1e-12):
            raise ValueError("sampled JV must increase voltage and not increase generating current")
    if rows[0][1]<=0 or rows[-1][1]>1e-9:
        raise ValueError("sweep must include nonzero Jsc and a zero-current Voc endpoint")
    return rows

def bracket(rows,voltage_rel_bound,current_rel_bound):
    """Valid provided TRUE continuous J(V) is nonincreasing and errors
    bound every sample. Upper endpoint rectangles cover unobserved maxima.
    """
    lo=max(v*j for v,j in rows)
    hi=max(rows[i+1][0]*rows[i][1] for i in range(len(rows)-1))
    assert hi>=lo-1e-8*max(1,lo)
    lower=lo*(1-voltage_rel_bound)*(1-current_rel_bound)
    upper=hi*(1+voltage_rel_bound)*(1+current_rel_bound)
    return {"sampled_mpp_lower_W_m2":lo,"monotone_mpp_upper_W_m2":hi,
            "calibrated_mpp_lower_W_m2":lower,"calibrated_mpp_upper_W_m2":upper,
            "unsampled_sampling_gap_W_m2":hi-lo}

def certificate(p5,unc,iv_paths):
    if p5.get("real_world_certified") is not False:raise ValueError("P5 cannot self-certify")
    provenance=p5.get("declared_provenance") or {}
    hashes=provenance.get("ordered_iv_sha256")
    if not isinstance(hashes,list) or len(hashes)!=len(iv_paths) or not all(isinstance(x,str) and len(x)==64 for x in hashes):
        raise ValueError("ordered IV SHA256 list mandatory")
    if provenance.get("temperature_K") is None or not provenance.get("incident_spectrum_sha256"):
        raise ValueError("original specimen and irradiance provenance missing")
    if not isinstance(unc.get("monotone_full_IV_source"),str) or not unc["monotone_full_IV_source"].strip():
        raise ValueError("source-backed full-sweep monotonicity and steady-state declaration needed")
    for key in ("solar_rel_bound","voltage_rel_bound","current_rel_bound",
                "converter_efficiency_abs_bound","auxiliary_nominal_W_m2",
                "auxiliary_abs_bound_W_m2","drive_nominal_W_m2",
                "drive_abs_bound_W_m2","recovered_nominal_W_m2",
                "recovered_abs_bound_W_m2"):
        if key not in unc:raise ValueError("missing source-bound uncertainty "+key)
    uSolar=number(unc["solar_rel_bound"],"solar",0,.99)
    uV=number(unc["voltage_rel_bound"],"voltage",0,.99)
    uJ=number(unc["current_rel_bound"],"current",0,.99)
    uEta=number(unc["converter_efficiency_abs_bound"],"eta",0,1)
    aux=number(unc["auxiliary_nominal_W_m2"],"aux")
    auxErr=number(unc["auxiliary_abs_bound_W_m2"],"auxerr")
    drive=number(unc["drive_nominal_W_m2"],"drive")
    driveErr=number(unc["drive_abs_bound_W_m2"],"driveerr")
    recover=number(unc["recovered_nominal_W_m2"],"recovered")
    recoverErr=number(unc["recovered_abs_bound_W_m2"],"recoverederr")
    if recover>drive:raise ValueError("recovered energy exceeds drive")
    records=p5["four_terminal_per_junction"]
    if len(records)!=len(iv_paths) or not 2<=len(records)<=5:
        raise ValueError("2-5 IVs and matching source MPP channels required")
    sourceNet=number(p5["four_terminal_net_W_m2"],"source net",-1e12)
    nominal=sum(number(p["delivered_mpp_W_m2"],"delivered") for p in records)-aux-drive+recover
    if abs(nominal-sourceNet)>1e-8*max(1,abs(sourceNet)):
        raise ValueError("nominal auxiliary/driver costs changed from original P5")
    sun=number(p5["incident_solar_W_m2"],"incident",1e-12)
    lower=upper=0.
    per=[]
    for idx,(path,original_sha,p) in enumerate(zip(iv_paths,hashes,records)):
        digest=hashlib.sha256(Path(path).read_bytes()).hexdigest()
        if digest!=original_sha or digest not in provenance["input_sha256"].values():
            raise ValueError("IV data do not match exact original P5 source manifest")
        rows=iv_load(path)
        cert=bracket(rows,uV,uJ)
        eta=number(p["converter_eta"],"converter eta",0,1)
        originalMPP=number(p["gross_mpp_W_m2"],"source piecewise MPP")
        # Piecewise-linear model optimum must lie between sampled-real lower
        # and monotonic upper; otherwise wrong original source/units.
        if not cert["sampled_mpp_lower_W_m2"]-1e-8<=originalMPP<=cert["monotone_mpp_upper_W_m2"]+1e-8:
            raise ValueError("original P5 MPP incompatible with original raw IV")
        if abs(number(p["delivered_mpp_W_m2"],"delivered")-eta*originalMPP)>1e-8*max(1,originalMPP):
            raise ValueError("converter-delivered power forged")
        lo=cert["calibrated_mpp_lower_W_m2"]*max(0,eta-uEta)
        hi=cert["calibrated_mpp_upper_W_m2"]*min(1,eta+uEta)
        lower+=lo;upper+=hi
        per.append({"junction":idx+1,"iv_sha256":digest,**cert,
                    "delivered_lower_W_m2":lo,"delivered_upper_W_m2":hi})
    lowerNet=lower-(aux+auxErr)-(drive+driveErr)+max(0,recover-recoverErr)
    upperNet=upper-max(0,aux-auxErr)-max(0,drive-driveErr)+recover+recoverErr
    loSolar=sun*(1-uSolar);hiSolar=sun*(1+uSolar)
    return {"sample_id":provenance.get("sample_id"),
        "incident_spectrum_sha256":provenance["incident_spectrum_sha256"],
        "source_document":provenance.get("source_document"),
        "temperature_K":provenance.get("temperature_K"),
        "solar_lower_W_m2":loSolar,"solar_upper_W_m2":hiSolar,
        "net_lower_W_m2":lowerNet,"net_upper_W_m2":upperNet,
        "strict_robust_over_50":2*lowerNet>hiSolar,
        "worst_case_eta_pct":100*lowerNet/hiSolar,
        "per_junction_bounds":per,
        "full_curve_monotonicity_evidence_declared":unc["monotone_full_IV_source"],
        "true_continuum_monotonicity_authenticated":False,
        "steady_state_IEC_60904_certified":False,
        "independent_device_certification":False}

def selftest():
    checks=[]
    def ck(name,v):
        assert bool(v),name
        checks.append(name)
    for count in (5,11,21,51,101,1001):
        rows=[(i/(count-1),510*(1-i/(count-1))) for i in range(count)]
        r=bracket(rows,0,0)
        ck(str(count)+" exact true MPP included",r["sampled_mpp_lower_W_m2"]<=127.5+1e-8<=r["monotone_mpp_upper_W_m2"]+1e-8)
        ck(str(count)+" lower bound",abs(r["sampled_mpp_lower_W_m2"]-127.5)<.1)
        ck(str(count)+" upper explicit",r["monotone_mpp_upper_W_m2"]>=127.5)
    r5=bracket([(v,510*(1-v)) for v in [0,.25,.5,.75,1]],0,0)
    r1001=bracket([(i/1000,510*(1-i/1000)) for i in range(1001)],0,0)
    ck("5 point upper severe",abs(r5["monotone_mpp_upper_W_m2"]-191.25)<1e-9)
    ck("1001 point upper tight",abs(r1001["monotone_mpp_upper_W_m2"]-127.755)<1e-9)
    ck("sampling refinement tightens margin",r1001["unsampled_sampling_gap_W_m2"]<r5["unsampled_sampling_gap_W_m2"])
    ck("voltage current calibration widening",bracket([(v,510*(1-v)) for v in [0,.5,1]],.02,.02)["calibrated_mpp_upper_W_m2"]>bracket([(v,510*(1-v)) for v in [0,.5,1]],0,0)["calibrated_mpp_upper_W_m2"])
    ck("lower sample calibration decreases",bracket([(v,510*(1-v)) for v in [0,.5,1]],.02,.02)["calibrated_mpp_lower_W_m2"]<127.5)
    return {"checks_passed":len(checks),"all_passed":True,"synthetic_only":True,
            "required_physical_assumption":"real full-sweep steady-state I(V) continuous/nonnegative/nonincreasing",
            "tests":checks}

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--selftest",action="store_true")
    p.add_argument("--p5",type=Path);p.add_argument("--uncertainty",type=Path)
    p.add_argument("--iv",type=Path,nargs="+")
    p.add_argument("--output",type=Path)
    a=p.parse_args()
    if a.selftest:r=selftest()
    else:
        if not a.p5 or not a.uncertainty or not a.iv:
            p.error("require P5 receipt, original source bounds, and every raw IV file")
        r=certificate(json.loads(a.p5.read_text()),
                      json.loads(a.uncertainty.read_text()),a.iv)
    if a.output:a.output.write_text(json.dumps(r,indent=2)+"\n")
    print(json.dumps(r,indent=2))
if __name__=="__main__":main()
