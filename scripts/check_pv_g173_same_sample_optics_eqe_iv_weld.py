#!/usr/bin/env python3
"""P5/P7 measured-data weld: common-sample optical/EQE/IV to 2T/4T power.

Only source-supplied spectral fractions and source-supplied illuminated IV
curves may generate a candidate net electrical efficiency. Synthetic SELFTEST
receipts are NEVER physical device results. Previous ideal G173 optimizer is
not substituted for real EQE, JV or independently authenticated evidence.

spectrum CSV: wavelength_nm,global_W_m2_nm (>=2 rows), OR original\nASTM G173 four columns (wavelength, extraterrestrial, global, direct).
optics CSV: wavelength_nm,R,A1,...,AN,T (N=2..5)
eqe CSV: wavelength_nm,EQE1,...,EQEN
iv_i CSV: voltage_V,current_A_m2 (>=2 rows for each of N cells)
All spectra share EXACT wavelength grid. Fractions R+T+sum A_i=1.
Requires EQE_i<=A_i, so the ratio is not mislabeled as internal QE.
For two-terminal assembly, predicts an IDEAL lossless series connection
from separate cell IV; it does not claim to be a measured assembled 2T JV.
For 4T, each separate IV yields its piecewise-linear MPP, then an explicitly
supplied per-channel converter efficiency and net auxiliary cost is applied.
"""
import argparse
import csv
import json
import hashlib
from pathlib import Path

import numpy as np

H=6.62607015e-34; C=299792458.; Q=1.602176634e-19

def sha256_file(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def table(path):
    with open(path,encoding="utf-8-sig",newline="") as f:
        reader=csv.reader(f)
        header=next(reader)
        a=np.array([[float(x) for x in row] for row in reader if row],float)
    if a.ndim!=2 or a.shape[0]<2 or a.shape[1]!=len(header) or not np.isfinite(a).all():
        raise ValueError(f"{path}: invalid finite rectangular table")
    return header,a

def matching(primary,other):
    if primary.shape[0]!=other.shape[0] or not np.array_equal(primary[:,0],other[:,0]):
        raise ValueError("spectral grids must match exactly; no silent interpolation")

def strict_spectrum(spec,optic,eqe,n):
    if spec.shape[1] not in (2,4) or optic.shape[1]!=n+3 or eqe.shape[1]!=n+1:
        raise ValueError("unexpected spectrum/optics/EQE column count")
    matching(spec,optic);matching(spec,eqe)
    wl=spec[:,0]; incoming=spec[:,2] if spec.shape[1]==4 else spec[:,1]\n    if spec.shape[1]==4:\n        if spec.shape[0]!=2002 or abs(wl[0]-280)>.001 or abs(wl[-1]-4000)>.001:\n            raise ValueError("4-column G173 must have all 2002 standard rows")\n        if abs(float(np.trapezoid(incoming,wl))-1000.3706555734)>.015:\n            raise ValueError("G173 global input checksum failed")
    if np.any(np.diff(wl)<=0) or wl[0]<=0 or np.any(incoming<0):
        raise ValueError("invalid wavelength ordering or negative irradiance")
    R=optic[:,1]; A=optic[:,2:2+n]; T=optic[:,-1]; E=eqe[:,1:]
    if np.any(optic[:,1:]<0) or np.any(optic[:,1:]>1) or np.any(E<0) or np.any(E>1):
        raise ValueError("spectral fractions must be in [0,1]")
    if not np.allclose(R+np.sum(A,axis=1)+T,1,rtol=0,atol=1e-6):
        raise ValueError("photon energy fraction missing or double counted")
    if np.any(E>A+1e-8):
        raise ValueError("EQE exceeds its wavelength-local optical absorptance")
    power=float(np.trapezoid(incoming,wl))
    if power<=0:raise ValueError("zero incident solar input")
    photons=incoming*(wl*1e-9)/(H*C)
    jsc=Q*np.trapezoid(photons[:,None]*E,wl,axis=0)
    return power,jsc.tolist()

def validate_iv(iv):
    if iv.shape[1]!=2:raise ValueError("IV requires voltage and current")
    V=iv[:,0];J=iv[:,1]
    if np.any(np.diff(V)<=0) or V[0]!=0 or np.any(J<0) or np.any(np.diff(J)>1e-10):
        raise ValueError("IV requires V=0 first, V increasing, nonnegative monotonically decreasing J")
    if J[-1]>1e-9 or J[0]<=0:
        raise ValueError("IV must include short circuit and open circuit")
    return V,J

def segment_power_max(x,y):
    """Exact maximum over a piecewise-linear y(x), for P=x*y."""
    winners=[(float(x[i]*y[i]),float(x[i])) for i in range(len(x))]
    for i in range(len(x)-1):
        dx=x[i+1]-x[i]
        if dx<=0:continue
        slope=(y[i+1]-y[i])/dx
        intercept=y[i]-slope*x[i]
        if slope<0:
            stationary=-intercept/(2*slope)
            if x[i]<stationary<x[i+1]:
                winners.append((float(stationary*(slope*stationary+intercept)),float(stationary)))
    return max(winners)

def max_4terminal(ivs,eta):
    output=[]
    for idx,(iv,eff) in enumerate(zip(ivs,eta)):
        V,J=validate_iv(iv)
        P,vmp=segment_power_max(V,J)
        output.append({"junction":idx+1,"gross_mpp_W_m2":P,
                       "voltage_mpp_V":vmp,"converter_eta":float(eff),
                       "delivered_mpp_W_m2":P*float(eff)})
    return output

def series_max(ivs):
    """Exact piecewise-linear current matched series stack P=I sum V_i(I)."""
    curves=[validate_iv(iv) for iv in ivs]
    cap=min(j[0] for v,j in curves)
    current_knots={0.,float(cap)}
    for v,j in curves:
        current_knots.update(float(t) for t in j if 0<=t<=cap)
    points=sorted(current_knots)
    vs=[]
    for i in points:
        total=0.
        for v,j in curves:
            # reverse I(V) to V(I); zero-current points may duplicate.
            flipped_j=j[::-1];flipped_v=v[::-1]
            good=np.r_[True,np.diff(flipped_j)>1e-13]
            total+=float(np.interp(i,flipped_j[good],flipped_v[good]))
        vs.append(total)
    # Power is I*Vtotal(I), Vtotal declines as I increases.
    power,current=segment_power_max(np.asarray(points),np.asarray(vs))
    return {"gross_mpp_W_m2":power,"current_mpp_A_m2":current,
            "voltage_mpp_V":float(np.interp(current,points,vs)),
            "type":"predicted_lossless_series_from_separate_IV_not_measured_assembled_2T"}

def weld(spec,optic,eqe,ivs,eta,aux=0,drive=0,recovered=0,jsc_tolerance=.02):
    n=len(ivs)
    if not 2<=n<=5 or len(eta)!=n:raise ValueError("2–5 cells with one converter eta each")
    if any(not 0<=x<=1 for x in eta) or min(aux,drive,recovered)<0 or recovered>drive:
        raise ValueError("invalid converter or signed auxiliary/drive cost")
    incident,expected=strict_spectrum(spec,optic,eqe,n)
    measured=[validate_iv(i)[1][0] for i in ivs]
    if any(abs(a-b)>jsc_tolerance*max(a,b) for a,b in zip(expected,measured)):
        raise ValueError("optical EQE Jsc disagrees with the SAME-JV short circuit")
    independent=max_4terminal(ivs,eta)
    series=series_max(ivs)
    gross4=sum(j["delivered_mpp_W_m2"] for j in independent)
    net4=gross4-aux-drive+recovered
    # Same external auxiliary ledger applies to ideal unconverted series case.
    net2=series["gross_mpp_W_m2"]-aux-drive+recovered
    return {"incident_solar_W_m2":incident,"expected_optical_Jsc_A_m2":expected,
            "iv_measured_Jsc_A_m2":list(map(float,measured)),
            "four_terminal_per_junction":independent,
            "four_terminal_net_W_m2":net4,"four_terminal_net_PCE":net4/incident,
            "four_terminal_strictly_above_half":2*net4>incident,
            "two_terminal_ideal_series":series,
            "two_terminal_net_W_m2":net2,"two_terminal_net_PCE":net2/incident,
            "two_terminal_strictly_above_half":2*net2>incident,
            "optical_energy_conservation":"checked per wavelength",
            "EQE_bounded_by_absorption":"checked per wavelength",
            "provenance":"USER-SUPPLIED; authenticity not verified by computation",
            "real_world_certified":False}

def selftest():
    checks=[]
    def ck(n,cond):
        assert bool(cond),n
        checks.append(n)
    n=4;wl=np.linspace(400.,1000.,31)
    S=np.column_stack([wl,np.ones_like(wl)])
    A=np.full((len(wl),n),.2)
    optical=np.column_stack([wl,np.full(len(wl),.1),A,np.full(len(wl),.1)])
    eqe=np.column_stack([wl,A*.8])
    expected=strict_spectrum(S,optical,eqe,n)[1]
    iv=[]
    for current in expected:
        v=np.linspace(0,1.,21)
        iv.append(np.column_stack([v,current*(1-v)]))
    result=weld(S,optical,eqe,iv,[.97]*n,aux=2.)
    ck("synthetic per-wavelength balance",result["optical_energy_conservation"].startswith("checked"))
    ck("synthetic optical Jsc matches JV",np.allclose(result["expected_optical_Jsc_A_m2"],expected))
    ck("synthetic 4T nonnegative MPP",result["four_terminal_net_W_m2"]>0)
    ck("synthetic 2T series MPP",result["two_terminal_ideal_series"]["gross_mpp_W_m2"]>0)
    ck("synthetic 4T <= gross",sum(x["delivered_mpp_W_m2"] for x in result["four_terminal_per_junction"])<=sum(x["gross_mpp_W_m2"] for x in result["four_terminal_per_junction"]))
    ck("selftest not certified",result["real_world_certified"] is False)
    def rejected(fn):
        try:fn()
        except ValueError:return True
        return False
    ck("reject double-counted absorption",rejected(lambda:strict_spectrum(S,np.column_stack([wl,np.full(len(wl),.1),A*2,np.full(len(wl),.1)]),eqe,n)))
    ck("reject EQE > A",rejected(lambda:strict_spectrum(S,optical,np.column_stack([wl,A*1.1]),n)))
    ck("reject grid mismatch",rejected(lambda:strict_spectrum(S,optical,np.column_stack([wl+1,A*.8]),n)))\n    ck("reject incomplete 4-column G173",rejected(lambda:strict_spectrum(np.column_stack([wl,wl,wl,wl]),optical,eqe,n)))
    ck("reject Jsc mismatch",rejected(lambda:weld(S,optical,eqe,[np.column_stack([i[:,0],i[:,1]*.1]) for i in iv],[.97]*n)))
    ck("reject converter eta >1",rejected(lambda:weld(S,optical,eqe,iv,[1.2]*n)))
    ck("reject recovered work > drive",rejected(lambda:weld(S,optical,eqe,iv,[1.]*n,drive=1,recovered=2)))
    ck("reject non-monotonic IV",rejected(lambda:validate_iv(np.array([[0,1],[1,2]]))))
    ck("pure 1J piecewise MPP is V=Voc/2",abs(segment_power_max(*validate_iv(iv[0]))[1]-.5)<1e-12)
    ck("4T gross dominates ideal lossless 2T",sum(x["gross_mpp_W_m2"] for x in max_4terminal(ivs,[1.]*n))>=series_max(ivs)["gross_mpp_W_m2"]-1e-9)
    return {"checks_passed":len(checks),"all_passed":True,"checks":checks,
            "synthetic_example_not_measured":result}

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--selftest",action="store_true")
    p.add_argument("--sample-id",type=str)
    p.add_argument("--temperature-k",type=float)
    p.add_argument("--source-provenance",type=str)
    p.add_argument("--spectrum",type=Path);p.add_argument("--optics",type=Path)
    p.add_argument("--eqe",type=Path);p.add_argument("--iv",type=Path,nargs="+")
    p.add_argument("--converter-efficiency",type=float,nargs="+")
    p.add_argument("--auxiliary-w-m2",type=float,default=0.)
    p.add_argument("--drive-w-m2",type=float,default=0.)
    p.add_argument("--recovered-w-m2",type=float,default=0.)
    p.add_argument("--output",type=Path)
    a=p.parse_args()
    if a.selftest:out=selftest()
    else:
        if not all([a.spectrum,a.optics,a.eqe,a.iv,a.converter_efficiency,
                    a.sample_id,a.temperature_k,a.source_provenance]):
            p.error("real-data evaluation requires all 5 input families plus sample ID, temperature and source provenance")
        if a.temperature_k<=0 or not np.isfinite(a.temperature_k):
            p.error("temperature must be finite and >0 K")
        _,s=table(a.spectrum);_,o=table(a.optics);_,e=table(a.eqe)
        iv=[table(x)[1] for x in a.iv]
        out=weld(s,o,e,iv,a.converter_efficiency,
                 a.auxiliary_w_m2,a.drive_w_m2,a.recovered_w_m2)
        all_files=[a.spectrum,a.optics,a.eqe]+a.iv
        out['declared_provenance']={
            'sample_id':a.sample_id,'temperature_K':a.temperature_k,
            'source_document':a.source_provenance,
            'incident_spectrum_sha256':sha256_file(a.spectrum),
            'input_sha256':{str(path):sha256_file(path) for path in all_files},
            'data_authenticity_independently_verified':False}

    if a.output:a.output.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2))
if __name__=="__main__":main()
