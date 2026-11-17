#!/usr/bin/env python3
"""ASTM G173 multijunction radiative upper-bound reference. Not a PV device.
Source: NLR ASTM G173-03, 2002 rows (global AM1.5 + DNI).
External data is intentionally NOT vendored; see README/source notice.
"""
import argparse, csv, json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize_scalar

H=6.62607015e-34; C=299792458; KB=1.380649e-23
Q=1.602176634e-19; T=298.15; VT=KB*T/Q
HC_EV_NM=H*C/Q*1e9; BB=2*np.pi/(H**3*C**2)

def load(path):
    rows=[]
    with open(path, newline="",encoding="utf-8-sig") as f:
        for row in csv.reader(f):
            if len(row)!=4: continue
            try: r=list(map(float,row))
            except ValueError: continue
            if all(np.isfinite(r)):rows.append(r)
    a=np.asarray(rows)
    if a.shape!=(2002,4) or abs(a[0,0]-280)>.001 or abs(a[-1,0]-4000)>.001:
        raise ValueError("Expected 2002 standard G173 four-column wavelength rows")
    if np.any(np.diff(a[:,0])<=0):raise ValueError("Wavelengths not strictly increasing")
    if abs(np.trapezoid(a[:,2],a[:,0])-1000.3706555734)>.015:
        raise ValueError("Global AM1.5 power checksum failed")
    if abs(np.trapezoid(a[:,3],a[:,0])-900.1393292842)>.015:
        raise ValueError("Direct-normal AM1.5 power checksum failed")
    return a

class Spectrum:
    def __init__(self,a,col):
        self.lam=a[:,0]
        irr=a[:,col]
        self.power=float(np.trapezoid(irr,self.lam))
        photons=irr*self.lam*1e-9/(H*C)
        self.cumulative=np.concatenate([[0],np.cumsum(
            .5*(photons[:-1]+photons[1:])*np.diff(self.lam))])
    def above(self,eg):
        return float(np.interp(HC_EV_NM/eg,self.lam,self.cumulative))

def jzero(eg):
    e=eg*Q;kt=KB*T
    return Q*BB*sum(np.exp(-n*e/kt)*(
        e*e*kt/n+2*e*kt*kt/n**2+2*kt**3/n**3) for n in range(1,5))

def junctions(gaps,spec,conc):
    previous=0.0;j=[]
    for eg in gaps:
        above=spec.above(eg)
        j.append((Q*(above-previous)*conc,jzero(eg)))
        previous=above
    return j

def four(j):
    total=0.0
    for photo,dark in j:
        if photo<=0:return 0.0
        rhs=np.log1p(photo/dark);lo=0;hi=rhs
        for _ in range(48):
            x=(lo+hi)/2
            if x+np.log1p(x)>rhs:hi=x
            else:lo=x
        x=(lo+hi)/2
        total+=max(0,(photo-dark*np.expm1(x))*VT*x)
    return float(total)

def series(j):
    cap=min(item[0] for item in j)
    if cap<=0:return 0.0
    def p(current):
        return current*sum(VT*np.log1p((photo-current)/dark) for photo,dark in j)
    r=minimize_scalar(lambda x:-p(x),bounds=(0,cap),method="bounded",
        options={"xatol":max(1e-10,cap*1e-10)})
    return float(-r.fun)

def fit(n,spec,conc,term,starts=12):
    rng=np.random.default_rng(19042026+n+term)
    def efficiency(g):
        j=junctions(g,spec,conc)
        return (four(j) if term==4 else series(j))/(spec.power*conc)
    best=(-1,None)
    for start in range(starts):
        g=np.linspace(2.38,.58,n) if start==0 else np.sort(
            rng.uniform(.5,2.6,n))[::-1]
        for _ in range(10):
            before=efficiency(g)
            for i in range(n):
                lo=.5 if i==n-1 else g[i+1]+.04
                hi=2.7 if i==0 else g[i-1]-.04
                if lo>=hi:continue
                def loss(x):
                    trial=g.copy();trial[i]=x
                    return -efficiency(trial)
                opt=minimize_scalar(loss,bounds=(lo,hi),method="bounded",
                    options={"xatol":1e-5})
                g[i]=opt.x
            if abs(efficiency(g)-before)<1e-9:break
        eta=efficiency(g)
        if eta>best[0]:best=(eta,np.round(g,4).tolist())
    return {"eta_pct":round(100*best[0],3),"gaps_eV":best[1]}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--spectrum",required=True)
    parser.add_argument("--output")
    parser.add_argument("--quick",action="store_true")
    a=parser.parse_args()
    rows=load(a.spectrum)
    gl,di=Spectrum(rows,2),Spectrum(rows,3)
    for spec in (gl,di):
        for gaps in ([1.33],[1.9,1.0],[2.0,1.4,.8]):
            j=junctions(gaps,spec,1)
            assert 0<=series(j)<=four(j)+1e-7
            assert four(j)<=spec.power+1e-7
    results={"source":"NLR ASTM G173-03, mirror frssp/atlc ASTMG173.csv (blob 300821f0)",
        "note":"Ideal radiative ONLY, one emitting hemisphere, no measured device or global optimum",
        "global_W_m2":gl.power,"direct_W_m2":di.power,"cell_T_K":T,"runs":{}}
    for name,spec,conc in (("global_one_sun",gl,1),("direct_665_suns",di,665)):
        results["runs"][name]={}
        for n in ((1,3) if a.quick else (1,2,3,4,5)):
            results["runs"][name][str(n)]={"4T":fit(n,spec,conc,4),
                                             "2T":fit(n,spec,conc,2)}
    # Hypothetical *electrical* step-gap modulation, NOT a prediction that
    # measured optical Stark shifts become usable electrical bandgap shifts.
    # Any signed RF net input above this GROSS improvement defeats PV gain.
    source_gaps=((1.424,1.350),(1.424,1.336),(2.000,1.500),
                 (2.000,1.800),(2.000,1.400),(2.000,2.000))
    results["hypothetical_stark_gross_break_even"]=[]
    for static_gap,shifted_gap in source_gaps:
        static_w=four(junctions([static_gap],gl,1))
        shifted_w=four(junctions([shifted_gap],gl,1))
        results["hypothetical_stark_gross_break_even"].append({
            "static_gap_eV":static_gap,"shifted_gap_eV":shifted_gap,
            "static_ideal_W_m2":round(static_w,3),
            "shifted_ideal_W_m2":round(shifted_w,3),
            "max_allowable_net_RF_and_aux_W_m2_before_gain_disappears":
                round(shifted_w-static_w,3)})
    if a.output:Path(a.output).write_text(json.dumps(results,indent=2)+"\n")
    print(json.dumps(results,indent=2))

if __name__=="__main__":main()
