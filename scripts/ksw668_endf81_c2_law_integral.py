#!/usr/bin/env python3
"""C2 exact ENDF/B-VIII.1 N14 MF3/MT103 interpolation-law-aware source fold.

Official original evaluation DOI 10.11578/endf/2571019. Input ENDF bytes
are SHA256 checked by ksw668_endf81_n14np_original.get_grid.
Merge every ENDF knot and flux knot; integrate inside each subinterval using
adaptive 8/16 point Gauss-Legendre (no endpoints). This preserves ENDF
histogram jumps (INT=1) and duplicate-energy discontinuities, where a naive
global trapezoid is WRONG. Supports ENDF INT=1..5 and rejects extrapolation.
A ground-level spectrum is not a spectrum inside the body without transport.
"""
import argparse,bisect,csv,hashlib,json,math
from pathlib import Path
import ksw668_endf81_n14np_original as ENDF

N8=(-.9602898564975363,-.7966664774136267,-.5255324099163290,-.1834346424956498,.1834346424956498,.5255324099163290,.7966664774136267,.9602898564975363)
W8=(.1012285362903763,.2223810344533745,.3137066458778873,.3626837833783620,.3626837833783620,.3137066458778873,.2223810344533745,.1012285362903763)
N16=(-.9894009349916499,-.9445750230732326,-.8656312023878317,-.7554044083550030,-.6178762444026437,-.4580167776572274,-.2816035507792589,-.0950125098376374,.0950125098376374,.2816035507792589,.4580167776572274,.6178762444026437,.7554044083550030,.8656312023878317,.9445750230732326,.9894009349916499)
W16=(.0271524594117541,.0622535239386479,.0951585116824928,.1246289712555339,.1495959888165767,.1691565193950025,.1826034150449236,.1894506104550685,.1894506104550685,.1826034150449236,.1691565193950025,.1495959888165767,.1246289712555339,.0951585116824928,.0622535239386479,.0271524594117541)

class XS:
    def __init__(self,grid):
        self.xy=grid['pairs']
        self.energy=[e for e,v in self.xy]
        self.region=grid['interpolations']
        if self.region[-1][0]!=len(self.xy):raise ValueError("Invalid ENDF NBT")
    def sigma(self,e):
        if not self.energy[0]<=e<=self.energy[-1]:raise ValueError("No ENDF extrapolation")
        j=bisect.bisect_right(self.energy,e)
        if j==0:return self.xy[0][1]
        if j>=len(self.xy):return self.xy[-1][1]
        e0,v0=self.xy[j-1];e1,v1=self.xy[j]
        if e==e0:return v0
        if e1<=e0:raise ValueError("Unresolved duplicate ENDF energy")
        law=next(l for end,l in self.region if j+1<=end)
        if law==1:return v0
        f=(e-e0)/(e1-e0) if law in (2,4) else math.log1p((e-e0)/e0)/math.log1p((e1-e0)/e0)
        if law in (4,5):
            if v0<=0 or v1<=0:raise ValueError("Invalid ENDF log XS")
            result=v0*math.exp(f*math.log(v1/v0))
        else:result=v0+f*(v1-v0)
        if result<0 or not math.isfinite(result):raise ValueError("Bad physical XS")
        return result

class Flux:
    def __init__(self,rows):
        self.data=rows
        self.energy=[x for x,y in rows]
        if len(rows)<2 or any(not math.isfinite(x) or x<=0 or not math.isfinite(y) or y<0 for x,y in rows):
            raise ValueError("Invalid source spectrum")
        if any(y<=x for x,y in zip(self.energy,self.energy[1:])):
            raise ValueError("Flux knot energies not strictly increasing")
    def at(self,e):
        if not self.energy[0]<=e<=self.energy[-1]:raise ValueError("Flux extrapolation")
        i=bisect.bisect_right(self.energy,e)
        if i==0:return self.data[0][1]
        if i>=len(self.energy):return self.data[-1][1]
        e0,v0=self.data[i-1];e1,v1=self.data[i]
        return v0+(v1-v0)*(e-e0)/(e1-e0)

def gauss(f,a,b,nodes,weights):
    mid=(a+b)/2;half=(b-a)/2
    return half*sum(w*f(mid+half*x) for x,w in zip(nodes,weights))

def integrate_source(grid,flux_rows,n14_atoms,source,atol=1e-9,rtol=1e-8,max_depth=10):
    if not source or not source.strip():raise ValueError("Original source settings required")
    if not math.isfinite(n14_atoms) or n14_atoms<0:raise ValueError("Invalid target inventory")
    xs=XS(grid);flux=Flux(flux_rows)
    a,b=flux.energy[0],flux.energy[-1]
    if a<xs.energy[0] or b>xs.energy[-1]:
        raise ValueError("Evaluated source cannot cover entire neutron flux domain")
    knots=sorted(set(flux.energy+[e for e in xs.energy if a<e<b]))
    diagnostics={"subdivisions":0,"max_relative_estimate":0.0}
    def fn(e):return flux.at(e)*xs.sigma(e)
    def interval(left,right,depth):
        i8=gauss(fn,left,right,N8,W8)
        i16=gauss(fn,left,right,N16,W16)
        if not math.isfinite(i16) or i16<0:raise ValueError("Nonphysical rate integrand")
        err=abs(i16-i8)
        diagnostics["max_relative_estimate"]=max(
            diagnostics["max_relative_estimate"],err/max(abs(i16),1e-300))
        if err<=atol*(right-left)/(b-a)+rtol*abs(i16):return i16
        if depth>=max_depth:raise ValueError("Source fold did not numerically converge")
        mid=(left+right)/2
        if mid==left or mid==right:raise ValueError("Unresolvable source interval")
        diagnostics["subdivisions"]+=1
        return interval(left,mid,depth+1)+interval(mid,right,depth+1)
    integral=math.fsum(interval(x,y,0) for x,y in zip(knots,knots[1:]) if x<y)
    return {
      "status":"Conditional evaluated nuclear reaction-rate model, NOT human measurement",
      "source_endf_doi":"10.11578/endf/2571019",
      "original_n14_endf_sha256":grid["original_sha256"],
      "source_flux_origin_and_settings":source,
      "spectrum_support_eV":[a,b],
      "total_n14_atoms":n14_atoms,
      "evaluated_original_laws":sorted(set(l for _,l in xs.region)),
      "joint_energy_knots":len(knots),
      "flux_times_sigma_integral_barn_cm2_s":integral,
      "modelled_reactions_per_second":integral*n14_atoms*1e-24,
      "algorithm":"8/16 point adaptive Gauss, only between ENDF & flux knots, histogram/duplicate discontinuities respected",
      "diagnostics":diagnostics,
      "unaccounted_source_uncertainty":True,
      "body_neutron_transport_not_calibrated":True,
      "no_out_of_domain_extrapolation":True,
    }

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--endf",type=Path,required=True)
    ap.add_argument("--flux-csv",type=Path,required=True)
    ap.add_argument("--flux-source",required=True)
    ap.add_argument("--n14-atoms",type=float,required=True)
    ap.add_argument("--out",type=Path)
    ns=ap.parse_args()
    g=ENDF.get_grid(ns.endf,check_source_sha=True)
    with ns.flux_csv.open(newline="",encoding="utf-8-sig") as h:
        reader=csv.DictReader(h)
        if set(reader.fieldnames or [])!={"energy_eV","differential_flux_cm2_s_eV"}:
            raise ValueError("Unlabelled or incorrectly labelled neutron flux CSV")
        values=[(float(r["energy_eV"]),float(r["differential_flux_cm2_s_eV"])) for r in reader]
    result=integrate_source(g,values,ns.n14_atoms,ns.flux_source)
    result["verified_flux_csv_sha256"]=hashlib.sha256(ns.flux_csv.read_bytes()).hexdigest()
    result["verified_original_endf_sha256"]=ENDF.ORIGINAL_SHA
    output=json.dumps(result,sort_keys=True,indent=2)+"\n"
    if ns.out:ns.out.write_text(output)
    print(output)

if __name__=="__main__":
    main()
