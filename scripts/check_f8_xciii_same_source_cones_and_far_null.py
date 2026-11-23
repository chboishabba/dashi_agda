"""F8 XCIII — original moving AdS5 compact-source causal support.
Finite source radius 0<r<eps and pulse 0<Delta T<pulse. Exact SymPy
brane convexity and induced cone; high-precision bounded source-event
ambient cone; original LVI production far Weyl non-null audit.
Causal reach is NOT a proof of nonzero Green coupling, detector reception,
strong wall trace or continuum convergence. No CI or new solver.
"""
import json
from pathlib import Path
import sympy as sp
import mpmath as mp

t=sp.symbols("t",positive=True)
F=sp.asinh(t)-sp.sqrt(1+t*t)/t
df=sp.simplify(sp.diff(F,t))
b=1/t
v=sp.simplify(sp.diff(b,t)/df)
accel=sp.simplify(sp.diff(v,t)/df)
assert sp.simplify(df-sp.sqrt(1+t*t)/t**2)==0
assert sp.simplify(v+1/sp.sqrt(1+t*t))==0
assert sp.simplify(accel-t**3/(1+t*t)**2)==0

def check():
    mp.mp.dps=75
    f=lambda u: mp.asinh(u)-mp.sqrt(1+u*u)/u
    T0=f(1);T1=f(12);pulse=mp.mpf(".065")
    eps=mp.mpf(".04");zr=mp.mpf(1)/12
    r0=mp.sqrt((T1-T0)**2-(1-zr)**2)
    rin=r0-mp.mpf(".012");rfar=r0+mp.mpf(".1")
    rbrane=mp.log(12)
    assert rbrane+eps<rin<r0<rfar
    assert rfar-eps-r0==mp.mpf(".06")
    def source_t(delta):
        return mp.findroot(lambda x:f(x)-T0-delta,(1,mp.mpf("1.12")))
    def cone(delta,rrecv,rsource):
        te=source_t(delta)
        return (T1-T0-delta)**2-(1/te-zr)**2-(rrecv-rsource)**2
    def rate(delta):
        te=source_t(delta);dz=1/te-zr;dt=T1-T0-delta
        # d(cone)/dT_source = -2(dt + dz dz_source/dT)
        return -2*(dt-dz/mp.sqrt(1+te*te))
    for d in (mp.mpf(0),pulse/4,pulse/2,pulse):
        assert rate(d)<0
        assert cone(d,rfar,eps)<0
    assert cone(0,rfar,eps)<0
    assert cone(0,rin,0)>0>cone(pulse,rin,0)
    assert cone(0,rin,eps)>0>cone(pulse,rin,eps)
    def cutoff(rs,x,y):
        return mp.findroot(lambda delta:cone(delta,rin,rs),(x,y))
    center=cutoff(mp.mpf(0),mp.mpf(".01"),mp.mpf(".02"))
    edge=cutoff(eps,mp.mpf(".055"),mp.mpf(".064"))
    assert 0<center<edge<pulse
    assert cone(mp.mpf(".06"),rin,mp.mpf(".039"))>0
    # Convex moving wall b(T): its straight endpoint chord is wholly on
    # the original physical side z>=b(T), since d²b/dT²>0.
    for delta in (mp.mpf(0),pulse/3,pulse*mp.mpf(".92")):
        te=source_t(delta);ze=1/te
        for j in range(1,20):
            lam=mp.mpf(j)/20
            Tmid=(1-lam)*(T0+delta)+lam*T1
            zchord=(1-lam)*ze+lam*zr
            assert zchord>1/source_t(Tmid-T0)
    # The prior LV/LVI receipt is original production but its stored
    # compact values are transcribed, not literal complete native JSON.
    path=Path(__file__).resolve().parents[1]/"Artifacts/ksw668/ads5_f8_LVI_corrected_refinement_compact_20261120.json"
    j=json.loads(path.read_text())
    assert j["schema"]=="LVI-corrected-finite-refinement-compact-receipt"
    assert j["physical_acceptance"] is False
    assert j["geometry"]["eps"]==.04 and j["geometry"]["final_t"]==12
    observed={}
    for label in ("coarse","medium","factorial-A","factorial-C","fine","fine-dt-half"):
        row=j["rows"][label]
        e4=sum(row["farE4"]);e5=sum(row["farE5"])
        assert all(map(lambda x:abs(x)<1e200,row["farE4"]+row["farE5"]))
        observed[label]={"far_E4":e4,"far_E5":e5,
                         "far_E4_nonzero":bool(e4!=0),"far_E5_nonzero":bool(e5!=0)}
    assert all(x["far_E4_nonzero"] and x["far_E5_nonzero"] for x in observed.values())
    return {"status":"PASS geometry / FAIL physical far-causal-null acceptance",
      "source_spatial_support":"r<0.04","source_bulk_clock_pulse":"0<DeltaT<0.065",
      "exact_d2z_dT2":str(accel),"bulk_chord_stays_physical_side":True,
      "near_brane_source_gap":float(rin-rbrane-eps),
      "far_bulk_source_exclusion_gap":float(rfar-r0-eps),
      "near_center_latest_source_DeltaT":float(center),
      "near_source_edge_limiting_latest_DeltaT":float(edge),
      "near_center_pulse_fraction":float(center/pulse),
      "near_edge_pulse_fraction":float(edge/pulse),
      "far_reported_nonzero_original_native_values":observed,
      "limitation":"Historical far E4/E5 are nonzero at a continuum causally inaccessible receiver. Classify as finite-grid causal defect, not a physical signal or proven unique error mechanism; original full source-to-Green/strong trace and time/radial refinement remain open."}

if __name__=="__main__":
    print(json.dumps(check(),indent=2))
