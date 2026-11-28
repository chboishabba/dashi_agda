"""LXXXVII F8 P0: fail-closed full native A0/A1/C0/C1 receiver receipt gate.

Run ORIGINAL scripts/run_f8_lxix_native_source_matrix.py separately with
cooperative 90s local timeouts/checkpoints, then compare its four completed
JSON files with the historical 96-value extracted-stage receipt.
No simulation, CI, or interpolation model is constructed by this checker.
A historical diagnostic match is NOT a continuum/Agda/kernel certificate.
"""
import argparse, json, math
from pathlib import Path
import numpy as np
from ksw668_f8_tt_multipole import F

LABELS=("A0","A1","C0","C1")
PLACES=("near","far")
CHANNELS=("E4","E5","E4_tangent","E5_tangent")
SUFFIXES=("mode_intrinsic_4D_electric_Weyl",
          "mode_projected_5D_electric_Weyl",
          "mode_intrinsic_4D_electric_Weyl_tangent",
          "mode_projected_5D_electric_Weyl_tangent")

def geometry(label):
    assert label in LABELS
    dr=.008 if label[0]=="A" else .006
    eps=.04;dy=.012;final_t=12.
    span=F(final_t)-F(1.)
    n=math.ceil(span/.0012)
    dt=span/n
    bulk=math.sqrt(span*span-(1-1/final_t)**2)
    rx=bulk-.012;far=bulk+.1
    gap=rx-eps-math.log(final_t)
    nr=math.ceil(3.01/dr)+1
    ny=math.ceil(2.01/dy)+1
    assert gap>dr/2,("photon dark guard",label,gap)
    assert dt<min(dr*math.sqrt(3/44),dy*.45)
    for r in (rx,far):
        ir=int(math.floor(r/dr))
        assert 1<=ir-1 and ir+2<nr-1,(label,"cubic stencil",r,ir,nr)
    assert n==2258
    return dict(dr=dr,dy=dy,dt=dt,n=n,nr=nr,ny=ny,rx=rx,far=far,
                photon_margin=gap-dr/2,weak=label[-1]=="1")

def validate_receipt(reference):
    assert reference["scope"].startswith("extracted native stage")
    assert reference["channels"]==list(CHANNELS)
    assert reference["ell"]==[0,2,4]
    assert reference["steps_per_run"]==2259
    assert reference["normal_order"]==3
    assert set(reference["runs"])==set(LABELS)
    count=0
    for label in LABELS:
        g=geometry(label)
        assert abs(reference["dt"]-g["dt"])<1e-15
        assert abs(reference["dr_A" if label[0]=="A" else "dr_C"]-g["dr"])<1e-15
        for place in PLACES:
            arr=np.asarray(reference["runs"][label][place],dtype=float)
            assert arr.shape==(3,4) and np.isfinite(arr).all()
            count+=arr.size
    assert count==96
    return count

def compare_original(reference,prod,label,atol=1e-11,rtol=1e-6):
    g=geometry(label)
    assert prod["normal_order"]==3
    assert prod["steps"]==g["n"]
    assert abs(prod["step_time"]-g["dt"])<1e-15
    assert abs(prod["step_radial"]-g["dr"])<1e-15
    assert abs(prod["step_bulk"]-g["dy"])<1e-15
    assert bool(prod["weak_source_load"])==g["weak"]
    assert bool(prod["conservative_source_cell_average"])!=g["weak"]
    assert abs(prod["nominal_receiver_r"]-g["rx"])<1e-12
    assert abs(prod["far_receiver_grid_r"]-g["far"])<1e-12
    assert prod["intrinsic_4D_weyl_spatial_operator"]=="full_reconstructed_Delta3"
    assert not prod["numerical_convergence_certified"]
    residuals=[]
    for place in PLACES:
        prefix="receiver" if place=="near" else "far"
        for channel,suffix in enumerate(SUFFIXES):
            key=prefix+"_"+suffix
            observed=np.asarray(prod[key],dtype=float)
            expected=np.asarray(reference["runs"][label][place],dtype=float)[:,channel]
            assert observed.shape==(3,) and np.isfinite(observed).all()
            diff=np.abs(observed-expected)
            tol=atol+rtol*np.abs(expected)
            for mode in range(3):
                residuals.append(dict(place=place,ell=2*mode,channel=CHANNELS[channel],
                    difference=float(diff[mode]),tolerance=float(tol[mode]),
                    passed=bool(diff[mode]<=tol[mode])))
    assert len(residuals)==24
    failures=[r for r in residuals if not r["passed"]]
    assert not failures,("full production mismatch",label,failures)
    return dict(label=label,matched=24,max_difference=max(r["difference"] for r in residuals))

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--receipt",type=Path,
      default=Path(__file__).resolve().parents[1]/
      "Artifacts/ksw668/ads5_f8_LXIX_source_intervention_20261120.json")
    p.add_argument("--work",type=Path,required=True,
      help="Four completed ORIGINAL A0.json/A1.json/C0.json/C1.json outputs")
    p.add_argument("--atol",type=float,default=1e-11)
    p.add_argument("--rtol",type=float,default=1e-6)
    args=p.parse_args()
    assert args.atol>=0 and args.rtol>=0
    receipt=json.loads(args.receipt.read_text())
    validate_receipt(receipt)
    reports=[]
    for label in LABELS:
        path=args.work/(label+".json")
        assert path.is_file(),("original production run absent",str(path))
        reports.append(compare_original(receipt,json.loads(path.read_text()),label,args.atol,args.rtol))
    print(json.dumps(dict(status="PASS: 96/96 production-versus-historical-signature",
       reference_provenance=receipt["scope"],reports=reports,
       warning="This is a diagnostic parity receipt, NOT physical convergence or source rounding certification."),indent=2))

if __name__=="__main__":main()
