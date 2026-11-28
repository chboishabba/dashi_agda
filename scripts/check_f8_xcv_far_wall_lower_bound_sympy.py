"""F8 XCV — checkpoint-independent raw far-wall lower bound.

Consumes two ORIGINAL master LVI full producer JSONs at their original old
solver/blob identities. SymPy rational interpolation inequalities are
conditional only on their original `read_all` cubic stencil and recorded
far_mode_values. Does NOT fabricate native NPZ, reconstruct any particular
wall cell, certify continuum causality, or rerun propagation. No CI.
"""
import json
import argparse
from pathlib import Path
import sympy as S

FILES = {
    "medium": "ads5_f8_LVI_independent_medium_full.json",
    "medium-dt-half": "ads5_f8_LVI_independent_medium-dt-half_full.json",
}
OLD_SOLVER_SHA="26f089b2aea202a82f19db7faa6c0e3eaa4554c5"
OLD_CK_SHA="4e319596d9064e7c9238b4a6570401e94df8a521"

def original_interpolation_bound(data):
    assert data["model"]=="original moving AdS5 a=t Neumann compact TT"
    assert data["original_radial_multipoles"]==[0,2,4]
    assert data["normal_order"]==3
    assert data["source_git_blobs"]["ksw668_f8_tt_multipole.py"]==OLD_SOLVER_SHA
    assert data["source_git_blobs"]["ksw668_f8_ssprk_checkpoint.py"]==OLD_CK_SHA
    assert data["fixed_physical_receiver_cubic_interpolation"] is True
    assert data["intrinsic_4D_weyl_spatial_operator"]=="full_reconstructed_Delta3"
    r=S.Rational(str(data["far_receiver_grid_r"]))
    dr=S.Rational(str(data["step_radial"]))
    eps=S.Rational(str(data["eps"]))
    j=int(S.floor(r/dr));q=r/dr-j
    weights=[-q*(q-1)*(q-2)/6, (q+1)*(q-1)*(q-2)/2,
             -(q+1)*q*(q-2)/2, (q+1)*q*(q-1)/6]
    assert S.simplify(sum(weights)-1)==0
    assert j>=1 and j+2<int(data["radius_bins"])-1
    wa=sum(map(abs,weights))
    assert wa>0
    far=data["far_mode_values"]
    assert len(far)==3
    bound=[]
    for idx,ell in enumerate((0,2,4)):
        H=S.Rational(str(far[idx]))
        assert H!=0,("recorded far-field nonzero control failed",ell)
        factor=(r/eps)**ell
        # |H|=factor*|sum_i w_i U_i| <=factor*sum|w_i|*max|U_i|.
        lower=abs(H)/(factor*wa)
        assert lower>0
        bound.append({"ell":ell,"recorded_far_H":str(H),
                      "minimum_max_abs_native_wall_stencil":float(lower)})
    return {"far_stencil_indices":[j-1,j,j+1,j+2],
            "fractional_cell_position":float(q),
            "sum_abs_cubic_weights":float(wa),
            "lower_bounds":bound}

def run(root):
    out={}
    for label,filename in FILES.items():
        path=root/filename
        assert path.is_file(),("missing ORIGINAL full producer JSON",str(path))
        data=json.loads(path.read_text(),parse_float=S.Rational)
        out[label]=original_interpolation_bound(data)
    for ell in range(3):
        assert out["medium"]["lower_bounds"][ell]["minimum_max_abs_native_wall_stencil"]>0
        assert out["medium-dt-half"]["lower_bounds"][ell]["minimum_max_abs_native_wall_stencil"]>0
    assert out["medium"]["far_stencil_indices"]==[330,331,332,333]
    return {"status":"PASS exact algebra on original full producer decimal receipt inputs",
            "cases":out,"physical_far_causal_null":"FAIL",
            "checkpoint_raw_grid_cell_recovered":False,
            "scope":"Necessary wall-stencil amplitude lower bounds; not actual NPZ field measurement, source-to-field causal bound or convergence."}
if __name__=="__main__":
    a=argparse.ArgumentParser()
    a.add_argument("--receipt-dir",type=Path,default=Path(__file__).resolve().parents[1]/"Artifacts"/"ksw668")
    args=a.parse_args()
    print(json.dumps(run(args.receipt_dir),indent=2))
