"""LXXXII P0 finite-grid original-FV emitter error receipt (conditional).

Uses ORIGINAL exact_cell_averages, ORIGINAL mathematical FV source boxes, and
measured binary64 native receiver source Jacobian K supplied by --adjoint-npz.
All arithmetic in the *reported a posteriori inequalities* uses Fraction.
This does NOT certify general floating-point emitter/adjoint algorithms.
"""
from fractions import Fraction as Q
import argparse,json
import numpy as np
from check_f8_lxxxi_original_fv_interval import boxes
from ksw668_f8_fv_source_flux import exact_cell_averages

def receipt(panels, evidence=None):
    h=Q(1,5); eps=.04; dr=.008; nr=13
    src=exact_cell_averages(eps,np.arange(nr)*dr,dr)
    mathematical=boxes(h=h,panels=panels)
    errors=[]; cells=[]
    for q in range(3):
        dimension=3+4*q
        for j in range(nr):
            W=((j*h+h/2)**dimension-max(Q(0),j*h-h/2)**dimension)/dimension
            emitted=Q(float(src[q,j]))*W
            lo,hi=mathematical[q][j] if j<=5 else (Q(0),Q(0))
            assert lo<=hi
            required=max(lo-emitted,emitted-hi,Q(0))
            absolute=max(abs(emitted-lo),abs(emitted-hi))
            errors.append(absolute/W)
            cells.append(dict(q=q,j=j,outside=bool(required>0),
                min_inflation=float(required),mass_error_upper=float(absolute)))
    report=dict(panels=panels,excluded_cells=sum(x['outside'] for x in cells),
        max_required_mass_inflation=max(x['min_inflation'] for x in cells),
        max_mass_error_bound=max(x['mass_error_upper'] for x in cells),cells=cells)
    if evidence is not None:
        d=np.load(evidence)
        K=d['K']; assert K.shape==(6,3,3,nr)
        assert np.array_equal(d['native_fv'],src), 'evidence source array differs'
        rows=[]
        for channel in range(6):
            for mode in range(3):
                bound=Q(0);lo=hi=nom=Q(0)
                for q in range(3):
                    dimension=3+4*q
                    for j in range(nr):
                        c=Q(float(K[channel,mode,q,j]))
                        W=((j*h+h/2)**dimension-max(Q(0),j*h-h/2)**dimension)/dimension
                        a,b=mathematical[q][j] if j<=5 else (Q(0),Q(0))
                        bound+=abs(c)*errors[q*nr+j]
                        lo+=min(c*a/W,c*b/W)
                        hi+=max(c*a/W,c*b/W)
                        nom+=c*Q(float(src[q,j]))
                assert lo<=nom+bound and hi>=nom-bound
                sharp=max(abs(nom-lo),abs(nom-hi))
                assert sharp<=bound
                rows.append(dict(channel=channel,mode=mode,
                    upper_absolute_error=float(bound),
                    sharp_box_error=float(sharp)))
        report['frozen_receiver']=dict(
            max_absolute_error_bound=max(v['upper_absolute_error'] for v in rows),rows=rows)
    report['authority']='Exact-rational finite fixture source enclosure assuming original FV interval validity and ideal rational h=1/5. Measured binary64 coefficients and K are frozen as exact data. Not a general IEEE/SciPy roundoff theorem or native floating evolution bound.'
    return report

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--panels',type=int,default=256)
    ap.add_argument('--adjoint-npz',default=None)
    args=ap.parse_args()
    print(json.dumps(receipt(args.panels,args.adjoint_npz),indent=2))
