#!/usr/bin/env python3
"""Exact finite common-source lead/lag and Rai-methods acceptance cut.

Source credits: Rai et al., iScience 28:112922 (2025), DOI
10.1016/j.isci.2025.112922, owns the empirical EEG, CCA, and methods.
Markus & Shamay-Tsoory (2024) DOI 10.3389/fnhum.2024.1497034
and Varlet & Grootswagers (2024) DOI 10.3389/fnhum.2024.1385624
supply original independently authored methodological context.

The invented lagged traces here are NOT their data or their Granger result.
"""
from __future__ import annotations
from fractions import Fraction as F
import json
import argparse

PAPER = "10.1016/j.isci.2025.112922"
# The published source reports 5 second / 80% overlapping CCA windows,
# circular-shift randomization (1000 repetitions) and 95% cluster cutoff.
# These are source metadata, not a complete executable original pipeline.
METHOD = dict(paper_doi=PAPER, band_hz=[1,4], window_seconds=5,
              overlap_percent=80, surrogate_kind="circularly shifted EEG",
              surrogates=1000, threshold_percentile=95,
              method="correlated component analysis", phase="observational")


def audit_method(m):
    expected = METHOD
    if not isinstance(m, dict) or set(m)!=set(expected) or any(m[k]!=v for k,v in expected.items()):
        raise ValueError("source-locked Rai method metadata mismatch")
    hop=F(m['window_seconds']*(100-m['overlap_percent']),100)
    if hop != 1:
        raise ValueError("unexpected sample window hop")
    return {"source_method_match":True,"nominal_window_hop_seconds":str(hop),
            "raw_data_present":False,"reproduced_CCA":False,
            "reproduced_1000_shift_null":False,
            "reproduced_cluster_FWER":False,
            "Granger_predictive_not_interventional":True}


def sequence(n=100):
    """Deterministic invented exogenous binary drive with sufficient rank."""
    x=7
    data=[]
    for _ in range(n):
        x=(1103515245*x+12345)%(2**31)
        data.append(1 if (x//65536)%2 else -1)
    return data


def solve(m, y):
    """Fraction Gauss-Jordan: only a 2- or 3-variable exact OLS toy."""
    n=len(m)
    a=[[F(m[i][j]) for j in range(n)]+[F(y[i])] for i in range(n)]
    for col in range(n):
        pivot=next((r for r in range(col,n) if a[r][col]),None)
        if pivot is None:
            raise ValueError("singular exact design")
        a[col],a[pivot]=a[pivot],a[col]
        v=a[col][col]
        a[col]=[z/v for z in a[col]]
        for r in range(n):
            if r!=col:
                scale=a[r][col]
                a[r]=[a[r][j]-scale*a[col][j] for j in range(n+1)]
    return [a[i][-1] for i in range(n)]


def fit(rows):
    p=len(rows[0][0]);
    if any(len(x)!=p for x,_ in rows):raise ValueError('inconsistent regression dimensions')
    m=[[sum(x[i]*x[j] for x,_ in rows) for j in range(p)] for i in range(p)]
    v=[sum(x[i]*y for x,y in rows) for i in range(p)]
    return solve(m,v)


def mse(rows,beta):
    return sum((y-sum(a*b for a,b in zip(x,beta)))**2 for x,y in rows)/len(rows)


def causal_common_source_witness():
    """Z->X, Z->Y at different lags; no structural edge X->Y.

    At t: X[t]=Z[t-1], Y[t]=Z[t-2].  A held-out lagged OLS
    gives an exact predictive X[t-1]->Y[t], solely because Z is
    shared.  A surgical intervention do(X[t-1] = -X[t-1]) changes
    that observation but not Y[t].
    """
    z=sequence()
    x=[0]+z[:-1]
    y=[0,0]+z[:-2]
    points=[]
    for t in range(3,len(z)):
        row_y=[F(1),F(y[t-1])]
        row_xy=[F(1),F(y[t-1]),F(x[t-1])]
        row_z=[F(1),F(y[t-1]),F(z[t-2])]
        points.append((row_y,row_xy,row_z,F(y[t])))
    tr=points[:55];ev=points[55:]
    fit_y=fit([(a,d) for a,b,c,d in tr]);fit_xy=fit([(b,d) for a,b,c,d in tr])
    fit_z=fit([(c,d) for a,b,c,d in tr])
    base=mse([(a,d) for a,b,c,d in ev],fit_y)
    extended=mse([(b,d) for a,b,c,d in ev],fit_xy)
    source=mse([(c,d) for a,b,c,d in ev],fit_z)
    assert base>0 and extended==0 and source==0
    for t in range(3,len(z)):
        normal=x[t-1];forced=-normal
        assert forced!=normal
        assert y[t]==z[t-2] # upstream state unchanged by x-only intervention
    return {"fixture_source":"invented shared exogenous rhythm Z",
       "train_rows":len(tr),"heldout_rows":len(ev),
       "heldout_Ypast_only_MSE":str(base),
       "heldout_Ypast_plus_Xpast_MSE":str(extended),
       "heldout_Ypast_plus_original_source_MSE":str(source),
       "predictive_lag_improvement":True,"direct_X_to_Y_edge_in_SCM":False,
       "do_X_changes_Y_in_declared_SCM":False,
       "original_EEG_or_study_Granger_reproduced":False}



def squared_pearson_int(x, y):
    """Exact Pearson squared by integer cross products; NOT Rai CCA."""
    if len(x) != len(y) or len(x) < 3:
        raise ValueError('short or mismatched binary traces')
    n=len(x)
    sx=sum(x); sy=sum(y)
    cov=n*sum(a*b for a,b in zip(x,y))-sx*sy
    vx=n*sum(a*a for a in x)-sx*sx
    vy=n*sum(b*b for b in y)-sy*sy
    if vx<=0 or vy<=0:
        raise ValueError('zero-variance binary trace')
    return F(cov*cov,vx*vy)


def circular_shift_shared_cue_null():
    """A 1000-shift permutation can reject temporal mismatch WITHOUT
    identifying direct X->Y coupling if both are driven by the same Z.

    Stand-in statistic is Pearson R squared, not CCA/cluster correction.
    All 1000 shifts are distinct and nonzero on 1009 invented samples.
    """
    z=sequence(1009)
    obs=squared_pearson_int(z,z)
    null=[squared_pearson_int(z,z[i:]+z[:i]) for i in range(1,1001)]
    assert obs==1 and max(null)<obs
    p=F(1+sum(v>=obs for v in null),1+len(null))
    return {'invented_samples':len(z),'null_permutations':len(null),
            'shift_offsets_distinct_and_nonzero':True,
            'unshifted_pearson_squared':str(obs),
            'max_shifted_pearson_squared':str(max(null)),
            'synthetic_permutation_tail_probability':str(p),
            'direct_brain_to_brain_edge_in_model':False,
            'common_sensory_cue_is_entire_explanation':True,
            'original_Rai_CCA_or_clusters_reproduced':False}

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--method', type=str, help='Source-defined method JSON for audit')
    a=p.parse_args()
    md=METHOD if a.method is None else json.load(open(a.method,encoding='utf8'))
    print(json.dumps({'method':audit_method(md),'lagged_common_source':causal_common_source_witness(),
                      'shared_cue_circular_shift':circular_shift_shared_cue_null()},indent=2,sort_keys=True))


if __name__=='__main__':main()
