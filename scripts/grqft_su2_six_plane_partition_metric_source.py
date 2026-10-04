#!/usr/bin/env python3
"""Finite SU(2) plaquette-matrix -> rigorous-interval first partition response.

For a supplied discrete set of SU(2) link configurations, independently
evaluate each of SIX literal rational-quaternion plaquette traces and the
standard bare SU(2) action. Compute the four diagonal derivatives of
sqrt(det g) g^ii g^jj W_ij at g=I and the complete sector metric derivatives.
Use rational Taylor bounds for exp(-S) to enclose Z and D_h log Z without
inventing a rational Gibbs density.

This is a selected DISCRETE QUADRATURE, not product-Haar SU(2) or a certified
approximation to it. Its E/R/B/vacuum fields are provided, NOT independently
derived from the CMP119 source. No Lorentzian stress, Wick continuation,
renormalised limit, or expanding-universe claim is implied.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

SPEC = importlib.util.spec_from_file_location(
    "grqft_su2_matrix_wilson", Path(__file__).with_name(
        "grqft_su2_literal_wilson_exact.py"))
assert SPEC and SPEC.loader
W = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(W)

PLANES=("01","02","03","12","13","23")
AXES=("0","1","2","3")
SECTORS=("E","R","B","vacuum")

def f(x):
    if isinstance(x,bool) or not isinstance(x,(str,int)):
        raise ValueError(f"non-exact rational: {x!r}")
    return F(x)

def I(x): return (x,x)
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def scale(s,a): return (min(s*a[0],s*a[1]),max(s*a[0],s*a[1]))
def div_pos(a,b):
    if b[0]<=0: raise ValueError("partition interval must be strictly positive")
    xs=[x/y for x in a for y in b]
    return (min(xs),max(xs))
def mul(a,b):
    xs=[x*y for x in a for y in b]
    return min(xs),max(xs)

def exp_negative_small(x,n):
    """For 0 <= x <= 1, odd Taylor truncation is lower, even is upper."""
    if x<0 or x>1 or n<2: raise ValueError("Taylor range/precision invalid")
    t=F(1)
    partial=t
    lower=None
    upper=None
    for k in range(1,2*n+1):
        t=t*x/k
        partial=partial-t if k%2 else partial+t
        if k==2*n-1: lower=partial
        if k==2*n: upper=partial
    assert lower is not None and upper is not None and lower>0 and lower<=upper
    return (lower,upper)

def exp_neg_interval(x,n=12):
    """Mathematically enclosed exp(-x), exact rational endpoints."""
    x=f(x)
    if x<0:
        lo,hi=exp_neg_interval(-x,n)
        return F(1)/hi,F(1)/lo
    times=0
    y=x
    while y>1:
        y/=2
        times+=1
    interval=exp_negative_small(y,n)
    for _ in range(times): interval=mul(interval,interval)
    return interval

def link_plaquette(links):
    if not isinstance(links,dict) or set(links)!=set(("AB","BC","DC","AD")):
        raise ValueError("Each oriented plaquette needs AB, BC, DC, AD")
    q=[W.quat(links[k]) for k in ("AB","BC","DC","AD")]
    h=W.loop(q)
    cost=1-h[0]
    if not (0<=cost<=2): raise ArithmeticError("SU2 Wilson cost out of bounds")
    return cost

def one_point(source,n=12):
    if source.get("model")!="six_plane_euclidean_SU2_discrete_quadrature":
        raise ValueError("Use explicit finite Euclidean SU2 discrete-quadrature model")
    provenance=source.get("provenance")
    if not isinstance(provenance,dict) or not all(
        isinstance(provenance.get(k),str) and provenance[k]
        for k in ("source_identifier","revision","cutoff","sector_provenance")):
        raise ValueError("Full finite model identity/provenance required")
    beta=4*f(source["inverse_bare_coupling_square"])
    if beta<=0: raise ValueError("bare inverse coupling must be positive")
    configs=source.get("configurations")
    if not isinstance(configs,list) or not configs:
        raise ValueError("nonempty finite quadrature required")
    ids=set()
    totalweight=F()
    reference_variation_totals={a:F() for a in AXES}
    Z=I(F())
    DZ={axis:I(F()) for axis in AXES}
    rows=[]
    for c in configs:
        name=c.get("id")
        if not isinstance(name,str) or not name or name in ids:
            raise ValueError("missing or duplicate configuration identity")
        ids.add(name)
        weight=f(c["reference_weight"])
        if weight<0: raise ValueError("negative discrete reference weight")
        totalweight+=weight
        plaquettes=c["plaquettes"]
        if not isinstance(plaquettes,dict) or set(plaquettes)!=set(PLANES):
            raise ValueError("require six actual SU2 plane plaquettes")
        energies={plane:beta*link_plaquette(plaquettes[plane])
                  for plane in PLANES}
        wilson_action=sum(energies.values(),F())
        # Euclidean d=4 metric derivative at g=I:
        # dS_W/dg_aa = 1/2 Σ E_ij - Σ_{j != a} E_aj.
        dw={a:wilson_action/2-sum(
            (energies[p] for p in PLANES if a in p),F())
            for a in AXES}
        if sum(dw.values(),F())!=0:
            raise ArithmeticError("Wilson d=4 conformal trace fails")
        sectors=c.get("sectors")
        if not isinstance(sectors,dict) or set(sectors)!=set(SECTORS):
            raise ValueError("complete E/R/B/vacuum sectors required")
        sector_base=F()
        sector_ds={a:F() for a in AXES}
        for s in SECTORS:
            entry=sectors[s]
            if set(entry)!=set(("action","diagonal_derivative")):
                raise ValueError("Each sector requires base action and four derivatives")
            metric=entry["diagonal_derivative"]
            if not isinstance(metric,dict) or set(metric)!=set(AXES):
                raise ValueError("Each sector requires 0,1,2,3 derivatives")
            sector_base+=f(entry["action"])
            for a in AXES:sector_ds[a]+=f(metric[a])
        refs=c.get("reference_log_derivative")
        if not isinstance(refs,dict) or set(refs)!=set(AXES):
            raise ValueError("reference measure score needed at all four axes")
        for a in AXES:
            reference_variation_totals[a]+=weight*f(refs[a])
        ds={a:dw[a]+sector_ds[a] for a in AXES}
        scores={a:f(refs[a])-ds[a] for a in AXES}
        action=wilson_action+sector_base
        density=exp_neg_interval(action,n)
        weighted=scale(weight,density)
        Z=add(Z,weighted)
        for a in AXES:
            DZ[a]=add(DZ[a],scale(scores[a],weighted))
        rows.append({"id":name,"wilson_action":str(wilson_action),
                     "complete_action":str(action),
                     "six_plaquette_energies":{p:str(x) for p,x in energies.items()},
                     "wilson_metric_derivative":{a:str(x) for a,x in dw.items()},
                     "sector_metric_derivative":{a:str(x) for a,x in sector_ds.items()},
                     "reference_measure_score":{a:str(f(refs[a])) for a in AXES},
                     "total_log_weight_derivative":{a:str(x) for a,x in scores.items()},
                     "density_interval":[str(x) for x in density],
                     "weighted_action_trace":str(sum(ds.values(),F()))})
    if totalweight!=1:
        raise ValueError("discrete reference weights must sum exactly to one")
    if any(v!=0 for v in reference_variation_totals.values()):
        raise ValueError("metric-dependent probability reference violates D_h integral 1 = 0")
    if Z[0]<=0:
        raise ArithmeticError("partition positivity enclosure failed")
    logderiv={a:div_pos(DZ[a],Z) for a in AXES}
    trace=I(F())
    for a in AXES:trace=add(trace,logderiv[a])
    # Stronger correlated enclosure, avoids independent intervals cancelling
    # poorly: integrate the same four diagonal log-weight scores.
    source_trace_num=I(F())
    for row in rows:
        original=next(c for c in configs if c["id"]==row["id"])
        ts=sum((f(row["total_log_weight_derivative"][a]) for a in AXES),F())
        density=tuple(f(x) for x in row["density_interval"])
        source_trace_num=add(source_trace_num,scale(f(original["reference_weight"])*ts,density))
    correlated_trace=div_pos(source_trace_num,Z)
    pure_wilson=all(
        all(f(e["action"])==0 and all(f(v)==0 for v in e["diagonal_derivative"].values())
            for e in c["sectors"].values())
        and all(f(x)==0 for x in c["reference_log_derivative"].values())
        for c in configs
    )
    if pure_wilson and correlated_trace!=(F(),F()):
        raise ArithmeticError("classical Wilson Weyl response must vanish exactly")
    return {
       "status":"six_plane_matrix_SU2_discrete_quadrature_rigorous_intervals",
       "source_identification":"bare_Wilson_plus_supplied_E_R_B_vacuum",
       "reference_measure":"finite_discrete_quadrature_not_SU2_Haar",
       "provenance":provenance,"bare_beta_SU2":str(beta),
       "n_configurations":len(configs),"taylor_terms":2*n,
       "partition_interval":[str(x) for x in Z],
       "partition_metric_derivative_interval":
           {a:[str(x) for x in DZ[a]] for a in AXES},
       "D_logZ_interval":{a:[str(x) for x in logderiv[a]] for a in AXES},
       "four_diagonal_sum_naive_interval":[str(x) for x in trace],
       "four_diagonal_correlated_trace_interval":[str(x) for x in correlated_trace],
       "bare_wilson_only_trace_exactly_zero":pure_wilson,
       "published_CMP119_measure_constructed":False,
       "full_SU2_Haar_quadrature_certified":False,
       "renormalized_Lorentzian_stress_identified":False,
       "accelerated_expansion_derived":False,
       "configuration_rows":rows
    }

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source",type=Path)
    parser.add_argument("--taylor-pairs",type=int,default=12)
    parser.add_argument("--out",type=Path)
    args=parser.parse_args()
    try:
        raw=args.source.read_bytes()
        result=one_point(json.loads(raw),args.taylor_pairs)
        result["input_sha256"]=hashlib.sha256(raw).hexdigest()
        rendering=json.dumps(result,indent=2,sort_keys=True)+"\n"
        if args.out:args.out.write_text(rendering)
        else:print(rendering,end="")
    except (ArithmeticError,ValueError,KeyError,TypeError,OSError) as err:
        print(f"FAIL-CLOSED: {err}",file=sys.stderr)
        return 2
    return 0
if __name__=="__main__":
    raise SystemExit(main())
