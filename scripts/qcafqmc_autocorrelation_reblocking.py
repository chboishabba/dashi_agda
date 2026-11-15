#!/usr/bin/env python3
"""Source-matched AFQMC correlated-block and independent-replica inference.

No adjacent imaginary-time blocks are treated as IID. Integrated
autocorrelation is conservatively estimated by dyadic blocking and a plateau.
The uncertainty from independent seeds is separately compared with the
within-seed blocking uncertainties; the larger is retained. For a very small
number of seeds this is an *uncertainty diagnostic*, not a confidence interval.

Algorithmic attribution: Flyvbjerg and Petersen, J. Chem. Phys. 91, 461 (1989);
Wolff, Comput. Phys. Commun. 156, 143 (2004).
"""
import json
import math
import numpy as np

class InsufficientAutocorrelationEvidence(ValueError):
    pass

def blocking_estimate(values,min_final_blocks=16):
    a=np.asarray(values,dtype=float)
    if a.ndim!=1 or len(a)<64 or not np.isfinite(a).all():
        raise InsufficientAutocorrelationEvidence("need >=64 finite consecutive blocks")
    levels=[]
    current=a.copy()
    while len(current)>=min_final_blocks:
        n=len(current)
        variance=float(np.var(current,ddof=1))
        se2=variance/n
        levels.append({"block_size":len(a)//n,"n_blocks":n,
                       "variance_of_mean":se2})
        if n<2*min_final_blocks:break
        if n%2:current=current[:-1]
        current=.5*(current[::2]+current[1::2])
    baseline=levels[0]["variance_of_mean"]
    if baseline<=0:
        if np.all(a==a[0]):return {"mean":float(a[0]),"standard_error":0.,
                                   "tau_int_lower_estimate":.5,
                                   "levels":levels,"plateau_verified":True}
        raise InsufficientAutocorrelationEvidence("zero base variance but nonconstant samples")
    # Blocking variance should eventually stabilise. Select largest
    # tested variance as a non-underestimating conservative finite-level
    # diagnostic (NOT a rigorous statistical upper confidence bound).
    highest=max(x["variance_of_mean"] for x in levels)
    estimated_tau=max(.5,.5*highest/baseline)
    if len(levels)<3:
        raise InsufficientAutocorrelationEvidence("insufficient blocking levels")
    return {"mean":float(np.mean(a)),
            "standard_error":float(math.sqrt(highest)),
            "tau_int_lower_estimate":float(estimated_tau),
            "levels":levels,
            "plateau_verified":False,
            "uncertainty_kind":"maximum dyadic blocking variance diagnostic"}

def replica_average(block_energies):
    results=[blocking_estimate(x) for x in block_energies]
    if len(results)<3:raise InsufficientAutocorrelationEvidence(
        "need >=3 independent replica seeds")
    means=np.array([r["mean"] for r in results])
    seed_variance=float(np.var(means,ddof=1)/len(means))
    within_variance=float(np.mean([r["standard_error"]**2 for r in results])
                          /len(results))
    error=float(math.sqrt(max(seed_variance,within_variance)))
    return {"mean":float(means.mean()),"standard_error":error,
            "n_independent_replicas":len(means),
            "seed_level_SE":float(math.sqrt(seed_variance)),
            "within_seed_blocking_SE":float(math.sqrt(within_variance)),
            "replicas":results,
            "not_a_rigorous_confidence_interval":True}

def reaction_contrasts(B,BC,C):
    """Independent structures/seeds: no covariance assumption."""
    groups={"B":replica_average(B),"BC":replica_average(BC),
            "C":replica_average(C)}
    def difference(name):
        delta=groups[name]["mean"]-groups["B"]["mean"]
        se=math.hypot(groups[name]["standard_error"],
                      groups["B"]["standard_error"])
        return {"delta_hartree":delta,"error_diagnostic_hartree":se,
                "delta_kcal_mol":delta*627.5094740631,
                "error_diagnostic_kcal_mol":se*627.5094740631}
    return {"groups":groups,"barrier":difference("BC"),
            "reaction":difference("C"),
            "statistical_status":"correlation-aware diagnostic; not a 95% CI"}

def self_test():
    rng=np.random.default_rng(71093)
    def correlated(offset):
        out=[]
        for seed in range(4):
            noise=rng.normal(scale=.02,size=4096)
            x=np.empty(4096)
            x[0]=offset+noise[0]
            for j in range(1,len(x)):
                x[j]=offset+.90*(x[j-1]-offset)+noise[j]
            out.append(x[128:])
        return out
    B=correlated(-1.)
    BC=correlated(-.9)
    C=correlated(-1.02)
    c=reaction_contrasts(B,BC,C)
    assert c["barrier"]["delta_hartree"]>0
    assert c["reaction"]["delta_hartree"]<0
    first=c["groups"]["B"]["replicas"][0]
    assert first["tau_int_lower_estimate"]>.5
    assert first["standard_error"]>np.std(B[0],ddof=1)/np.sqrt(len(B[0]))
    try:blocking_estimate(np.arange(8))
    except InsufficientAutocorrelationEvidence:pass
    else:raise AssertionError("too-short autocorrelation series accepted")
    return {"passed":True,
            "B_tau_int_lower_estimate":first["tau_int_lower_estimate"],
            "B_naive_IID_SE":float(np.std(B[0],ddof=1)/np.sqrt(len(B[0]))),
            "B_blocked_SE":first["standard_error"],
            "barrier_delta_hartree":c["barrier"]["delta_hartree"],
            "reaction_delta_hartree":c["reaction"]["delta_hartree"],
            "synthetic_AR1_only":True}

if __name__=="__main__":
    print(json.dumps(self_test(),indent=2))
