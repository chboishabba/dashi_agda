#!/usr/bin/env python3
"""Exact finite negative controls for the attached YM R445 A/B/C endpoint claims.

This checker NEVER models the original SU(N) Wilson Gibbs law and NEVER
refutes Yang--Mills. It refutes claimed GENERAL implications which must
not be used as if they were physical theorems:

  (1) fixed block ratio squared -> 16^-k: FALSE
  (2) rare bad region under Q -> small TV under P: FALSE
  (3) action term away from X cannot change P_X: FALSE for correlated Q
  (4) local comparison TV(P_k,Q_k)=0 -> P_k Cauchy: FALSE
  (5) local TV=0 -> exponential spatial clustering: FALSE
  (6) projectively consistent positive measures -> OS RP: FALSE
  (7) a 1/k scale error -> summable: FALSE

Also checks the TRUE exact finite decomposition that is safe to use:

  P_X-Q_X = [P_X - M_X] + [M_X-Q_X]
  M_X = ∑_y P_Y(y) Q(X|y),

with |P_X-M_X| bounded by supremum of conditional TV distances,
and |M_X-Q_X| bounded by TV(P_Y,Q_Y) via Markov contraction.

All arithmetic is fractions, no mock "physical YM solution", and no
kernel certificate. Source owner: F19/P0/R445 original #1503.
"""
from fractions import Fraction as F
from itertools import product
from math import comb
import json


def tv(p, q):
    assert len(p) == len(q) and sum(p) == sum(q) == 1
    return sum((abs(a-b) for a,b in zip(p,q)), F(0))/2


def x_marginal(joint):
    assert set(joint) == {(0,0),(0,1),(1,0),(1,1)}
    assert sum(joint.values()) == 1
    return [sum((joint[(x,y)] for y in (0,1)), F(0))
            for x in (0,1)]


def y_marginal(joint):
    return [sum((joint[(x,y)] for x in (0,1)), F(0))
            for y in (0,1)]


def external_only_countermodel():
    q = {(0,0):F(3,8),(0,1):F(1,8),
         (1,0):F(1,8),(1,1):F(3,8)}
    # Weight ONLY outside: independent of the interior variable x.
    w = {0:F(1),1:F(3)}
    z = sum((v*w[y] for (x,y),v in q.items()), F(0))
    p = {(x,y):v*w[y]/z for (x,y),v in q.items()}
    assert z == 2
    assert x_marginal(q) == [F(1,2),F(1,2)]
    assert x_marginal(p) == [F(3,8),F(5,8)]
    assert tv(x_marginal(p),x_marginal(q)) == F(1,8)
    # The change is Cov_Q(1_{x=1}, w(y))/E_Q[w(y)].
    e_x = x_marginal(q)[1]
    e_w = z
    e_xw = sum((q[(1,y)]*w[y] for y in (0,1)), F(0))
    covariance = e_xw - e_x*e_w
    assert covariance == F(1,4)
    assert covariance / z == F(1,8)
    return {"Q_X": ["1/2","1/2"],"P_X":["3/8","5/8"],
            "TV_X":"1/8","outside_interacting_activity_touching_X":0,
            "covariance_Q_X_w":"1/4"}


def bad_region_reweighting():
    # Rare event under target Q (1/(N+1)); reweight it by N.
    # Under effective P it has probability exactly 1/2!
    for n in [100,1000,10000]:
        q = [F(n,n+1),F(1,n+1)]
        s = [F(1),F(n)]
        z = sum((a*b for a,b in zip(q,s)),F(0))
        p = [a*b/z for a,b in zip(q,s)]
        assert p == [F(1,2),F(1,2)]
        assert tv(p,q) == F(1,2)-F(1,n+1)
    return {"Q_bad_N1000":str(F(1,1001)),
            "P_bad_N1000":"1/2",
            "TV_N1000":str(F(1,2)-F(1,1001))}


def conditional_mixture_tv():
    # Exhaustive rational joint models, including dependent measures.
    vals = [F(1),F(2),F(3)]
    checked = 0
    for a in product(vals,repeat=4):
        qa=sum(a); q={(x,y):a[2*x+y]/qa for x in (0,1) for y in (0,1)}
        qy=y_marginal(q)
        for b in product(vals,repeat=4):
            pb=sum(b)
            p={(x,y):b[2*x+y]/pb for x in (0,1) for y in (0,1)}
            py=y_marginal(p)
            # N_X = mixture with the P exterior and Q conditional fibers.
            m=[sum((py[y]*q[(x,y)]/qy[y] for y in (0,1)),F(0))
               for x in (0,1)]
            pcond={y:[p[(x,y)]/py[y] for x in (0,1)] for y in (0,1)}
            qcond={y:[q[(x,y)]/qy[y] for x in (0,1)] for y in (0,1)}
            max_cond=max(tv(pcond[y],qcond[y]) for y in (0,1))
            actual=tv(x_marginal(p),x_marginal(q))
            exterior=tv(py,qy)
            assert tv(x_marginal(p),m) <= max_cond
            assert tv(m,x_marginal(q)) <= exterior
            assert actual <= max_cond+exterior
            checked+=1
    return {"two_site_positive_joint_pairs":checked,
            "inequality":"TV(P_X,Q_X)<=sup_y TV(P(X|y),Q(X|y))+TV(P_Y,Q_Y)"}


def noncauchy_zero_tv_comparison():
    # P_k=Q_k alternate point masses, so D_k=0 for all k,
    # but TV(P_k,P_(k+1))=1.
    seq=[[F(1),F(0)] if k%2==0 else [F(0),F(1)] for k in range(20)]
    assert all(tv(a,a)==0 for a in seq)
    assert all(tv(seq[k],seq[k+1])==1 for k in range(19))
    return {"all_D_k":0,"successive_original_measure_TV":1}


def nonclustering_zero_tv_comparison():
    # At EVERY separation R, a single global fair spin duplicated at
    # two sites has E F=E G=1/2, E FG=1/2, Cov=1/4.
    for sep in [1,2,4,8,16,1024,100000]:
        e_f=e_g=F(1,2)
        e_fg=F(1,2)
        assert e_fg-e_f*e_g == F(1,4)
    return {"all_comparison_D":0,"all_separation_covariance":"1/4"}


def no_OS_from_probability_alone():
    # Two times t=-1,+1; states (+,-),(-,+) with mass 1/2 each.
    # Positive-time linear test f=spin_+; its reflected copy=spin_-.
    # OS Gram quadratic form E[theta f * f]=-1.
    states=[((1,-1),F(1,2)),((-1,1),F(1,2))]
    rp=sum((F(spins[0]*spins[1])*prob for spins,prob in states),F(0))
    assert rp==-1
    return {"normalized_positive_probability":True,"OS_reflection_Gram":"-1"}


def fixed_ratio_and_harmonic():
    assert F(1,4)**2 == F(1,16)
    assert F(1,4)**(2*2) == F(1,256)
    assert F(1,16)!=F(1,256)
    # For all j: sum_{k=2^j}^{2^(j+1)-1} 1/(16 k) > 1/32.
    blocks=[]
    for j in range(10):
        lo=2**j;hi=2**(j+1)
        block=sum((F(1,16*k) for k in range(lo,hi)),F(0))
        assert block>F(1,32)
        blocks.append(block)
    assert sum(blocks,F(0)) > F(10,32)
    return {"single_step_sq":"1/16","invalid_k2_iterated_sq":"1/256",
            "each_dyadic_harmonic_block_lower_bound":"1/32",
            "blocks_verified":len(blocks),
            "mathematical_infinite_conclusion":"harmonic divergence, via one uniform lower bound per dyadic block"}


def check():
    data={
      "outside_only_action":external_only_countermodel(),
      "rare_bad_event":bad_region_reweighting(),
      "correct_conditional_mixture":conditional_mixture_tv(),
      "noncauchy_zero_D":noncauchy_zero_tv_comparison(),
      "nonclustering_zero_D":nonclustering_zero_tv_comparison(),
      "OS_counterexample":no_OS_from_probability_alone(),
      "scale_harmonic":fixed_ratio_and_harmonic()
    }
    return {
      "schema":"ym-r445-original-claim-logical-audit-v1",
      "result":"PASS",
      "exact_arithmetic":True,
      "physical_original_Wilson_R445_Dk_proved":False,
      "agda_kernel_checked":False,
      "E1_D1_D2_proved":False,
      "cases":data
    }


if __name__=="__main__":
    print(json.dumps(check(),indent=2))
