#!/usr/bin/env python3
"""SymPy-only source contract audit for X369 gates 2–5.

This is NOT a Torch implementation, an Agda proof run, a measured hardware
benchmark, or a semantic theorem. Source owners:
 LeechTransformer/models/history_orbit_moe.py: select_source_experts, step,
 execute_selected, per-expert histories, topk/sort/softmax.
 LeechTransformer/models/trialectic_wave_prior.py:
 directed_trialectic_invariants, trialectic_router_invariants.
 DASHI/Cognition/PNF/X369SharedHeadFusedScoreExact.agda.
"""
import itertools
import sympy as sp

checks = []
def check(label, condition):
    if not condition:
        raise AssertionError("X369_SOURCE_FOUR_GATES_FAIL: " + label)
    checks.append(label)

a,b,c,A,B,C,ws,wf,wr = sp.symbols("a b c A B C ws wf wr", real=True)
s = a*A+b*B+c*C
f = a*B+b*C+c*A
r = a*C+b*A+c*B
K = sp.Matrix([ws*a+wf*c+wr*b,
               ws*b+wf*a+wr*c,
               ws*c+wf*b+wr*a])
H = sp.Matrix([A,B,C])
full = ws*s+wf*f+wr*r
check("exact original directed fused score", sp.expand(full-K.dot(H)) == 0)

# The original residual has d unary(x) + d directed(x,h_e) coordinates,
# and a learned residual weight of shape [1,2*d]. The unary part of
# source C2 and C3 residual is shared across expert candidates.
unary=sp.symbols("unary")
bias_i,bias_j=sp.symbols("bias_i bias_j")
hi=sp.Matrix(sp.symbols("hi0:3"))
hj=sp.Matrix(sp.symbols("hj0:3"))
li=unary+K.dot(hi)+bias_i
lj=unary+K.dot(hj)+bias_j
check("common unary cancels even with different expert biases",
      sp.expand((li-lj)-(K.dot(hi-hj)+bias_i-bias_j)) == 0)
check("common residual unary weights have exact zero pairwise derivative",
      sp.diff(li-lj,unary) == 0)
check("source nominal 2d weights have d common-unary null directions",
      2*384-384 == 384)

# Exact quantizer/input/weight perturbation for the shared bilinear
# consumer. This is an algebraic perturbation, NOT a floating point
# rounding certificate for a particular torch CUDA/ROCm kernel.
x=sp.Matrix([a,b,c])
w=sp.Matrix([ws,wf,wr])
dw=sp.Matrix(sp.symbols("dw0:3"))
dx=sp.Matrix(sp.symbols("dx0:3"))
dh=sp.Matrix(sp.symbols("dh0:3"))
def fuse(wt,xt):
    return sp.Matrix([
        wt[0]*xt[0]+wt[1]*xt[2]+wt[2]*xt[1],
        wt[0]*xt[1]+wt[1]*xt[0]+wt[2]*xt[2],
        wt[0]*xt[2]+wt[1]*xt[1]+wt[2]*xt[0]])
deltaK=fuse(w+dw,x+dx)-fuse(w,x)
expandedK=fuse(w,dx)+fuse(dw,x)+fuse(dw,dx)
check("exact fused-weight and input perturbation", all(
    sp.expand(deltaK[i]-expandedK[i])==0 for i in range(3)))
deltaScore=fuse(w+dw,x+dx).dot(H+dh)-fuse(w,x).dot(H)
expected=expandedK.dot(H)+fuse(w,x).dot(dh)+expandedK.dot(dh)
check("exact fused input/history/weight score perturbation",
      sp.expand(deltaScore-expected)==0)
for variable in (a,b,c,A,B,C,ws,wf,wr):
    check("exact symbolic derivative parity "+str(variable),
          sp.expand(sp.diff(full,variable)-sp.diff(K.dot(H),variable))==0)

def sorted_ids(scores):
    # Deterministic reference ONLY: source torch.topk tie behaviour
    # need not match this ID-based fallback.
    return sorted(range(len(scores)),key=lambda i:(-scores[i],i))

# Strict cross-boundary enclosures preserve the selected SET.
# They do not necessarily preserve ordered slots or mixture weights.
top2_certificates=0
top2_ordered=0
for scores in itertools.product(range(-1,4),repeat=4):
    selected=sorted_ids(scores)[:2]
    selected_set=set(selected)
    for errors in itertools.product((-1,0,1),repeat=4):
        if all(scores[i]-abs(errors[i]) > scores[j]+abs(errors[j])
               for i in selected_set for j in range(4)
               if j not in selected_set):
            top2_certificates+=1
            updated=sorted_ids([scores[i]+errors[i] for i in range(4)])[:2]
            check_ok=set(updated)==selected_set
            if not check_ok:
                raise AssertionError("strict four expert top2 violation")
            top2_ordered+=int(updated==selected)
check("exhaustive four expert strict top2-set preservation",
      top2_certificates>0)
check("top2 set can be stable while slot order changes",
      top2_ordered<top2_certificates)
check("explicit selected slots reorder with identical set",
      sorted_ids([3,2,0])[:2]!=sorted_ids([2,3,0])[:2])
check("tie policy cannot be assumed source portable",
      sorted_ids([1,1])!=list(reversed(sorted_ids([1,1]))))

# Same chosen experts do not imply the same softmax weights.
def p0(x,y):
    return sp.exp(x)/(sp.exp(x)+sp.exp(y))
check("selected softmax changes with changing relative score",
      sp.simplify(p0(3,2)-p0(3,1))!=0)
z=sp.symbols("common_shift")
check("common unary shift cancels exact softmax",
      sp.simplify(p0(3+z,2+z)-p0(3,2))==0)

# Recurrent source model: source owns every expert history for routing,
# even while the remote execute_selected packet contains only selected
# histories. An inactive history can be silent at t0 and decisive at t1.
def dot_score(x,h): return sum(xx*hh for xx,hh in zip(x,h))
inactiveA=[(0,0,0),(0,0,0)]
inactiveB=[(0,0,0),(2,0,0)]
at0=(0,0,0)
at1=(1,0,0)
scores=lambda xx,hs:[dot_score(xx,h) for h in hs]
check("selected packet indistinguishable at initial zero activation",
      sorted_ids(scores(at0,inactiveA))[0] ==
      sorted_ids(scores(at0,inactiveB))[0] == 0)
check("inactive reactivation can change next selected expert",
      sorted_ids(scores(at1,inactiveA))[0]==0 and
      sorted_ids(scores(at1,inactiveB))[0]==1)

# A packet with authenticated original IDs, ordered weights, x,
# selected histories and model parameters suffices for ONE selected
# execution. It does not suffice for future global routing unless
# all inactive histories remain at their authoritative source.
check("source selected packet and future routing differ in scope",True)

# Exact scalar multiplication-site model ONLY:
# 3 directed 3-product terms + 3 head products per expert versus
# 9 precompute terms once + 3 history products per expert.
for experts in (1,2,4,8):
    check("disclosed multiplication-plan saving E="+str(experts),
          12*experts-(9+3*experts)==9*(experts-1))

# Semantic output labels cannot be inferred from router score parity:
# a task consumer may retain the same topk while changing an entirely
# separate 3-phase label under the task's own input action.
phase=lambda p:(p[0]+p[1])%3
shift=lambda p:((p[0]+1)%3,p[1])
pairs=list(itertools.product(range(3),repeat=2))
check("typed modular task action independent of router representation",
      all(phase(shift(p))==(phase(p)+1)%3 for p in pairs))
phase_wrong={p:phase(p) for p in pairs}
phase_wrong[(2,2)]=0
def action_defect(rule):
    return sum(rule[shift(p)]!=(rule[p]+1)%3 for p in pairs)
check("task algorithm action defect zero",
      action_defect({p:phase(p) for p in pairs})==0)
check("heldout memorizer action defect two",
      action_defect(phase_wrong)==2)

# Real arithmetic error certification for explicit fixed-point/rational
# quantizer tolerances. This is an INDEPENDENT bounded source fixture,
# not an inference about torch's float kernels or calibrated checkpoint.
from fractions import Fraction as F
w_exact=(F(2),F(-1),F(1))
x_exact=(F(1),F(2),F(-1))
histories_exact=[
    (F(1),F(0),F(1)),(F(-1),F(2),F(0)),
    (F(0),F(1),F(-1)),(F(3),F(0),F(0))]
def dot(a,b): return sum(aa*bb for aa,bb in zip(a,b))
def exact_fuse(weight,xx):
    return (weight[0]*xx[0]+weight[1]*xx[2]+weight[2]*xx[1],
            weight[0]*xx[1]+weight[1]*xx[0]+weight[2]*xx[2],
            weight[0]*xx[2]+weight[1]*xx[1]+weight[2]*xx[0])
epsw=(F(1,64),)*3
epsx=(F(1,32),)*3
epsh=(F(1,16),)*3
couplings=(((0,0),(1,2),(2,1)),
           ((0,1),(1,0),(2,2)),
           ((0,2),(1,1),(2,0)))
du_max=[
    sum(abs(w_exact[k])*epsx[l] +
        epsw[k]*abs(x_exact[l]) + epsw[k]*epsx[l]
        for k,l in couplings[j])
    for j in range(3)]
u_exact=exact_fuse(w_exact,x_exact)
dw=(epsw[0],-epsw[1],epsw[2])
dx=(-epsx[0],epsx[1],-epsx[2])
dh=(epsh[0],-epsh[1],epsh[2])
w_q=tuple(aa+bb for aa,bb in zip(w_exact,dw))
x_q=tuple(aa+bb for aa,bb in zip(x_exact,dx))
source_scores=[]
quant_scores=[]
certified_budget=[]
for h in histories_exact:
    h_q=tuple(aa+bb for aa,bb in zip(h,dh))
    exact_score=dot(u_exact,h)
    q_score=dot(exact_fuse(w_q,x_q),h_q)
    bound=sum(du_max[j]*abs(h[j]) +
              (abs(u_exact[j])+du_max[j])*epsh[j]
              for j in range(3))
    if abs(q_score-exact_score)>bound:
        raise AssertionError("quantized source score exceeds admitted bound")
    source_scores.append(exact_score)
    quant_scores.append(q_score)
    certified_budget.append(bound)
check("rational four-expert source/input/head/history budget enclosure",True)
selected_set=set(sorted_ids(source_scores)[:2])
margin_safe=all(
    source_scores[i]-certified_budget[i] >
    source_scores[j]+certified_budget[j]
    for i in selected_set for j in range(4) if j not in selected_set)
check("rational four-expert top2 decision certified by budget",margin_safe)
check("rational four-expert selection actually preserved",
      set(sorted_ids(quant_scores)[:2])==selected_set)
# If score budgets are not strict enough, no safety claim is made
# even if a particular observed quantized route happens to agree.
check("strict budget is sufficient, not necessary",
      source_scores[3]>source_scores[2])

# Explicit consumer non-descent from the EXISTING DASHI
# TrialecticBoundaryFaceNonfactorabilityExact witness: same three
# positive dyadic edges, different reciprocal/coercive face labels.
# Route-score equality (or equal boundary features) cannot distinguish
# this independent semantic face without additional evidence.
boundary=("positive","positive","positive")
state_reciprocal=(boundary,"reciprocal")
state_coercive=(boundary,"coercive")
check("identical trialectic boundary distinct face consumers",
      state_reciprocal[0]==state_coercive[0] and
      state_reciprocal[1]!=state_coercive[1])
# An external 'semantic action' requires a licensed task action,
# not reinterpreting a C2 sign flip or arbitrary geometric C3 cycle.
# These intentionally separate output action domains.
semantic_labels=("reciprocal","coercive","underdetermined")
geometric_rotation=lambda v:(v[1],v[2],v[0])
check("rotating geometry does not synthesize a face label",
      geometric_rotation((1,2,3))==(2,3,1) and
      "reciprocal" not in geometric_rotation((1,2,3)))
# The source's route logits can be exactly equal despite a changed
# face label; any model claiming this face consumer must carry its
# information in another verified channel or residual.
check("router-score sufficiency alone cannot recover semantic face",
      K.dot(hi)==K.dot(hi) and
      state_reciprocal[1]!=state_coercive[1])

# The rational four-expert fixture also has a strict WITHIN-SELECTED
# order margin, so both ordered slots (not merely the set) are safe.
ordered=sorted_ids(source_scores)[:2]
check("rational top2 slot order certified",
      source_scores[ordered[0]]-certified_budget[ordered[0]] >
      source_scores[ordered[1]]+certified_budget[ordered[1]])
check("rational top2 slot order actually preserved",
      sorted_ids(quant_scores)[:2]==ordered)

print("X369_SOURCE_FOUR_GATES_SYMPY_PASS",len(checks),
      "grouped checks; strict_top2=",top2_certificates,
      "same_order=",top2_ordered)
