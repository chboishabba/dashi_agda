#!/usr/bin/env python3
"""Exact original R4 coherent topk-load envelope (source-legal synthetic params).

Strict source score order on the ENTIRE nonnegative REAL load ray,
not merely four observed loads. Uses exact SymPy rational polynomials.

Original source owners: LeechTransformer/models/history_orbit_moe.py
and trialectic_wave_prior.py, with constant expert FFN outputs
(0,1,0,0), head/histories/source score weights as disclosed in
scripts/check_x369_r4_topk_kink_sympy.py.

Proves selected-set breakpoint regime and selected-output formula,
including a unique real analytical crest at t=19/9; distinguishes
continuous-output harmless tie surfaces from cutoff tie t=14/5,
whose output is intrinsically source-selection ambiguous.
This is NOT a trained checkpoint, Torch rounding or Agda kernel proof.
"""
import sympy as S
R=S.Rational
checks=[]
def chk(label,cond):
    if not bool(cond):
        raise AssertionError("R4_FULL_LOAD_ENVELOPE_FAIL "+label)
    checks.append(label)
t=S.symbols("t",real=True,nonnegative=True)
slopes=[0,4,9,11]
bias=[8,3,-11,-16]
L=[S.Integer(b)+S.Integer(s)*t for b,s in zip(bias,slopes)]
output=[0,1,0,0]
cutpoints=[R(0),R(5,4),R(19,9),R(5,2),R(19,7),R(14,5)]
regions=[
    (cutpoints[0],cutpoints[1],(0,1)),
    (cutpoints[1],cutpoints[2],(1,0)),
    (cutpoints[2],cutpoints[3],(1,2)),
    (cutpoints[3],cutpoints[4],(1,3)),
    (cutpoints[4],cutpoints[5],(3,1)),
    (cutpoints[5],S.oo,(3,2)),
]
def chosen_response(pair):
    denom=sum(S.exp(L[i]) for i in pair)
    return S.simplify(sum(output[i]*S.exp(L[i]) for i in pair)/denom)
def margin_fn(i,j):
    return S.expand(L[i]-L[j])
def ordered_route_at(q):
    vals=[line.subs(t,q) for line in L]
    return tuple(sorted(range(4),key=lambda i:(-vals[i],i))[:2])
def verify_open_region(left,right,pair):
    i,j=pair
    excluded=[e for e in range(4) if e not in pair]
    for high,low in [(i,j)]+[(j,k) for k in excluded]:
        gap=margin_fn(high,low)
        if right==S.oo:
            chk(f"ray endpoint {left}: {high}>{low}",
                gap.subs(t,left)>=0 and
                S.diff(gap,t)>=0 and
                (gap.subs(t,left)>0 or S.diff(gap,t)>0))
        else:
            mid=(left+right)/2
            chk(f"open interval {left}-{right}: {high}>{low}",
                gap.subs(t,left)>=0 and gap.subs(t,right)>=0
                and gap.subs(t,mid)>0)
    mid=left+1 if right==S.oo else (left+right)/2
    chk(f"chosen strict topk {left}-{right}",
        ordered_route_at(mid)==pair)

for left,right,pair in regions:
    verify_open_region(left,right,pair)
responses=[chosen_response(ids) for _,_,ids in regions]
logistic=lambda z:1/(1+S.exp(-z))
expected=[
    logistic(4*t-5),logistic(4*t-5),
    logistic(14-5*t),logistic(19-7*t),
    logistic(19-7*t),S.Integer(0)]
for (left,right,pair),y,z in zip(regions,responses,expected):
    chk(f"exact source scalar mixture on {left}-{right}",
        S.simplify(y-z)==0)
# On strict open regions, the ordinary derivative sign is
# positive up to 19/9, negative from 19/9 until 14/5,
# and identically zero after the selection collapse.
for n,z in enumerate(expected):
    # Keep derivative unreduced: sympy.simplify may rewrite logistic
    # derivatives to cosh forms that a later simplify cannot cancel.
    dz=S.diff(z,t)
    if n<2:
        chk(f"strict initial facilitation derivative {n}",
            S.cancel(S.together(dz-4*z*(1-z)))==0)
    elif n<3:
        chk(f"first decline derivative {n}",
            S.cancel(S.together(dz+5*z*(1-z)))==0)
    elif n<5:
        chk(f"overload competition decline derivative {n}",
            S.cancel(S.together(dz+7*z*(1-z)))==0)
    else:
        chk("collapsed source output is zero after final cutoff",dz==0)
# Cusp at first replacement has matching response but opposite
# one-sided derivatives: piecewise continuous, not smooth.
crest=R(19,9)
crest_differential=R(31,9)
chk("exact crest gaps",
    S.simplify((L[1]-L[0]).subs(t,crest)-crest_differential)==0
    and S.simplify((L[1]-L[2]).subs(t,crest)-crest_differential)==0)
crest_y=logistic(crest_differential)
chk("first replacement continuous response",
    S.simplify(expected[1].subs(t,crest)-crest_y)==0
    and S.simplify(expected[2].subs(t,crest)-crest_y)==0)
chk("crest derivative jump sign",
    S.diff(expected[1],t).subs(t,crest)>0
    and S.diff(expected[2],t).subs(t,crest)<0)
# A change of tie order at 5/4 and 19/7 changes only sorted
# slot positions, not the selected set/weighted output.
for bound,left_region,right_region in [
    (R(5,4),0,1),(R(19,7),3,4)]:
    chk("slot tie leaves output invariant at "+str(bound),
        S.simplify(expected[left_region].subs(t,bound)
        -expected[right_region].subs(t,bound))==0)
# At 5/2, the two zero-output competitors tie:
# the source output is still well-defined although IDs are not.
chk("zero-output competitor tie has continuous scalar source output",
    S.simplify(expected[2].subs(t,R(5,2))
        -expected[3].subs(t,R(5,2)))==0)
# At 14/5 the contributing e1 and zero-output e2 tie for
# SECOND place behind e3. torch.topk has unspecified tie choice.
cut=R(14,5)
left_limit=S.simplify(expected[4].subs(t,cut))
right_limit=S.simplify(expected[5].subs(t,cut))
chk("final cutoff has genuinely output-changing tie",
    S.simplify(left_limit-logistic(-R(3,5)))==0
    and right_limit==0 and left_limit>0)
chk("at final cutoff second slot is tied",
    (L[1]-L[2]).subs(t,cut)==0
    and (L[3]-L[1]).subs(t,cut)>0)
# Strictly sampled four-load original ResponseKink profile remains.
for q,ids,nat in [(0,(0,1),0),(1,(0,1),2),
                  (2,(1,0),9),(3,(3,2),0)]:
    chk("source four-load route "+str(q),
        ordered_route_at(R(q))==ids)
    score=chosen_response(ids).subs(t,q)
    chk("source Nat four-load "+str(q),
        int(S.floor(10*score.evalf(60)))==nat)
# Mechanistic negative control: forcing pair 0,1 for all
# positive loads gives logistic(4t-5) with strictly positive
# derivative; hence no overload limb without selected changes.
forced=chosen_response((0,1))
chk("fixed-route source output monotone all nonnegative loads",
    S.simplify(forced-logistic(4*t-5))==0
    and S.cancel(S.together(S.diff(forced,t)-4*forced*(1-forced)))==0)
print("X369_R4_FULL_LOAD_ENVELOPE_SYMPY_PASS",len(checks))
print("FULL_LOAD_STRICT_REGIMES")
for left,right,pair in regions:
    print(str(left),str(right),pair,str(chosen_response(pair)))
print("CREST",str(crest),"response",S.N(crest_y,15))
print("FINAL_TOPK_TIE",str(cut),"left",S.N(left_limit,15),
      "right",str(right_limit),"tie_not_certifiable")
