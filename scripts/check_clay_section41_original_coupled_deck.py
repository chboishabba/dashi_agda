#!/usr/bin/env python3
"""Section41 exact ORIGINAL coupled six-deck and causal-bit controls.

Uses exact rational arithmetic; tests the SAME source Q0(a,s),
dField(a,s) and all SIX addresses. The squared derivative profile
and SIGNED SIXFOLD PRODUCT both survive simultaneous root partnering.
A five-address negative control demonstrates that the product
orientation would change with ODD parity (unless product is zero).

Also finite-checks the original anchored/paired Boolean clock
under an explicit addressed-bit observation ABI. No native Lean
or Agda kernel, global Hodge Chow, or P-vs-NP proof is claimed.
"""
from fractions import Fraction as Q
from itertools import product

counts = {"Hodge_Q0_profile": 0, "Hodge_coupled_delta": 0,
          "Hodge_odd_negative": 0, "Hodge_free_puncture": 0,
          "Hodge_fold_negative": 0, "PNP_bit_clock": 0}

def q0(a, s):
    return -3*a**3 -3*a*a*s-a*a+3*a*s+3*a-2*s*s+s+3

def derivative(a,s):
    return -3*a*a+3*a+1-4*s

def partner(a,s):
    return s+derivative(a,s)/2

def mul(xs):
    out=Q(1)
    for x in xs: out*=x
    return out

# Exact rational source values; includes negative, zero and positive
# polynomial addresses and both sheets away from the fold.
addresses=(Q(-1),Q(0),Q(1,2),Q(1),Q(3,2),Q(2))
coords=(Q(-1,3),Q(0),Q(1,4),Q(3,4),Q(-2,5),Q(5,7))
for shift in range(13):
    a=tuple(addresses[(i+shift)%6] for i in range(6))
    s=tuple(coords[(i+2*shift)%6] for i in range(6))
    t=tuple(partner(ai,si) for ai,si in zip(a,s))
    for ai,si,ti in zip(a,s,t):
        assert q0(ai,ti)==q0(ai,si)
        assert derivative(ai,ti)==-derivative(ai,si)
        assert derivative(ai,ti)**2==derivative(ai,si)**2
        assert partner(ai,ti)==si
        counts["Hodge_Q0_profile"]+=4
    old=mul(derivative(ai,si) for ai,si in zip(a,s))
    new=mul(derivative(ai,ti) for ai,ti in zip(a,t))
    assert new==old
    counts["Hodge_coupled_delta"]+=1
    oldfive=mul(derivative(ai,si) for ai,si in zip(a[:5],s[:5]))
    newfive=mul(derivative(ai,ti) for ai,ti in zip(a[:5],t[:5]))
    assert newfive==-oldfive
    if oldfive: assert newfive!=oldfive
    counts["Hodge_odd_negative"]+=1+(oldfive!=0)

# Actual coupled original six-root incidence sample with a_i=0,
# y_i=3 and signed derivative product delta=1; root 0 and 1/2
# both satisfy Q0(0,s)=3, and the sixfold partner preserves delta.
a=(Q(0),)*6
s=(Q(0),)*6
t=tuple(partner(ai,si) for ai,si in zip(a,s))
assert all(q0(ai,si)==Q(3) and q0(ai,ti)==Q(3)
           for ai,si,ti in zip(a,s,t))
assert mul(derivative(ai,si) for ai,si in zip(a,s))==Q(1)
assert mul(derivative(ai,ti) for ai,ti in zip(a,t))==Q(1)
counts["Hodge_coupled_delta"]+=3

# A complete, original coupled Q0(a,s)=y+a^7/y fibre sample
# with all a_i=0, y_i=3, s_i∈{0,1/2}. Every derivative is ±1,
# so δ is genuinely nonzero and the sixfold partner has NO fixed
# point on any of the 2^6 legal signed-root sheets.
for choices in product((0,1),repeat=6):
    a=(Q(0),)*6
    y=(Q(3),)*6
    s=tuple(Q(b,2) for b in choices)
    t=tuple(partner(ai,si) for ai,si in zip(a,s))
    delta=mul(derivative(ai,si) for ai,si in zip(a,s))
    assert all(q0(ai,si)==yi and q0(ai,ti)==yi
               for ai,yi,si,ti in zip(a,y,s,t))
    assert delta != 0
    assert mul(derivative(ai,ti) for ai,ti in zip(a,t))==delta
    assert t!=s
    assert tuple(partner(ai,ti) for ai,ti in zip(a,t))==s
    counts["Hodge_free_puncture"]+=5

# The δ≠0 hypothesis is REAL: all six branch roots s=1/4 at
# a=0 have dField=0 and the partner fixes the same original root.
branch=(Q(1,4),)*6
assert all(derivative(Q(0),si)==0 for si in branch)
assert mul(derivative(Q(0),si) for si in branch)==0
assert tuple(partner(Q(0),si) for si in branch)==branch
counts["Hodge_fold_negative"]+=3

# Deterministic 1-bit source programs, explicit addressed input-bit
# observations and original terminal clock k. If outputs diverge,
# some address read before terminal must have different input value.
for n in (1,2,3):
    for x in product((0,1),repeat=n):
        for y in product((0,1),repeat=n):
            for transition in product((0,1),repeat=4):
                def step(state,bit):
                    return transition[2*state+bit]
                statex=statey=0
                seen=False
                for k in range(1,n+2):
                    address=(k-1)%n
                    seen |= x[address]!=y[address]
                    statex=step(statex,x[address])
                    statey=step(statey,y[address])
                    if statex!=statey:
                        assert seen
                        assert any(x[j%n]!=y[j%n] for j in range(k))
                        counts["PNP_bit_clock"]+=2
assert not list(range(0))
print("SECTION41 ORIGINAL COUPLED EXACT PASS",counts,
      "TOTAL",sum(counts.values()))
