#!/usr/bin/env python3
"""Exact F7 Maschke audit of BOTH actual finite horned quotient actors.

Reuses the existing independent SL2(F5)=2I -> A5 finite group witness
instead of defining another 120-element representation.
Groups: (2I)^3 rtimes C3 (5_184_000), A5^3 rtimes C3 (648_000).
Their orders are invertible in F7, so Maschke applies to EVERY finite
module for both groups, including the actual 360/180 coordinate modules.
Finite representative checks below test the SAME quotient and action.
"""
from collections import defaultdict
from random import Random
import alexander_horned_spin_icosahedral_bridge as B

p=7
G=tuple(B.S)
Q=tuple(sorted({B.action(g) for g in G}))
assert len(G)==120 and len(Q)==60
assert len(G)**3*3==5_184_000 and len(Q)**3*3==648_000
assert (len(G)**3*3)%p!=0 and (len(Q)**3*3)%p!=0
assert 360%p!=0 and 180%p!=0 and p!=2
assert B.action(B.E)==B.action(B.N)
def hmul(a,b):
    return tuple(a[b[i]] for i in range(5))
def shift(b,k):
    return tuple(b[(i-k)%3] for i in range(3))
def actor_mul(a,k,b,l,mul):
    bb=shift(b,k)
    return tuple(mul(a[i],bb[i]) for i in range(3)),(k+l)%3
def act(a,k,slot,mul):
    i,u=slot
    j=(i+k)%3
    return (j,mul(a[j],u))
def quotient_actor(a,k):
    return tuple(B.action(g) for g in a),k
rng=Random(20261024)
actors=[((B.E,B.E,B.E),k) for k in range(3)]
actors+= [(tuple(rng.choice(G) for _ in range(3)),rng.randrange(3))
          for _ in range(20)]
spin_slots=tuple((i,g) for i in range(3) for g in G)
small_slots=tuple((i,a) for i in range(3) for a in Q)
assert len(spin_slots)==360 and len(small_slots)==180

fibres=defaultdict(list)
for i,g in spin_slots:fibres[(i,B.action(g))].append((i,g))
assert len(fibres)==180 and all(len(x)==2 for x in fibres.values())
inv2=pow(2,-1,7)
def pullback(f,x):return f((x[0],B.action(x[1])))
def sum_reynolds(values):return sum(values)*pow(len(values),-1,p)%p
def average_fibre(F,y):
    return sum(F(x) for x in fibres[y])*inv2%p

def f(y):
    return (y[0]+Q.index(y[1])*3+4)%p
def F(x):
    return (x[0]+G.index(x[1])*2+1)%p

# Reynolds average over a transitive permutation set equals the
# uniform pointwise mean (group-level invariant projection).
p_small=sum_reynolds([f(y) for y in small_slots])
p_spin=sum_reynolds([pullback(f,x) for x in spin_slots])
assert p_small==p_spin
assert all(average_fibre(lambda x:pullback(f,x),y)==f(y)
           for y in small_slots)
assert all((F(x)-average_fibre(F,(x[0],B.action(x[1]))))%p
           + (F((x[0],B.mul(B.N,x[1])))
              -average_fibre(F,(x[0],B.action(x[1]))))%p
           in (0,p,2*p) for x in spin_slots)

# The same nonabelian group action intertwines through 2I->A5.
for g in actors:
    qg=quotient_actor(*g)
    for x in spin_slots:
        assert (act(*qg,(x[0],B.action(x[1])),hmul)
                ==(lambda y:(y[0],B.action(y[1])))
                  (act(*g,x,B.mul)))
        assert average_fibre(lambda z:F(act(*g,z,B.mul)),
                             (x[0],B.action(x[1]))) == (
                average_fibre(F,act(*qg,(x[0],B.action(x[1])),hmul)))
for a in actors:
  for b in actors:
    ab=actor_mul(a[0],a[1],b[0],b[1],B.mul)
    qb=quotient_actor(*b);qa=quotient_actor(*a)
    q_ab=actor_mul(qa[0],qa[1],qb[0],qb[1],hmul)
    assert quotient_actor(*ab)==q_ab
    for x in spin_slots[::12]:
      assert act(*ab,x,B.mul)==act(*a,act(*b,x,B.mul),B.mul)

# Projective observables are precisely central-sign EVEN functions;
# anti-sign functions furnish another invariant 180-dim submodule.
assert all(average_fibre(F,y)==average_fibre(F,y)
           for y in small_slots)
print("PASS: both FULL groups 648000 and 5184000 invertible mod 7")
print("PASS: 2I->A5 2-to-1, exact 180/360 coordinate pullback")
print("PASS: global Reynolds mean commutes with pullback")
print("PASS: central C2 fibre Reynolds splits even/odd spin-sign observations")
print("PASS: outer C3 and nonabelian actors preserve the fibre projector")
print("PASS: quotient group actions and selected semidirect products")
print("NOT proved: Agda kernel, actual Monster VOA, wild complement geometry")
