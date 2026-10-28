#!/usr/bin/env python3
"""Same *selected* horn commutator root, spin12 vs projective A5 BIDI.

Actual previously constructed finite root in
alexander_horned_spin_icosahedral_bridge.py is transported through
the explicit 120-element SL2(F5)<->icosian map and faithful GL12(F7)
actor. Its cube is diag(-I4,I4,I4), yet maps to identity projectively.
Finite SOURCE/quotient witness only, not geometric wild pi1.
"""
import alexander_horned_spin_icosahedral_bridge as Old
import alexander_horned_icosian_f49_minimal_spin as Spin
import alexander_horned_full_actor_f7_spin12 as Full

root=Old.q
assert Old.power(root,3)==Old.N
assert Old.action(Old.power(root,3))==tuple(range(5))
q=Spin.equivalence[root]
m=((q,Spin.QI,Spin.QI),0)
m3=Full.multiply_actor(Full.multiply_actor(m,m),m)
assert m3[0]==(Spin.QN,Spin.QI,Spin.QI)
assert m3[1]==0
assert Full.actor_matrix(m3)!=Full.identity
M=Full.actor_matrix(m3)
assert all(M[j][j]==(6 if j<4 else 1) for j in range(12))
assert all(M[i][j]==0 for i in range(12) for j in range(12) if i!=j)
left,right=Old.root
assert Old.comm(left,right)==root
def transport(g):return ((Spin.equivalence[g],Spin.QI,Spin.QI),0)
def inverse_icosian(q):
    a,b,c,d=q
    return (a,Spin.en(b),Spin.en(c),Spin.en(d))
def inverse_actor(a):
    return (tuple(inverse_icosian(g) for g in a[0]),0)
a=transport(left);b=transport(right)
comm=Full.multiply_actor(Full.multiply_actor(
    Full.multiply_actor(a,b),inverse_actor(a)),inverse_actor(b))
assert comm==m
assert Full.actor_matrix(comm)==Full.actor_matrix(m)
print("PASS actual selected generating horn-root commutator -> faithful GL12(F7) actor")
print("PASS same root cube has spin image diag(-I4,I4,I4) != I12")
print("PASS same root cube projective A5 image is identity")
print("NOT CLAIMED actual wild geometric pi1, physical Dirac state, Monster 3B identity")
