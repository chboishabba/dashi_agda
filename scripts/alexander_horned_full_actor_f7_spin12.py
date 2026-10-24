#!/usr/bin/env python3
"""Faithful 12D spin-sensitive representation of (2I)^3 rtimes C3 over F7.

Consumes the prior exact 120-icosian -> GL4(F7) representation.
This is a WREATH-IMPRIMITIVE actor on 3 copies of an actual
four-dimensional spin-sign module. The same central element
that A5 quotient erases acts as scalar -I12.
The explicit matrix multiplication is checked on representative
group elements; generic faithfulness follows from distinct block
positions and injectivity of the prior four-dimensional map.
"""
from random import Random
import alexander_horned_icosian_f49_minimal_spin as Spin
P=7
one=Spin.QI; minus=Spin.QN
rho=lambda g:Spin.restrict(Spin.embed(g))
D=12

def multiply_actor(x,y):
    a,k=x;b,l=y
    return (tuple(Spin.qm(a[i],b[(i-k)%3]) for i in range(3)),(k+l)%3)

def actor_matrix(actor):
    triple,k=actor
    M=[[0]*D for _ in range(D)]
    for src in range(3):
        dst=(src+k)%3
        A=rho(triple[dst])
        for i in range(4):
            for j in range(4):
                M[4*dst+i][4*src+j]=A[i][j]
    return tuple(tuple(row) for row in M)

def matmul(A,B):
    return tuple(tuple(sum(A[i][j]*B[j][k] for j in range(D))%P
                       for k in range(D)) for i in range(D))

identity=tuple(tuple(int(i==j) for j in range(D)) for i in range(D))
negative=tuple(tuple(6 if i==j else 0 for j in range(D)) for i in range(D))
assert actor_matrix(((one,one,one),0))==identity
assert actor_matrix(((minus,minus,minus),0))==negative
assert actor_matrix(((one,one,one),1))!=identity
all_spin=tuple(Spin.icosians)
rng=Random(20261024)
actors=[((one,one,one),k) for k in range(3)]
actors += [(tuple(rng.choice(all_spin) for _ in range(3)),rng.randrange(3))
           for _ in range(15)]
for a in actors:
    for b in actors:
        assert actor_matrix(multiply_actor(a,b))==matmul(actor_matrix(a),actor_matrix(b))
assert len({rho(g) for g in all_spin})==120
for sector in range(3):
    assert len({actor_matrix((tuple(g if j==sector else one for j in range(3)),0))
                for g in all_spin})==120
print("PASS 2I^3 rtimes C3 -> GL12(F7), spin central sign -I12")
print("PASS 18x18 actor multiplication tests and 120-element injectivity on each sector")
print("GENERIC INJECTIVITY: C3 rotates block positions; distinct 4x4 factors identify remaining element")
print("NOT CLAIMED: globally minimal degree 12, geometric pi1 or Monster/Dirac representation")
