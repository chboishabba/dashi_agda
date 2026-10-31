#!/usr/bin/env python3
"""Structural SSP15 C3 ten-jet injectivity, via two Vandermonde blocks.

Proof (over characteristic zero). If ten jets vanish then G0(k)=G2(k)
and G1(k)=G2(k), hence G0(k)=G1(k) for k=0..4. The 5
disjoint nodes {3,7,13,19,31} have a nonsingular Vandermonde matrix,
so their coefficients vanish. Now G2(k)=0 for k=0..9; the 10
residue-2 nodes have a nonsingular Vandermonde matrix, so all vanish.
This is an exact mathematical proof of injectivity for ALL inputs;
the script executes exact matrix identities and 9-jet collision.

For nine jets, take barycentric weights 1/D'(p) on the ten
residue-2 nodes; their moments 0..8 vanish and moment 9 = 1.
Clear rational denominators to obtain an integral collision.
"""
import math
from functools import reduce
from sympy import Matrix, Rational, ilcm, igcd, prod
from check_ssp15_c3_winding_jet_rank import P, jet_matrix

def vandermonde(nodes):
    return Matrix([[int(p)**k for p in nodes] for k in range(len(nodes))])

def primitive_barycentric(nodes):
    weights=[Rational(1,prod(q-r for r in nodes if r!=q)) for q in nodes]
    scale=reduce(ilcm,(w.q for w in weights),1)
    v=[int(w*scale) for w in weights]
    divisor=reduce(igcd,(abs(z) for z in v))
    return [z//divisor for z in v]

def main():
    g0=[p for p in P if p%3==0]
    g1=[p for p in P if p%3==1]
    g2=[p for p in P if p%3==2]
    assert len(g0)==1 and len(g1)==4 and len(g2)==10
    lhs=tuple(g0+g1)
    d5=vandermonde(lhs).det(method="domain-ge")
    d10=vandermonde(g2).det(method="domain-ge")
    assert d5!=0 and d10!=0
    assert d5==prod(lhs[j]-lhs[i] for i in range(5) for j in range(i+1,5))
    assert d10==prod(g2[j]-g2[i] for i in range(10) for j in range(i+1,10))
    kernel_map=dict(zip(g2,primitive_barycentric(g2)))
    collision=Matrix([kernel_map.get(p,0) for p in P])
    m9,m10=jet_matrix(9),jet_matrix(10)
    assert m9*collision==Matrix.zeros(18,1)
    assert (m10*collision)[9]!=0
    assert m10.rank()==15
    assert m9.rank()==14
    positive=collision.applyfunc(lambda z:max(0,z))
    negative=collision.applyfunc(lambda z:max(0,-z))
    assert m9*positive==m9*negative
    assert m10*positive!=m10*negative
    print("PASS structural injectivity: Vandermonde(5) and Vandermonde(10)")
    print("PASS exact minimal jet depth: 9 insufficient; 10 sufficient")
    print("PASS barycentric primitive integral nine-jet collision:",tuple(collision))
    print("PASS nonzero tenth derivative witness:",(m10*collision)[9])
if __name__=="__main__":main()
