#!/usr/bin/env python3
"""BR186: actual BR172 + BR156 projected p-p Coulomb operator.
Other s-containing ERIs deliberately omitted: not full CI.
"""
import sympy as s
from itertools import combinations
from check_hopf369_br172_174_joint import atomic
from check_hopf369_br154_156_atomic import coulomb

def eq(A,B):
    assert (A-B).applyfunc(s.simplify)==s.zeros(*A.shape)

def wedge(A,rows,cols):
    return s.Matrix(len(rows),len(cols),lambda i,j:
        A[rows[i][0],cols[j][0]]*A[rows[i][1],cols[j][1]]
        -A[rows[i][0],cols[j][1]]*A[rows[i][1],cols[j][0]])

def lift(A,pairs):
    t=s.symbols('t')
    return wedge(s.eye(A.rows)+t*A,pairs,pairs).diff(t).subs(t,0)

def main():
    H,J,U,params=atomic()
    V,_,modes,pp=coulomb()
    pairs=list(combinations(range(8),2))
    # Y_1,+1=-(px+i py)/sqrt2; Y_1,-1=(px-i py)/sqrt2.
    orbital={-1:s.Matrix([1,-s.I,0])/s.sqrt(2),0:s.Matrix([0,0,1]),1:-s.Matrix([1,s.I,0])/s.sqrt(2)}
    E=s.zeros(8,6)
    for j,(m,spin) in enumerate(modes):
        for i in range(3):
            E[2+2*i+(0 if spin==1 else 1),j]=orbital[m][i]
    eq(E.H*E,s.eye(6))
    eq(J*E,E*s.diag(*[m+s.Rational(spin,2) for m,spin in modes]))
    W=wedge(E,pairs,pp)
    eq(W.H*W,s.eye(15))
    C=(W*V*W.H).applyfunc(s.simplify)
    eq(W.H*C*W,V)
    assert C.rank()==15
    J2=lift(J,pairs);U2=wedge(U,pairs,pairs)
    H2=lift(H,pairs)+C
    eq(H2,H2.H)
    eq(H2*J2,J2*H2)
    eq(U2*H2.conjugate()*U2.H,H2)
    eq(U2*U2.conjugate(),s.eye(28))
    # Integer total Jz: time reversal no longer forces Kramers pairs.
    dims={j:len((J2-j*s.eye(28)).nullspace()) for j in range(-3,4)}
    assert sum(dims.values())==28 and all(dims[j]==dims[-j] for j in dims)
    print('BR186 total Jz dimensions',dims)
    print('PASS BR186 source-identical one-body + projected p-p Coulomb, axial and time-reversal action')
if __name__=='__main__':main()
