#!/usr/bin/env python3
"""BR210: exact Cartan collar trace and sharp closed-form refusal.
Exterior degree two, flat collar principal part; not an Einstein IBVP.
"""
import sympy as s
from itertools import combinations

def main():
    k,l=s.symbols('k l',positive=True)
    y=s.symbols('y',nonnegative=True)
    # Actual tangential exterior symbol in three spatial wall directions.
    xi=s.Matrix([k,0,0]); P=list(combinations(range(3),2))
    L=s.Matrix(3,3,lambda i,j:xi[P[i][0]]*int(P[i][1]==j)-xi[P[i][1]]*int(P[i][0]==j))
    assert L.T*L==k*k*s.eye(3)-xi*xi.T
    # Closed exact two-form d(alpha), alpha=exp(-ky+ikx1) dx2/(ik).
    # Strip the common phase; E_parallel and E_mixed have equal norms.
    f=s.exp(-k*y); e=s.Matrix([f,0,0]); m=s.Matrix([0,-s.I*f,0])
    assert e.diff(y)+s.I*L*m==s.zeros(3,1) # sign convention E_{iy}
    assert (e.H*e)[0]==f*f and (m.H*m)[0]==f*f
    assert s.integrate(2*f*f,(y,0,s.oo))==1/k
    assert (e.H*e)[0].subs(y,0)==1
    # Finite collar exact identity for independent polynomial field.
    a,b,c=s.symbols('a b c',real=True); q=a+b*y+c*y*y
    assert s.expand(q.subs(y,0)**2-s.integrate(q*q,(y,0,l))/l+2*s.integrate((1-y/l)*q*q.diff(y),(y,0,l)))==0
    # In frequency lambda>=1, weight lambda^(2s) splits the product
    # between lambda^(s+1/2) E_parallel and lambda^(s-1/2) D_y E_parallel.
    A,B,C,d=s.symbols('A B C d',positive=True)
    assert s.factor(d*A*A+(B+C)**2/d-2*A*(B+C))==(d*A-B-C)**2/d
    # Half-line closed-form packet: H^(1/2) bulk squared norm is 1,
    # while any lower tangential order has vanishing norm as k grows.
    assert s.simplify(k*s.integrate(2*f*f,(y,0,s.oo)))==1
    print('PASS BR210 exterior symbol, exact closed two-form trace obstruction, finite collar identity, half-order budget',s.__version__)
if __name__=='__main__':main()
