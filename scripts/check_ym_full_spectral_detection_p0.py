#!/usr/bin/env python3
"""Finite exact same-H full-sector detection countermodel (not Clay proof)."""
import sympy as s
def main():
    q=s.Rational(2,3);T=s.diag(1,s.Rational(3,4),s.Rational(1,2))
    e0,e1,e2=s.eye(3).columnspace()
    A=e0*e2.T+e2*e0.T;B=e0*e1.T+e1*e0.T
    C=lambda O,n:((O*e0).T*T**n*(O*e0))[0]
    checks=0
    assert T==T.T and all(x>=0 for x in T.eigenvals());checks+=1
    assert A==A.T and B==B.T;checks+=1
    for n in range(1,13):
        assert C(A,n)==s.Rational(1,2)**n;checks+=1
        assert C(A,n)<=q**n;checks+=1
        assert C(B,n)==s.Rational(3,4)**n;checks+=1
    assert s.Rational(3,4)>q>s.Rational(1,2);checks+=1
    v=A*e0;w=B*e0
    k=s.Matrix.hstack(*(T**n*v for n in range(3)))
    assert k.rank()==1;checks+=1
    full=s.Matrix.hstack(*(T**n*z for z in (v,w) for n in range(3)))
    assert full.rank()==2;checks+=1
    nv=s.Matrix.hstack(e1,e2)
    assert nv.T*T*nv==s.diag(s.Rational(3,4),s.Rational(1,2));checks+=1
    assert (nv.T*full).rank()==2;checks+=1
    assert C(B,1)>q;checks+=1
    x,y=s.symbols('x y',real=True);z=x*e1+y*e2
    assert s.simplify((z.T*T*z)[0]-s.Rational(3,4)*x*x-s.Rational(1,2)*y*y)==0;checks+=1
    a,b=s.symbols('a b',positive=True)
    assert s.simplify((a/b)**3-(a/b)**2)==a*a*(a-b)/b**3;checks+=1
    print(f'{checks}/{checks} PASS exact same-H finite full-sector detection; selected rank 1, full rank 2')
if __name__=='__main__':main()
