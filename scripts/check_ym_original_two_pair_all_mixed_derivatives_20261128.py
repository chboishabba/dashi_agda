#!/usr/bin/env python3
"""Original R445/Wilson L4 two-pair higher connected-derivative certificate.

Reuses the L=4 original 1536-face native source enumeration proved in
YMClayP0OriginalSUNF19TwelveStapleCenterHaarBaryonAndNonfactorization20261123.
For overlapping y/z original pairs, all N>=2, the exact Cartan restriction is
2/N*[11(1-cos(theta))+11(1-cos(phi))+1-cos(phi-theta)].
This script checks the ENTIRE mixed derivative parity family m,n=1..8
symbolically before specialization to ranks 2,3,4,5,8. Not an interacting
continuum construction or a CMP116 cluster activity bound.
"""
import sympy as S

def main():
    x,y,N,beta=S.symbols('theta phi N beta',real=True, positive=True)
    action=2/N*(11*(1-S.cos(x))+11*(1-S.cos(y))+
                (1-S.cos(y-x)))
    count=0
    for m in range(1,9):
        for n in range(1,9):
            actual=S.simplify(S.diff(action,x,m,y,n).subs({x:0,y:0}))
            if (m+n)%2:
                expected=S.Integer(0)
            else:
                expected=-S.Rational(2)/N*((-1)**(m+(m+n)//2))
            assert S.simplify(actual-expected)==0,(m,n)
            count+=1
    # The mixed derivatives of log(exp(-beta S)) are -beta times
    # those of the action; hence fourth-order connected data are nonzero
    # even if a Gaussian surrogate matches the mixed Hessian.
    assert S.simplify(S.diff(action,x,y).subs({x:0,y:0})+2/N)==0
    assert S.simplify(S.diff(action,x,2,y,2).subs({x:0,y:0})+2/N)==0
    assert S.simplify(S.diff(action,x,3,y).subs({x:0,y:0})-2/N)==0
    assert S.simplify(S.diff(action,x,y,3).subs({x:0,y:0})-2/N)==0
    for rank in (2,3,4,5,8):
        assert S.simplify((-beta*S.diff(action,x,2,y,2)
                            .subs({x:0,y:0,N:rank}))-2*beta/rank)==0
    print('PASS original-Wilson mixed derivative pattern',count,
          'symbolic derivatives; 4 Hessian/quartic identities; 5 ranks')

if __name__=='__main__':
    main()
