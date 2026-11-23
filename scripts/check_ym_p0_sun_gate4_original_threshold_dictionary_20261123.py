#!/usr/bin/env python3
"""YM P0 actual source scalar threshold crosswalk, not a physical CMP119 T.
The existing Gate4 predicate has literal SU2 rational quaternion holonomies.
The corresponding SU(N) normalized matrix Frobenius chord is analytically
2*(1-ReTr(U)/N) on TRUE continuous SU(N), at each original plaquette.
Distinct Gate4 "coupling" gamma and original bare Wilson beta stay distinct.
"""
from fractions import Fraction as Q
from itertools import product
import sympy as s
checks=0
def verify(v):
    global checks
    assert v
    checks+=1

for q in [(Q(3,5),Q(4,5),Q(0),Q(0)),
          (Q(-3,5),Q(0),Q(4,5),Q(0)),
          (Q(0),Q(0),Q(0),Q(1)),
          (Q(-1),Q(0),Q(0),Q(0)),
          (Q(1),Q(0),Q(0),Q(0))]:
    verify(sum(x*x for x in q)==1)
    cd=(q[0]-1)**2+sum(x*x for x in q[1:])
    df=1-q[0]
    verify(cd==2*df)
    for tau in (Q(0),Q(1,3),Q(1),Q(7,5),Q(2)):
        verify((tau*tau<=cd)==(df>=tau*tau/2))

# Exact true SU(N) determinant-1 diagonal eigenvalue fixture:
# (exp(i theta), exp(-i theta),1,...,1). Chord is Frobenius squared/N.
for n,co,tau in product(range(2,12),(Q(1),Q(0),Q(-1,2),Q(-1)),
                       (Q(0),Q(1,3),Q(1),Q(7,5),Q(2))):
    trace=Q(n-2+2*co,n)
    deficit=1-trace
    ch=Q(4-4*co,n)
    verify(ch==2*deficit)
    verify((tau*tau<=ch)==(deficit>=tau*tau/2))
    verify(0<=deficit<=2)

beta,gamma,p0,eta,B,eps=s.symbols('beta gamma p0 eta B eps',real=True)
tau=gamma*p0
eta_tau=eta**2*tau
verify(s.simplify(tau**2/2-gamma**2*p0**2/2)==0)
verify(s.simplify(eta_tau**2/2-eta**4*gamma**2*p0**2/2)==0)
logq=s.log(1176)+B/16-beta*eps/384
verify(s.simplify(384*logq+(beta*eps-384*s.log(1176)-24*B))==0)
verify(s.simplify((beta*tau**2-768*s.log(1176)-48*B)
        -2*(beta*eps-384*s.log(1176)-24*B).subs(eps,tau**2/2))==0)

d,c,K=s.symbols('d c K',positive=True)
BB=8+s.Rational(2,3)*s.log(K)+d*s.log(beta)
expr=c*c*s.log(beta)-768*s.log(1176)-48*BB
verify(s.expand(expr).coeff(s.log(beta))==c*c-16*d)
print('PASS',checks,'exact true SU(N) Wilson matrix, original SU2 rational-quaternion and two-scale threshold checks')
print('Existing Gate4 LargePlaquette uses tau=gamma*p0, NOT eta²*tau.')
print('True SU(N) scalar event: 1-ReTr(U_p)/N >= tau²/2.')
print('Bare chessboard sufficient condition: beta*tau²>768log1176+48 B_N(beta).')
print('Do not identify Gate4 gamma with actual Wilson beta without SOURCE evidence.')
print('Not CMP119/122 physical T, absolute CMP116 W3 or OS mass gap.')
