#!/usr/bin/env python3
"""Strict geometric KK charge-to-mass obstruction for free non-tachyonic modes.
For a spacelike periodic circle, p5=n/b, m4²=m5²+(n/b)² with m5²>=0;
canonical 4D KK gauge coupling q_n=sqrt(2)*n/(M_Pl*b).
Therefore |q_n|/m4 <= sqrt(2)/M_Pl for every n,b.
This is a restricted classical KK spectrum no-go, not a claim about
all higher-dimensional constructions or Higgs-mixed matter.
"""
import sympy as s
from decimal import Decimal, getcontext
getcontext().prec=40
n,b,M,m5=s.symbols('n b M m5',positive=True,real=True)
m4=s.sqrt(m5*m5+n*n/(b*b))
q=s.sqrt(2)*n/(M*b)
gap=s.factor(s.Rational(2,1)/(M*M)*m4*m4-q*q)
assert s.simplify(gap-2*m5*m5/(M*M))==0
assert s.simplify((q/m4).subs(m5,0)-s.sqrt(2)/M)==0
e=Decimal('0.3028221209');electron=Decimal('0.00051099895')
MP=Decimal('2.435e18')
ratio_observed=e/electron
ratio_limit=Decimal(2).sqrt()/MP
print('maximum geometric KK |q|/m =',ratio_limit,'GeV^-1')
print('electron measured |e|/m =',ratio_observed,'GeV^-1')
print('electron exceeds strict minimal KK ratio bound by',ratio_observed/ratio_limit)
assert ratio_observed/ratio_limit>Decimal('1e20')
print('PASS no-go for strict KK charge from fifth momentum with m5^2>=0')
print('DOES NOT rule out an independent bulk Maxwell photon or nonminimal mass/coupling sectors')
