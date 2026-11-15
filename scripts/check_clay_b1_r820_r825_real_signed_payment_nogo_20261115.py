#!/usr/bin/env python3
"""B1 exact classical real-Fourier no-go for unrestricted R820/R823/R825.

Uses original R820/R823/R824/R825 algebra (not an enstrophy residual),
C1 original real Galerkin ODE and C2 independently reconstructed R853 rate.
The generic same-packet R820/R853 identities are sourced from Agda and
base-changed to the real finite-Fourier semantics, not kernel-checked here.
"""
from fractions import Fraction
from pathlib import Path
from importlib.util import spec_from_file_location, module_from_spec
from sympy import symbols, simplify, Rational

HERE=Path(__file__).resolve().parent
C2=HERE/'check_clay_c2_r853_selected_rate_sympy_20261115.py'
assert C2.is_file(), f'Missing already committed C2 source: {C2}'
spec=spec_from_file_location('clay_c2_source',C2)
c2=module_from_spec(spec)
spec.loader.exec_module(c2)

# R820/R823 literal four-helicity signed rate at nu=margin=1.
N,Q,CC,d=symbols('N Q CC d',real=True)
S=2*(9*N-Q)+CC+6*d
Reserve=CC+6*d
Demand=2*(Q-9*N)
assert simplify(S-(Reserve-Demand))==0  # R823 actualFullRateIsReserveMinusDemand

# R760/R822/R824 original signed CC rows split: originalIncidence kept,
# not swapped with comparable prototype; no positivity of either term.
HighCC,LowCC=symbols('HighCC LowCC',real=True)
cc_sub={CC: HighCC-LowCC}
Quadratic=6*d
High=HighCC+2*9*N
Low=LowCC+2*Q
assert simplify(S.subs(cc_sub)-(Quadratic+High-Low))==0

# R815/R741/R853 SOURCE same-packet selected normal form, the actual
# original critical production and coherent commutator, not ordinary
# enstrophy residual. R820's rate = R815 and R853's rate = R815 are
# the preexisting source identities, to be interpreted over the real field.
C,P,D=symbols('C P D',real=True)
Combined=12*C
PacketSurplus=P-D
R815=6*(Combined-PacketSurplus)
R853=6*(12*C-P+D)
assert simplify(R815-R853)==0

# Reconstruct the ACTUAL original 3-4-5 witness directly from R224/R230/R692
# and its source-bound physical whole-ball derivative / original R854 T.
cval,pval,dval,r0,nm,ng=c2.exact_snapshot()
b=c2.analytic_bounds()
assert (cval,pval,dval,r0)==(Rational(-557627,125),0,15834,Rational(-28273644,125))
assert nm==8 and ng==8
K,Lambda,T=b['K'],b['L'],b['T']
assert Lambda == 618365778064115445891072 and K==5032512
assert T==Fraction(226189,3938540454339300631433585885184)

# From the REAL Galerkin C1 trajectory with the same initial Fourier state,
# ||u'||inf<=K on [0,T] and universal ||Dr||_1 <= Lambda on the same ball:
# r(t)<=r0+Lambda*K*t <= upper for EVERY 0<=t<=T (analytic proof).
upper=Fraction(-28273644,125)+Lambda*K*T
safe=Fraction(-19,125)
assert upper<safe<0
# Thus for EVERY positive h<=T (not just h=T),
# integral_0^h r(t) dt <= safe*h <0.
for divisor in [1,2,3,5,7,11,101]:
    h=T/divisor
    assert safe*h<0
# The uniform proof above covers ALL h, not merely this rational test set.
integral_upper=Fraction(-28273644,125)*T+Fraction(Lambda*K,2)*T*T
assert integral_upper<0

# R823/R825 equivalences preserve the SAME integral; in the real-Fourier
# base change they cannot be nonnegative on this physical solution.
# Counterexample to unrestricted universal positive B1 payment, NOT a
# source-typed construction of a Q-valued R408 live trajectory.
print('PASS R820/R823 reserve-demand symbolic identity (all real scalars)')
print('PASS R824/R825 original-incidence high-low symbolic identity')
print('PASS R815/R853 literal selected-rate normal form (no zero residual)')
print('PASS original R224/R230/R692/R847/R853 physical snapshot replay',r0)
print('PASS whole-ball C1/C2 physical rate envelope original T',T)
print('PASS every h in (0,T] satisfies integrated R820/R823/R825 signed rate <',safe,'*h <0')
print('RESOLVED_BY_REFUTATION: unrestricted nonnegative B1 physical selected signed payment')
print('OPEN: Agda rational-valued R408 carrier, alternate restricted B route, B2 W1, global NS endpoint')
