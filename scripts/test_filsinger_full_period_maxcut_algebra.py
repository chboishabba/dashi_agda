#!/usr/bin/env python3
"""Independent source-model algebra tests for the J29-J32 candidate runner.

PASS does not assert that the full six-event interval/periodic-orbit proof ran.
"""
from fractions import Fraction as F
import ast, math, pathlib
import sympy as s

here=pathlib.Path(__file__).resolve().parent
script=here/'check_filsinger_full_period_maxcut.py'
src=script.read_text()
ast.parse(src)
assert 'periodic_orbit_proved\':False' in src
assert 'CHECKPOINT_BUDGET_EXHAUSTED' in src
assert "('V_OFF',F('4.31574095'),F('.0076'),F('.0086'))" in src
assert "('U_OFF',F('4.92434095'),F('.0038'),F('.005'))" in src

# Original source rows: 1.55, 1.4, Cb, Rd, bank and HF current.
u,v,b,ih,cb,rd,rg,lh=s.symbols('u v b ih Cb Rd Rgap Lh',nonzero=True)
vu=s.symbols('Vd')
g_u=u-b-vu;g_v=v-b-vu
norm_u=s.Matrix([[0,0,1,0,-1,0,0,0,0]])
norm_v=s.Matrix([[0,0,0,1,-1,0,0,0,0]])
coef_u=s.Matrix([0,0,-s.Rational(155,100)/s.Rational(117,100),
                 -1/s.Rational(117,100),1/cb,0,0,0,0])
coef_v=s.Matrix([0,0,-1/s.Rational(117,100),
                 -s.Rational(14,10)/s.Rational(117,100),1/cb,0,0,0,0])
for name,g,coef,n in [('U',g_u,coef_u,norm_u),('V',g_v,coef_v,norm_v)]:
    df=g*coef/rd
    coords=s.Matrix([s.Symbol('i'),s.Symbol('j'),u,v,b,s.Symbol('q'),s.Symbol('r'),ih,s.Symbol('x')])
    J=s.simplify(df.jacobian(coords))
    assert s.simplify(J-coef*n/rd)==s.zeros(9)
    assert J.rank()==1
    assert df.subs((u if name=='U' else v),b+vu)==s.zeros(9,1)

# Spark transition has nonzero field jump, and bank normal e_b.
fb_minus,fb_plus=s.symbols('fb_minus fb_plus',nonzero=True)
spark_delta=s.Matrix([0,0,0,0,fb_plus-fb_minus,0,0,1,0])
nb=s.zeros(1,9); nb[4]=1
salt=s.eye(9)+spark_delta*nb/fb_minus
assert s.simplify(s.det(salt)-fb_plus/fb_minus)==0

# Nonlinear HF capacitor row bound on |x|<=2, |ih|<=3, Ch=0.12, Gload=0.52.
gload=F(52,100);ch=F(12,100)
cap_row=(1+gload+6*(3+2*gload))/ch
assert cap_row==F(644,3) and cap_row<F(250)

# Exact wave period is 11 subperiods within original 20*pi.
tau=20*s.pi/11
assert s.simplify(s.Rational(11,10)*tau-2*s.pi)==0
assert s.simplify(11*tau-20*s.pi)==0

# Exact alternating arctan bounds; never feed double pi into a proof.
def atan_bounds(x,n=35):
    val=sum(((-1)**k*x**(2*k+1)/F(2*k+1) for k in range(n)),F(0))
    rad=x**(2*n+1)/F(2*n+1)
    return val-rad,val+rad
a,b=atan_bounds(F(1,5)),atan_bounds(F(1,239))
pi_lo=16*a[0]-4*b[1];pi_hi=16*a[1]-4*b[0]
assert pi_lo<pi_hi and pi_hi-pi_lo<F(1,10**44)
assert pi_lo>F('3.14159265358979323846264338327950288419716939937510')
assert pi_hi<F('3.14159265358979323846264338327950288419716939937512')

print('PASS: AST, mode-kink Jacobians rank-one, identity diode saltation,')
print('      spark determinant, global capacitor bound, exact tau, rational pi interval')
print('FULL PERIOD CERTIFICATION: NOT TESTED BY THIS ALGEBRA SUITE')
