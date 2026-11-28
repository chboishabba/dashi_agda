#!/usr/bin/env python3
"""Original Machin two-atom Gaussian rational phase and Cayley ODE algebra.

Finite exact arithmetic only: this does NOT discharge the two actual
Bishop atan-to-exp evaluations or the Bishop analytic derivative limits.
"""
import json
from fractions import Fraction as F
import sympy as S


def mul(z, w):
    return z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0]


def power(z, n):
    a = (F(1), F(0))
    for _ in range(n):
        a = mul(a,z)
    return a


def phase(x):
    # (1+i*x)/(1-i*x) without introducing a floating-point pi.
    return (1-x*x)/(1+x*x), 2*x/(1+x*x)


def main():
    a,b=phase(F(1,5)),phase(F(1,239))
    assert a==(F(12,13),F(5,13))
    assert b==(F(28560,28561),F(239,28561))
    assert sum(t*t for t in a)==1 and sum(t*t for t in b)==1
    five4=power(a,4)
    assert five4==(F(-239,28561),F(28560,28561))
    assembled=mul(five4,(b[0],-b[1]))
    assert assembled==(F(0),F(1))
    # Signed and order controls: conjugation and power 4 are essential.
    assert mul(five4,b)!=(F(0),F(1))
    assert mul(power(a,3),(b[0],-b[1]))!=(F(0),F(1))
    assert mul(power(a,4),(b[0],b[1]))!=(F(0),F(1))
    x=S.symbols('x', real=True)
    I=S.I
    cayley=(1+I*x)/(1-I*x)
    assert S.simplify((1+x*x)*S.diff(cayley,x)-2*I*cayley)==0
    assert S.simplify(cayley.subs(x,0)-1)==0
    # Analytic target: E'=2i/(1+x*x)*E and E(0)=1.
    # Native Bishop proof still needs original atan derivative and uniqueness.
    assert S.simplify((1+x*x)*S.diff(2*S.atan(x),x)-2)==0
    h=S.symbols('h', positive=True)
    p=S.symbols('p', positive=True)
    assert S.simplify(2*p*(h/2)-p*h)==0
    # True selected CM exponent: 2*pi_M*i*((-1+i*h)/2)=-pi_M*h-i*pi_M.
    tau=(-1+I*h)/2
    exact_arg=S.expand(2*p*I*tau)
    assert S.simplify(exact_arg-(-p*h-I*p))==0
    # +i*pi_M exponent is equivalent only modulo the separately
    # established original Machin imaginary period, NOT the same arg.
    assert S.simplify(exact_arg-(-p*h+I*p))!=0
    q,w=S.symbols('q w')
    logratio=-2*p*h*w/(1-w)
    assert S.expand(S.series(S.exp(logratio),w,0,3).removeO()-(1-2*p*h*w+(2*(p*h)**2-2*p*h)*w*w))==0
    print(json.dumps({'five_phase':['12/13','5/13'], 'two39_phase':['28560/28561','239/28561'],
        'five_fourth':['-239/28561','28560/28561'], 'combined':['0','1'],
        'signed_negative_controls':3, 'cayley_complex_ODE_exact':True,
        'analytic_atan_derivative_reference':True,
        'selected_tau_half_to_full':True,'selected_tau_negative_imaginary_argument':True,
        'q_log_ray_two_coefficients':True,
        'original_bishop_atan_exp_evaluations_proved':False},sort_keys=True))


if __name__=='__main__': main()
