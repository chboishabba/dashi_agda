#!/usr/bin/env python3
"""Exact rational regression for original Bishop finite LOG quotient identities.

Not a substitute for Agda 2.9 kernel acceptance. Source recurrence owners:
 BishopPowerFirstOrderDifferenceFactorisationExact.agda;
 BishopOriginalFiniteLogQuotientSecondOrderExact.agda;
 BishopOriginalFiniteLogQuotientUniformModulusExact.agda.
"""
from fractions import Fraction as F

def original_power_quotient(x, y, n):
    q = F(0)
    for k in range(n):
        q = q*y + x**k
    return q

def second_power_quotient(x, y, n):
    q0, t = F(0), F(0)
    for k in range(n):
        t = t*y + q0
        q0 = q0*x + x**k
    return t

def original_log_quotient(x, y, n):
    return sum((original_power_quotient(x, y, k+1)/F(k+1)
                for k in range(n)), F(0))

def log_derivative(x, n):
    return sum((x**k for k in range(n)), F(0))

def original_log_second(x, y, n):
    return sum((second_power_quotient(x, y, k+1)/F(k+1)
                for k in range(n)), F(0))

def run():
    cases = 0
    radii = [F(1,4), F(1,2), F(3,4), F(9,10)]
    for radius in radii:
        for i in range(11):
            x = radius*F(i,10)
            for j in range(11):
                y = radius*F(j,10)
                h = y-x
                for n in range(21):
                    q = original_log_quotient(x,y,n)
                    p = log_derivative(x,n)
                    s = original_log_second(x,y,n)
                    sr = original_log_second(radius,radius,n)
                    assert q-p == h*s, ("factor",radius,x,y,n)
                    assert F(0) <= s <= sr, ("order",radius,x,y,n)
                    assert abs(q-p) <= abs(h)*sr, ("modulus",radius,x,y,n)
                    assert sr <= F(1,2)/(1-radius)**2, ("radius",radius,n)
                    cases += 1
    print(f"PASS {cases} exact rational stage/endpoint/radius cases")
    print("Includes negative increments, n=0 and x=y.")
    print("This is regression evidence, not Agda kernel verification.")

if __name__ == "__main__":
    run()
