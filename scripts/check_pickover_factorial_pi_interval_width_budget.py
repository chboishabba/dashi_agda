#!/usr/bin/env python3
"""Exact symbolic width obstruction for ordinary Pickover pi-interval evaluation.

TARGET: sin(99^(9999!)), not sin((99^9999)!) or a torsion CRT image.

Let E=9999!, N=99^E and let [L,U]⊂(3,4) be a genuine interval
enclosing pi, with exact width delta=U-L=10^(-P). The quotient
range N/L - N/U = N*delta/(L*U) > N*delta/16.

Since 99^10 > 10^19, N > 10^(19*E/10). Thus for
P <= 19*E/10 - 2, quotient range exceeds 100/16 > 1,
so one cannot certify the winding floor by requiring the ENTIRE
plain interval to stay inside a single integer bin. This is a
lower bound for that particular interval method, NOT all algorithms.

Original roots: Machin (1706), classical π irrationality, basic
interval arithmetic; DASHI #1260 already owns the certified
Machin window and complex-power algorithms. This adds only an
exact large-index resource receipt. No terminal sine sign.
"""
from math import factorial

def decimal_length(n):
    """Exact length via integer comparisons, no >4300-digit str()."""
    assert n>0
    lo,hi=0,max(2,n.bit_length())
    while lo+1<hi:
        m=(lo+hi)//2
        if n>=10**m: lo=m
        else: hi=m
    return lo+1

def audit():
    E=factorial(9999)
    assert E%10==0 and 99**10>10**19 and 99<100
    P=19*E//10-2
    assert 19*E==10*(P+2)
    # The displayed lower bound on *quotient interval width* is
    # >10^(19E/10-P)/16 = 100/16 > 1. Exact arithmetic only.
    assert 100>16
    assert decimal_length(E)==35656
    assert E.bit_length()==118445
    assert decimal_length(P)==35656
    assert P.bit_length()==118446
    # Avoid ever constructing 99**E, 10**P, or a pi bracket of width
    # 10**(-P): these are exactly the infeasible data objects.
    return dict(
      status='PASS',
      factorial_decimal_digits=decimal_length(E),
      factorial_binary_bits=E.bit_length(),
      naive_interval_precision_lower_expression='19*(9999!)/10 - 2 decimal places',
      decimal_digits_of_required_precision=decimal_length(P),
      rigorous_quotient_width_lower='100/16 > 1',
      exact_integer_evidence='99^10 > 10^19, 3 < pi < 4',
      scope='ordinary unrefined pi interval with full-width 10^-P',
      universal_complexity_lower_bound=False,
      original_terminal_sine_sign_certified=False
    )

if __name__=='__main__':
    import json
    print(json.dumps(audit(),indent=2))
