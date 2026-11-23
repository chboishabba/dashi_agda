"""Masser (1975), p.118, via Bruinier–Ono–Sutherland arXiv:1301.5672 Lemma 2.3.
Compare lower-level cubic jet with higher-level quadratic jet; classical K supplied.
"""
from pathlib import Path
import json
import argparse
from time import perf_counter
from sympy import Poly, QQ, Rational, symbols, cancel
from check_cm163_modular_diagonal import diagonal
from check_cm163_derivative_slice import slice_poly
from check_cm163_fast import logder

def cubic(P,S,K):
    P,S=P.shift(K),S.shift(K)
    assert P.nth(0)==P.nth(1)==S.nth(0)==S.nth(1)==0
    a,b=S.nth(2),S.nth(3)
    assert a and P.nth(2)
    return cancel(2*b/a-P.nth(3)/P.nth(2)) # gamma=-kappa

def masser(P,S,K):
    P,S=P.shift(K),S.shift(K)
    assert P.nth(0)==S.nth(0)==0 and S.nth(1)
    assert P.nth(1)==2*S.nth(1)
    return cancel((4*S.nth(2)-P.nth(2))/S.nth(1))

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--coeffs',type=Path,required=True)
    args=ap.parse_args()
    X=symbols('X')
    for p,K in [(3,-32768),(5,-884736)]:
        t=perf_counter();D=4*p-1
        g=cubic(diagonal(p,logder),slice_poly(p,K,logder),K)
        G=masser(diagonal(D,logder),slice_poly(D,K,logder),K)
        assert g==G
        print('PASS independent levels',p,D,'gamma',g,'seconds',perf_counter()-t,flush=True)
    a,b=json.loads(args.coeffs.read_text())
    K=-640320**3
    g=cubic(Poly.from_list([int(c,16) for c in a],X,domain=QQ),Poly.from_list([int(c,16) for c in b],X,domain=QQ),K)
    assert g==Rational(77859659565707,19943834790540897829879824384000)
    assert 4+3*Rational(K,K-1728)+6*K*g==Rational(77265280,90856689)
    print('PASS CM163 stored slices rational-only gamma',g,flush=True)
if __name__=='__main__':main()
