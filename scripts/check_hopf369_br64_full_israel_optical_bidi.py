#!/usr/bin/env python3
"""BR64: EXACT BIDI between full nonlinear Israel Frechet and BR34 row form.

For the SAME matched induced perturbation δh at an original wall with
k+=j/2, k-=-j/2, and actual δK from full BR60 nonlinear graph:
 R_ab := 2[δK_ab]-2j δh_ab,
 δI_ab = 1/2(R_ab-h0_ab tr_h0 R)+3 δj h0_ab.

Bidirectional inverse on all 10 symmetric wall entries:
 R = 2(δI-3 δj h0 - (1/3)h0 tr_h0(δI-3 δj h0)).
No division by q, q², or a characteristic spectral root. The formula
is valid even at the zero and null tangential-frequency strata.

This is the geometric trace-reversal bridge, NOT YET an unconditional
identification of the normalized BR34 source rows with actual nonlinear
δK: their BR14 optical/BR19 moving shape/source-normal coordinate weld
remains necessary. Unmatched two-face induced geometry is refused.

Imports actual BR61 source, no duplication of δK or δh.
"""
import argparse
import sympy as s
from check_hopf369_br61_two_face_nonlinear_israel import (
    start,eta,j,dj,trace,metric_data,δh,δK
)

def trace_rev(t):
    return t-eta*trace(t)

def inverse_trace_rev(t):
    return t-eta*trace(t)/3

def check():
    phi,pp,pm,src=start()
    h=src.h
    K=src.plus-src.minus
    R=2*K-2*j*h
    I=src.linear
    via=trace_rev(R)/2+3*dj*eta
    assert (I-via).applyfunc(s.expand)==s.zeros(4)
    inverse=2*inverse_trace_rev(I-3*dj*eta)
    assert (inverse-R).applyfunc(s.expand)==s.zeros(4)
    # The right-side inverse is purely algebraic and keeps the original
    # ten geometric rows, including trace and all off-diagonals.
    independent=[R[a,b] for a in range(4) for b in range(a,4)]
    assert len(independent)==10
    assert all(s.simplify(inverse[a,b]-R[a,b])==0 for a in range(4) for b in range(4))
    print('PASS BR64 full original moving junction BIDI, ten geometric rows, nonzero delta tension')

def negative():
    phi,pp,pm,src=start()
    bad=pm.copy()
    bad[0,0]+=s.Rational(3,7)
    assert (δh(phi,pp,j/2)-δh(phi,bad,-j/2))!=s.zeros(4)
    # Without common induced δh, there is no single h from which to
    # compute a legitimate trace-reversed shell variation.
    # Also any omission of delta j changes physical source.
    R=2*(src.plus-src.minus)-2*j*src.h
    badI=trace_rev(R)/2
    assert (badI-src.linear).applyfunc(s.expand)!=s.zeros(4)
    print('PASS BR64 mismatched induced metric and omitted tension variation REFUSED')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['bidi','negative'],default='bidi')
    a=p.parse_args()
    {'bidi':check,'negative':negative}[a.part]()

if __name__=='__main__':main()
