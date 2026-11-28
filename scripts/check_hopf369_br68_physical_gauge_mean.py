#!/usr/bin/env python3
"""BR68: actual BR34/BR55 gauge Codazzi + mean-force source comparison.

No reconstructed PDE boundary operator: this file imports the ORIGINAL
BR34 metric_side/metric_rows/gauge_rows and compares their specific rows
with the already existing nonzero-mean coordinateCodazzi formula in
Hopf369WarpedPhysicalBoundaryExact.

At arbitrary mean M_ab, BR34 uses:
  Gref_a = d_n c+_a - d_n c-_a + q_a[c_n] - j/2(c+_a+c-_a).
The physical coordinate Codazzi row uses:
  Gphys_a = d_n c+_a - d_n c-_a + q_a[c_n]
             -2 M_a^b [c_b] - j(c+_a+c-_a).
Thus Gphys-Gref=-2 M_a^b[c_b]-j/2(c+_a+c-_a).
No mismatch is absorbed into unverified gauge zero modes.

For actual k+=m+j/2, k-=m-j/2,
 tau(k+)+tau(k-) - [tau(j/2)+tau(-j/2)]
       = -4m(ell_+ + ell_-).
The original mean force is precisely the last metric D and E row;
the corrected mean is an independent source, not an Israel row.
All q, j, M, metric and gauge channels are independent.

The *moving* graph normal and connection/shape source of BR19/31 is
additive and remains explicitly separate. This is a frozen coordinate
mean correction, NOT full nonlinear harmonic gauge at arbitrary graph.
"""
import argparse
import sympy as s
from check_hopf369_br_warped_physical_attachment import (
    metric_side,metric_rows,gauge_rows,E4,trace4,keys
)

def samples():
    m,j=s.symbols('mean j', real=True)
    q=s.Matrix(s.symbols('q0:4'))
    M=s.Matrix(4,4,lambda a,b:s.Symbol(f'M{min(a,b)}{max(a,b)}'))
    cp=s.Matrix(s.symbols('cp0:5'))
    cm=s.Matrix(s.symbols('cm0:5'))
    dp=s.Matrix(s.symbols('dp0:5'))
    dm=s.Matrix(s.symbols('dm0:5'))
    return m,j,q,M,cp,cm,dp,dm

def gauge():
    m,j,q,M,cp,cm,dp,dm=samples()
    jump=cp[:4,0]-cm[:4,0]
    su=cp[:4,0]+cm[:4,0]
    reference=dp[:4,0]-dm[:4,0]+q*(cp[4]-cm[4])-j*su/2
    physical=dp[:4,0]-dm[:4,0]+q*(cp[4]-cm[4])-2*M*E4*jump-j*su
    adjustment=-2*M*E4*jump-j*su/2
    assert (physical-reference-adjustment).applyfunc(s.expand)==s.zeros(4,1)
    for alloc in 'DE':
        original=gauge_rows(cp,dp,cm,dm,q,j,alloc)
        assert original.rows==10
        assert original[5:9,0]==reference
        # D and E have distinct physical prefix allocations: they
        # share precisely the same 4 Codazzi and 1 Gauss suffix.
        assert original[-1]==(
            dp[4]-dm[4]-(q.T*E4*jump)[0]-2*j*(cp[4]+cm[4]))
        assert (original[5:9,0]+adjustment-physical
                ).applyfunc(s.expand)==s.zeros(4,1)
    # No artificial rank-zero promotion: if M or mean source changes,
    # the correction is a genuinely independent symbolic polynomial.
    assert adjustment!=s.zeros(4,1)
    print("BR68 constructed original D/E ten-row gauge, four physical Codazzi and Gauss corrections")

def mean():
    m,j,q,M,cp,cm,dp,dm=samples()
    def metric(seed):
        H=s.Matrix(4,4,lambda a,b:s.Symbol(f'h{seed}{min(a,b)}{max(a,b)}'))
        b=s.Matrix(s.symbols(f'b{seed}0:4'))
        ell=s.Symbol(f'ell{seed}')
        return H.row_join(b).col_join(b.T.row_join(s.Matrix([[2*ell]])))
    pp,px,pm,mx=[metric(k) for k in range(4)]
    base=metric_side(pp,px,q,j/2)[3]+metric_side(pm,mx,q,-j/2)[3]
    full=metric_side(pp,px,q,m+j/2)[3]+metric_side(pm,mx,q,m-j/2)[3]
    ellp=pp[4,4]/2;ellm=pm[4,4]/2
    correction=-4*m*(ellp+ellm)
    assert s.expand(full-base-correction)==0
    for alloc in "DE":
        rows=metric_rows(pp,px,pm,mx,q,j,alloc)
        assert rows.rows==30 and rows[-1]==base
        assert s.expand(rows[-1]+correction-full)==0
    assert correction!=0
    print("BR68 constructed D/E final mean-force physical correction -4m(ell+ +ell-)")

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--part',choices=['gauge','mean','all'],default='all')
    args=parser.parse_args()
    if args.part in ('gauge','all'):gauge()
    if args.part in ('mean','all'):mean()
if __name__=='__main__':main()
