#!/usr/bin/env python3
"""BR58: ALL-ORDER BR52 material conormal -> ORIGINAL BR34 D/E boundary rows.

BR52 gives actual ADM moving F=n-f and all 15+5 source derivative jets,
including independent time, tangent, and normal derivatives on BOTH faces.
Its normalized material derivative is:
  d_material U = d_n U + k_t d_t U + k_i d_i U.
BR34 physical D/E 30 metric and 10 gauge rows are linear in d_n U;
therefore the exact source correction is B(0,delta_xp,0,delta_xm).
This is their actual derivative-column Jacobian, with j,q varying
independently through all orders 0..8 (BR47).

Crucially this does NOT replace the real moving Israel hypersurface:
the full unit-normal factor sqrt(z) and graph material extrinsic shape
from BR19/31 remain separately unpaid. The linear BR34 reference
operator is NOT a general nonlinear moving-wall boundary map.

All computations are exact fractions, original BR34 SymPy tensor/gauge
row implementations; each allocation/sector in a separate <=90s stage.
"""
import argparse
from fractions import Fraction as F
import sympy as s
from check_hopf369_br_warped_physical_attachment import metric_rows,gauge_rows,dec
from check_hopf369_br52_all_order_material_flux import (
    ORDER,make_source,field_jet,coeff,add,mul,trim,sub
)

def val_coeff(ch,face,n):
    return F(((ch+3)*(face+2)*(n+1))%29-14,17+n)

def original_value(sector,face,n):
    dim=15 if sector=="metric" else 5
    v=s.Matrix([s.Rational(*val_coeff(k,face,n).as_integer_ratio())
                for k in range(dim)])
    return dec(v) if sector=="metric" else v

def normal_value(sector,face,n):
    dim=15 if sector=="metric" else 5
    v=s.Matrix([s.Rational(*coeff(field_jet(k,face,4),n).as_integer_ratio())
                  /s.factorial(n) for k in range(dim)])
    return dec(v) if sector=="metric" else v

def material_difference(sector,face,n,src):
    N,H,v,Hi,D,Ninv2,Fspace,Ftime,theta,kt,ks=src
    dim=15 if sector=="metric" else 5
    values=[]
    for k in range(dim):
        jets=[field_jet(k,face,i) for i in range(5)]
        corr=add(mul(kt,jets[0]),
                 sum_series(mul(ks[i],jets[i+1]) for i in range(4)))
        values.append(s.Rational(*corr[n].as_integer_ratio()))
    v=s.Matrix(values)
    return dec(v) if sector=="metric" else v

def sum_series(items):
    out=trim([])
    for a in items:out=add(out,a)
    return out

def zero(sector):
    return dec(s.zeros(15,1)) if sector=="metric" else s.zeros(5,1)

def bg_coeff(r):
    if r==0:
        return s.Rational(-6,5),s.Matrix([s.Rational(i+1,i+3) for i in range(4)])
    return (s.Rational((r+1)%7-3,r+11),
            s.Matrix([s.Rational((r+2)*(i+1)%13-6,r+i+17)
                      for i in range(4)]))

def rows(sector,alloc,U,j,q):
    if sector=="metric":
        return metric_rows(U[0],U[1],U[2],U[3],q,j,alloc)
    return gauge_rows(U[0],U[1],U[2],U[3],q,j,alloc)

def check(sector,alloc):
    src=make_source()
    z=zero(sector)
    Zq=s.zeros(4,1)
    out=30 if sector=="metric" else 10
    for order in range(ORDER+1):
        fields=lambda n: [
            original_value(sector,0,n),normal_value(sector,0,n),
            original_value(sector,1,n),normal_value(sector,1,n)
        ]
        correction=lambda n: [
            z,material_difference(sector,0,n,src),
            z,material_difference(sector,1,n,src)
        ]
        j0,q0=bg_coeff(0)
        # Coefficient of actual physical reference row Taylor series:
        # B(j0,q0;U_r) + Σ_{a=1}^r δB(j_a,q_a;U_{r-a}).
        source=rows(sector,alloc,fields(order),j0,q0)
        for a in range(1,order+1):
            ja,qa=bg_coeff(a)
            source+=rows(sector,alloc,fields(order-a),ja,qa)
            source-=rows(sector,alloc,fields(order-a),s.S.Zero,Zq)
        # Material conormal corrected normal jets, retaining both faces.
        material_fields=lambda n: [fields(n)[i]+correction(n)[i] for i in range(4)]
        modified=rows(sector,alloc,material_fields(order),j0,q0)
        for a in range(1,order+1):
            ja,qa=bg_coeff(a)
            modified+=rows(sector,alloc,material_fields(order-a),ja,qa)
            modified-=rows(sector,alloc,material_fields(order-a),s.S.Zero,Zq)
        # Real BR34 derivative columns are completely background-free;
        # therefore no uncharged j_t or q_t product is introduced.
        derivative_payment=rows(sector,alloc,correction(order),s.S.Zero,Zq)
        assert (modified-source-derivative_payment).applyfunc(s.cancel)==s.zeros(out,1),(
            sector,alloc,order)
        assert out==modified.rows
        # A nontrivial moving source must not silently be discarded:
        if order==0:
            assert derivative_payment!=s.zeros(out,1)
        if sector=="metric":
            # The last physical metric row is mean force and retains
            # its real normal-derivative contribution at every order.
            expected=derivative_payment[-1]
            assert s.cancel(modified[-1]-source[-1]-expected)==0
    print("PASS BR58",sector,alloc,"actual rows",out,"normal conormal source 0..8")
    print("PASS shared BR52 ADM/BR47 background time-jet and no false extra j*q mixing")

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--sector",choices=["metric","gauge"],required=True)
    p.add_argument("--allocation",choices=["D","E"],required=True)
    a=p.parse_args()
    check(a.sector,a.allocation)

if __name__=="__main__":main()
