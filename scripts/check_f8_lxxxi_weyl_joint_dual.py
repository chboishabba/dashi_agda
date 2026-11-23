"""All-channel Weyl fixture sensitivities through exact rational LXXVIII dual.

This is a 5-step mode3 test, not t=12 native production or a floating
adjoint rounding certificate. Reuses existing local fixture transcript.
"""
import json
from fractions import Fraction as Q
from math import ceil
import numpy as np
from check_f8_lxxx_four_weyl_source_vjp import observer, clock, source_vjp
from check_f8_lxxv_taylor import enclose
from check_f8_lxxviii_joint_moments import box_error, exact_witness, dual_upper
from ksw668_f8_weak_source import weak_source


def run(h):
    dr=float(h)*.04; dt=.00018; dy=.012; n=ceil(1/h)+1; nr=9
    grid=np.arange(n+1)*dr
    source=weak_source(.04, grid, dr)
    lo,hi,rows,defect=box_error(enclose(h,20),source,h)
    witness,piv=exact_witness(lo,hi,rows,defect,h)
    assert all(x<=y<=z for x,y,z in zip(lo,witness,hi))
    cs=clock(); A=np.array([[float(v) for v in row] for row in rows])
    max_bound=Q(0); wins=0; all_case=[]
    for location,radius in [('near',4.35*dr),('far',5.25*dr)]:
        O=observer(radius,dr,.04,dt,12.,cs,nr)[0]
        for ch in range(4):
            for q in range(3):
                K=source_vjp(O[ch,q],cs,dt,dr,dy)
                c=[]
                for mode in range(3):
                    d=3+4*mode
                    for i in range(n):
                        W=((i*h+h/2)**d-max(Q(0),i*h-h/2)**d)/d
                        c.append(Q(float(K[mode,i]))/W)
                assert len(c)==len(lo)
                z=[Q(0)]*4
                b0=(-dual_upper([-v for v in c],lo,hi,rows,defect,defect,z),
                     dual_upper(c,lo,hi,rows,defect,defect,z))
                fit=np.linalg.lstsq(A.T,np.array(list(map(float,c))),rcond=None)[0]
                lam=[Q(float(v)).limit_denominator(10**8) for v in fit]
                p0=(-dual_upper([-v for v in c],lo,hi,rows,defect,defect,[-v for v in lam]),
                     dual_upper(c,lo,hi,rows,defect,defect,lam))
                selected=(max(b0[0],p0[0]),min(b0[1],p0[1]))
                actual=sum((x*y for x,y in zip(c,witness)),Q(0))
                assert selected[0]<=actual<=selected[1]
                assert selected[0]<=selected[1]
                assert selected[1]-selected[0]<=b0[1]-b0[0]
                if selected[1]-selected[0]<b0[1]-b0[0]:wins+=1
                max_bound=max(max_bound,selected[1]-selected[0])
                all_case.append(dict(place=location, channel=ch,ell=2*q,
                      box_width=float(b0[1]-b0[0]), selected_width=float(selected[1]-selected[0]),
                      actual_error=float(actual), improved=(selected[1]-selected[0]<b0[1]-b0[0])))
    return dict(mesh=str(h), cases=len(all_case), projected_improvements=wins,
                max_selected_width=float(max_bound),
                max_floating_source_moment_defect=max(abs(float(v)) for v in defect),
                cases_detail=all_case)

if __name__=='__main__':
    a=[run(Q(1,5)),run(Q(3,20))]
    print(json.dumps(a,indent=2))
    print('PASS',sum(x['cases'] for x in a),'exact-rational joint-dual fixture enclosures')
