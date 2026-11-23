"""LXXXIII validated piecewise-linear improvement to original FV q4 source mass.

Reuse original FV primitives and the existing rational expneg donor. Analytic
global bound |f''| <= 444 for f=exp(1-1/(1-u*u)), 0<=u<=1,
from t=(1-u*u)^-1 >= 1 and t^n exp(-t)<=n!, exp(1)<3.

Receiver bound is conditional on the source analytic interval construction,
ideal rational h=1/5 and frozen binary64 K. Not a native floating-adjoint
or full 96-output production certificate.
"""
from fractions import Fraction as Q
import argparse, json
import numpy as np
from check_f8_lxxxi_original_fv_interval import bump, primitive
from ksw668_f8_fv_source_flux import exact_cell_averages

def integrated_bump(a,b,panels):
    lo=hi=Q(0)
    for k in range(panels):
        x=a+(b-a)*k/panels; y=a+(b-a)*(k+1)/panels
        h=y-x
        fx=bump(x); fy=bump(y)
        left=(y*(y**3-x**3)/3-(y**4-x**4)/4)/h
        right=((y**4-x**4)/4-x*(y**3-x**3)/3)/h
        assert left>=0 and right>=0
        # Linear-interpolation remainder: |f''|/2 * (u-x)*(y-u).
        # Integrate against u^2, using u^2<=y^2 and integral h^3/6.
        err=37*y*y*h**3
        linear_lo=left*fx[0]+right*fy[0]-err
        linear_hi=left*fx[1]+right*fy[1]+err
        weight=(y**3-x**3)/3
        monotone_lo=weight*fy[0];monotone_hi=weight*fx[1]
        l=max(linear_lo,monotone_lo);u=min(linear_hi,monotone_hi)
        assert l<=u
        lo+=l;hi+=u
    return lo,hi

def source_boxes(panels):
    h=Q(1,5)
    out=[]
    for q in range(3):
        row=[]
        for j in range(13):
            a=max(Q(0),(j-Q(1,2))*h)
            b=min(Q(1),(j+Q(1,2))*h)
            if a>=b:row.append((Q(0),Q(0)));continue
            al,au=primitive(q,a);bl,bu=primitive(q,b)
            lo=bl-au;hi=bu-al
            if q==2:
                il,iu=integrated_bump(a,b,panels)
                lo+=27*il;hi+=27*iu
            row.append((lo,hi))
        out.append(row)
    return out

def receipt(panels,adjoint_files):
    source=exact_cell_averages(.04,np.arange(13)*.008,.008)
    h=Q(1,5);bounds=source_boxes(panels)
    errs=[];outside=0;inflation=Q(0)
    for q in range(3):
        d=3+4*q
        for j in range(13):
            W=((j*h+h/2)**d-max(Q(0),j*h-h/2)**d)/d
            lo,hi=bounds[q][j]
            mass=Q(float(source[q,j]))*W
            assert lo<=hi
            infl=max(lo-mass,mass-hi,Q(0))
            outside+=infl>0
            inflation=max(inflation,infl)
            errs.append(max(abs(mass-lo),abs(mass-hi))/W)
    result={'panels':panels,'outside_cells':outside,
        'max_required_mass_inflation':float(inflation),'orders':{},
        'scope':'Analytic real-FV intervals; binary64 source/K are frozen data, no floating algorithm or continuum certification.'}
    for order,file in adjoint_files.items():
        d=np.load(file);K=d['K']
        assert K.shape==(6,3,3,13)
        assert np.array_equal(source,d['native_fv'])
        rows=[]
        for channel in range(6):
            for mode in range(3):
                E=sum((abs(Q(float(K[channel,mode,q,j])))*errs[q*13+j]
                      for q in range(3) for j in range(13)),Q(0))
                rows.append(float(E))
        result['orders'][str(order)]={'max_frozen_receiver_error':max(rows)}
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--panels',type=int,default=1024)
    ap.add_argument('--order3-npz')
    ap.add_argument('--order4-npz')
    args=ap.parse_args()
    inputs={}
    if args.order3_npz:inputs[3]=args.order3_npz
    if args.order4_npz:inputs[4]=args.order4_npz
    print(json.dumps(receipt(args.panels,inputs),indent=2))
