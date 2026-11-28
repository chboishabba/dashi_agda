"""LXXXI P0 real-arithmetic original FV source enclosure.

Reuses the #1527 expneg interval donor; uses original FV primitive identities
and monotonicity of the compact bump. Native binary64 emitter roundoff is a
SEPARATE open proof; receiver sensitivity K is frozen binary64 evidence.
"""
from fractions import Fraction as Q
from math import ceil
import argparse,json
import numpy as np
from check_f8_lxxii_rational_load import expneg
from ksw668_f8_fv_source_flux import exact_cell_averages

def scalar(coeff, interval):
    l,u=interval
    return (coeff*l,coeff*u) if coeff>=0 else (coeff*u,coeff*l)

def bump(u):
    if u==1:return Q(0),Q(0)
    if u==0:return Q(1),Q(1)
    return expneg(1/(1-u*u)-1)

def primitive(q,u):
    if u==0 or u==1:return Q(0),Q(0)
    x=u*u; den=(1-x)**6
    if q==0:
        c=-8*u**3*(2*x**3+13*x*x-18*x+5)/(5*den)
    elif q==1:
        c=-32*u**7*(6*x*x-6*x+1)/(7*den)
    else:
        c=-u**3*(315*x**6-1644*x**5+3993*x**4-5392*x**3+4185*x*x-1764*x+315)/(35*den)
    return scalar(c,bump(u))

def fourth_remainder(a,b,panels):
    low=Q(0);high=Q(0)
    for k in range(panels):
        x=a+(b-a)*k/panels
        y=a+(b-a)*(k+1)/panels
        moment=(y**3-x**3)/3
        low+=moment*bump(y)[0]
        high+=moment*bump(x)[1]
    return 27*low,27*high

def boxes(h=Q(1,5),panels=256):
    n=ceil(1/h)+1
    out=[[None]*n for _ in range(3)]
    for j in range(n):
        a=max(Q(0),(j-Q(1,2))*h)
        b=min(Q(1),(j+Q(1,2))*h)
        for q in range(3):
            if a>=b:out[q][j]=(Q(0),Q(0));continue
            al,ah=primitive(q,a);bl,bh=primitive(q,b)
            lo=bl-ah;hi=bh-al
            if q==2:
                il,ih=fourth_remainder(a,b,panels)
                lo+=il;hi+=ih
            out[q][j]=(lo,hi)
    return out

def assess(evidence=None):
    h=Q(1,5); b=boxes()
    r=np.arange(13)*.008;src=exact_cell_averages(.04,r,.008)
    source=[]
    for q in range(3):
        d=3+4*q
        for j in range(6):
            W=((j*h+h/2)**d-max(Q(0),j*h-h/2)**d)/d
            lo,hi=b[q][j];z=Q(float(src[q,j]))*W
            source.append(dict(q=q,j=j,width=float(hi-lo),
                binary64_inside=lo<=z<=hi,rounding_gap=float(max(lo-z,z-hi,Q(0)))))
    result=dict(max_cell_mass_width=max(v['width'] for v in source),
       max_observed_float_mass_gap=max(v['rounding_gap'] for v in source),
       all_float_masses_inside=all(v['binary64_inside'] for v in source),
       cells=source)
    if evidence:
        evidence=np.load(evidence);K=evidence['K']
        assert K.shape==(6,3,3,13)
        outputs=[]
        for a in range(6):
            for m in range(3):
                lower=upper=nom=Q(0)
                for q in range(3):
                    d=3+4*q
                    for j in range(13):
                        c=Q(float(K[a,m,q,j]))
                        if j<=5:
                            W=((j*h+h/2)**d-max(Q(0),j*h-h/2)**d)/d
                            lo,hi=b[q][j];lo/=W;hi/=W
                        else:lo=hi=Q(0)
                        lower+=min(c*lo,c*hi)
                        upper+=max(c*lo,c*hi)
                        nom+=c*Q(float(src[q,j]))
                outputs.append(dict(channel=a,mode=m,width=float(upper-lower),
                    float_native_gap=float(max(lower-nom,nom-upper,Q(0)))))
        result['frozen_receiver']=dict(max_interval_width=max(x['width'] for x in outputs),
            max_native_binary64_gap=max(x['float_native_gap'] for x in outputs),
            all_native_float_rows_inside=all(x['float_native_gap']==0 for x in outputs),
            rows=outputs)
    result['scope']='Mathematical FV source boxes with original primitive, existing expneg donor and monotone fourth remainder. Native binary64 emitter rounding and adjoint floating errors NOT certified.'
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--native-adjoint-npz')
    a=p.parse_args()
    print(json.dumps(assess(a.native_adjoint_npz),indent=2))
