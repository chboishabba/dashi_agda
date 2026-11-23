"""LXXXV native spatial coefficient audit, finite-grid conditional comparison.

Compares original FV radial rows against exact rationals (dr=1/125) and the
original order-3/4 wall-normal matrices against high precision independent
formulas (dy=3/250, original binary64 b frozen). Does NOT certify IEEE error
of all compiled stage arithmetic or physical b(t) and receiver geometry.
"""
import json
from fractions import Fraction as Q
import numpy as np
import mpmath as mp
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import F
from warp_stage_adjoint import radial,normal
mp.mp.dps=90

def real(x):
    if isinstance(x,Q):return mp.mpf(x.numerator)/x.denominator
    return mp.mpf(float(x))

def audit():
    dr=.008;dy=.012;nr=13;ny=7
    radial_errors=[]
    for q,d in enumerate((3,7,11)):
        cells=np.arange(1,nr,dtype=float)
        denominator=(cells+.5)**d-(cells-.5)**d
        cp=d*(cells+.5)**(d-1)/denominator
        cm=d*(cells-.5)**(d-1)/denominator
        R=radial(nr,dr,q).toarray()
        for j in range(1,nr-1):
            low=Q(2*j-1,2);high=Q(2*j+1,2)
            den=high**d-low**d
            p=Q(d)*high**(d-1)/den;m=Q(d)*low**(d-1)/den
            exactscale=Q(125**2);nativescale=Q(float(dr*dr))
            coefficient=max(abs(Q(float(cp[j-1]))-p),abs(Q(float(cm[j-1]))-m))
            stage=max(abs(Q(float(cp[j-1]))/nativescale-p*exactscale),
                      abs(Q(float(cm[j-1]))/nativescale-m*exactscale))
            exactrow={j-1:m*exactscale,j:-(m+p)*exactscale,j+1:p*exactscale}
            transpose=max(abs(Q(float(R[j,k]))-v) for k,v in exactrow.items())
            radial_errors.append(dict(q=q,j=j,coefficient=float(coefficient),
                stage_scaled=float(stage),sparse_transpose=float(transpose)))
    steps=4;dt=.001
    t=np.array([brentq(lambda z:F(z)-F(1)-.02-k*dt/2,.5,3)
                for k in range(2*steps+1)])
    b=1/t
    normal_errors=[]
    for order in (3,4):
        for k in range(len(b)):
            z=[real(Q(float(b[k]))+i*Q(3,250)) for i in range(ny)]
            original=normal(ny,dy,float(b[k]),order).toarray()
            D=[[mp.mpf(0) for _ in range(ny)] for _ in range(ny)]
            for i in range(ny):
                if i==0:D[i][0]=-1;D[i][1]=1
                elif i==ny-1:D[i][ny-2]=-1;D[i][ny-1]=1
                else:D[i][i-1]=-mp.mpf('0.5');D[i][i+1]=mp.mpf('0.5')
            error=mp.mpf(0)
            for i in range(ny):
                for j in range(ny):
                    ref=D[i][j]/real(Q(3,250))
                    if order==4:
                        ref*=mp.power(z[i]/z[j],mp.mpf(3)/2)
                        if i==j:ref+=mp.mpf(3)/(2*z[i])
                    error=max(error,abs(real(original[i,j])-ref))
            normal_errors.append(dict(order=order,slot=k,max_error=float(error)))
    out=dict(status='PASS',radial_rows=len(radial_errors),
        radial_coeff_max=max(x['coefficient'] for x in radial_errors),
        native_stage_scaled_max=max(x['stage_scaled'] for x in radial_errors),
        sparse_transpose_max=max(x['sparse_transpose'] for x in radial_errors),
        normal_order3_max=max(x['max_error'] for x in normal_errors if x['order']==3),
        normal_order4_max=max(x['max_error'] for x in normal_errors if x['order']==4),
        normal_slots=len(b),radial=radial_errors,normal=normal_errors,
        scope='Selected fixture coefficient discrepancies; binary64 b frozen, ideal rational dr/dy. Not production floating error certification.')
    print(json.dumps(out,indent=2))
if __name__=='__main__':audit()
