#!/usr/bin/env python3
"""Semidiscrete manufactured polynomial for the ORIGINAL moving AdS5 PDE.

For each TT multipole effective radial dimension d=3,7,11,
H(T,z,r)=d*T*T+r*r (independent of z) solves bulk linear tensor equation.
The exact moving Israel boundary datum is G=2*d*v(T)*T, where
qplus=qminus=2*d*T. Verify original stage on interior stencils.
This noncompact manufactured test is NOT the actual compact physical source.
"""
import math,json
import numpy as np
from ksw668_f8_tt_multipole import stage,enforce

def check(dr=.025,dy=.035,nr=25,ny=12,t=1.7,T=.3,normal_order=2):
    if min(dr,dy,T)<=0 or nr<6 or ny<6:
        raise ValueError('positive original-model manufactured test')
    dims=(3,ny,nr)
    U=np.zeros(dims);P=U.copy();M=U.copy();src=np.zeros((3,nr))
    r=np.arange(nr)*dr;v=-1/math.sqrt(1+t*t);b=1/t
    cp=np.zeros((3,nr));cm=np.zeros((3,nr))
    for q in range(3):
        d=3+4*q
        U[q]=d*T*T+r[None,:]**2
        P[q]=2*d*T;M[q]=2*d*T;src[q,:]=d
        for j in range(1,nr):
            den=(j+.5)**d-(j-.5)**d
            cp[q,j]=d*(j+.5)**(d-1)/den
            cm[q,j]=d*(j-.5)**(d-1)/den
    amp=2*v*T
    enforce(U,P,M,v,amp,src)
    outU=U.copy();outP=U.copy();outM=U.copy()
    stage(U,P,M,outU,outP,outM,dr,dy,b,v,amp,src,cp,cm,normal_order)
    errU=[];errP=[];errM=[]
    for q in range(3):
        d=3+4*q
        # Buffer cells exclude the forced outgoing boundary and its stencil.
        interior=(slice(1,ny-3),slice(0,nr-2))
        errU.append(float(np.max(abs(outU[q][interior]-2*d*T))))
        errP.append(float(np.max(abs(outP[q][interior]-2*d))))
        errM.append(float(np.max(abs(outM[q][interior]-2*d))))
        qplus=P[q,0,0];qminus=M[q,0,0]
        assert abs((1+v)*qplus+(v-1)*qminus-2*amp*d)<2e-12
    maxerr=max(errU+errP+errM)
    assert maxerr<1e-9
    return dict(original_a_t_model=True,normal_order=normal_order,effective_dimensions=[3,7,11],
        manufactured_bulk_H='d*T²+r², independent of z',
        manufactured_Israel_G='2*d*v(T)*T',
        max_err_dU=max(errU),max_err_dP=max(errP),max_err_dM=max(errM),
        original_moving_Israel_exact=True,
        semidiscrete_manufactured_consistency=True,
        compact_physical_source=False,
        receiver_Weyl_convergence=False,physical_observation=False)
if __name__=='__main__':print(json.dumps(check(),indent=2))
