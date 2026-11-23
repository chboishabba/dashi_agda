"""Compact TT checkpoint roundtrip and terminal-history parity.
Small-box harness, not full production propagate() replay.
"""
import numpy as np
from ksw668_f8_tt_multipole import stage,affine_mode3_stage,enforce
from ksw668_f8_fv_source_flux import exact_cell_averages
nr=17; ny=17; dr=.008; dy=.02; dt=.0005
src=exact_cell_averages(.04,np.arange(nr)*dr,dr)
cp=np.zeros_like(src);cm=np.zeros_like(src)
for q in range(3):
 d=3+4*q
 for j in range(1,nr):
  den=(j+.5)**d-(j-.5)**d
  cp[q,j]=d*(j+.5)**(d-1)/den;cm[q,j]=d*(j-.5)**(d-1)/den
import math
def F(t):return math.asinh(t)-math.sqrt(1+t*t)/t
T0=F(1)
def coeff(T):
 t=max(1.,math.exp(T+1)/2)
 for _ in range(7):
  t-=(F(t)-T)/(math.sqrt(1+t*t)/t**2)
  if t<.5:t=.5
 v=-1/math.sqrt(1+t*t);b=1/t;ds=T-T0;q=2*ds/.065-1
 amp=-6*math.sqrt(1-v*v)/b*math.exp(1-1/(1-q*q)) if 0<ds<.065 else 0.
 return v,b,amp
def rhs(X,T,aff):
 U,P,M=X;v,b,amp=coeff(T);enforce(U,P,M,v,amp,src,3)
 out=np.empty_like(X)
 args=(U,P,M,*out,dr,dy,b,v,amp,src,cp,cm,3)
 if aff:affine_mode3_stage(stage,*args)
 else:stage(*args)
 return out
def step(X,T,aff):
 X1=X+dt*rhs(X,T,aff)
 X2=.75*X+.25*(X1+dt*rhs(X1,T+dt,aff))
 return (X+2*(X2+dt*rhs(X2,T+dt/2,aff)))/3
from ksw668_f8_ssprk_checkpoint import NativeCheckpoint
from pathlib import Path
from tempfile import TemporaryDirectory
nt=160

def run(aff,path=None,cuts=()):
    X=np.zeros((3,3,ny,nr));walls=[None]*4
    config=dict(nt=nt,affine_stage=aff,dr=dr,dy=dy,dt=dt)
    def helper():return NativeCheckpoint(path,config,X.shape[1:],src,cp,cm)
    if path is not None: ck=helper()
    for it in range(nt+1):
        T=T0+it*dt
        if it in (nt-1,nt):
            j=it-(nt-1);walls[j]=X[0,:,0,:].copy();walls[j+2]=rhs(X,T,aff)[0,:,0,:].copy()
        X=step(X,T,aff)
        if it+1 in cuts:
            ck.save(it+1,*X,*walls)
            ck=helper();cursor,*fields=ck.load();assert cursor==it+1
            X=np.stack(fields[:3]);walls=fields[3:]
    walls.extend([X[0,:,0,:].copy(),rhs(X,T0+(nt+1)*dt,aff)[0,:,0,:].copy()])
    return [*X,*walls]

if __name__=='__main__':
 with TemporaryDirectory() as tmp:
    path=Path(tmp)/'state.npz';count=0
    for aff in (False,True):
        A=run(aff)
        for cuts in ((1,),(65,130),(159,),(160,),(161,),(1,65,130,159,160,161)):
            B=run(aff,path,cuts)
            for a,b in zip(A,B):np.testing.assert_array_equal(a,b);count+=1
        print('route',aff,'6 schedules bitwise equal')
    print('array checks',count)
    ck=NativeCheckpoint(path,dict(nt=nt,affine_stage=False,dr=dr,dy=dy,dt=dt),(3,ny,nr),src,cp,cm)
    try:ck.load();raise AssertionError('accepted mismatch')
    except ValueError as e:assert 'identity mismatch' in str(e)
    print('cross-route checkpoint rejection PASS')
