"""Coarse full-clock source-driven forward diagnostic, not production refinement."""
import argparse,json,math,time
import numpy as np
from scipy.optimize import brentq
from check_f8_modal_cfl import clock,envelope
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_signed_route_stage import step
from warp_native_geometric_receiver import receiver_bank
from check_f8_signed_window import window_rows
from check_f8_shrinking_injection import build,read


def run(route):
    start=time.monotonic();dr=.03;dy=.036;nr=math.ceil(3.01/dr)+1;ny=113;delta=.18
    cap=float(envelope(dr,dy,nr-1,route)[2]);T0=clock(1);span=clock(12)-T0
    nt=math.ceil(span/min(.002,cap));h=span/nt;T=np.arange(nt+2)*h
    def coeff(s):
        t=brentq(lambda z:clock(z)-s,.5,14);v=-1/math.sqrt(1+t*t);q=2*(s-T0)/.065-1
        return v,1/t,-6*math.sqrt(1-v*v)*t*math.exp(1-1/(1-q*q)) if abs(q)<1 else 0.
    ts=np.array([1/coeff(T0+n*h)[1] for n in range(nt+2)])
    vel=np.array([coeff(T0+n*h/2)[0] for n in range(2*(nt+1)+1)])
    r=np.arange(nr)*dr;src=exact_cell_averages(.04,r,dr);cp=np.zeros_like(src);cm=cp.copy()
    j=np.arange(1,nr,dtype=float);a=j-.5;b=j+.5
    for q,d in enumerate((3,7,11)):
        den=b**d-a**d;cp[q,1:]=d*b**(d-1)/den;cm[q,1:]=d*a**(d-1)/den
    bulk=math.sqrt(span**2-(1-1/12)**2);rxs=(bulk-.012,bulk+.1)
    patches=[build(T,ts,dy,ny,dr,nr,rx,delta) for rx in rxs]
    windows=[window_rows(ts,h,rx,.04,dr,nr,span-.15,.10)[:2] for rx in rxs]
    assert all(not np.any(src[:,p[2]]) for p in patches)
    assert all(not np.any(src[:,i]) for i,w in windows)
    X=np.zeros((6,3,ny,nr));shrink=np.zeros((2,6,3));window=np.zeros((2,2,3));slots=[]
    for n in range(nt+2):
        for k,(p,(i,w)) in enumerate(zip(patches,windows)):
            if p[0].start<=n<p[0].stop:
                for ch in range(6):shrink[k,ch]+=read(p,ch,n,X)
            if np.any(w[:,n]):window[k]+=np.sum(w[:,n]*X[0,:,0,:][:,i],axis=-1)
        if n>=nt-1:slots.append(X[:3].copy())
        if n==nt+1:break
        X=step(X,T0+n*h,h,coeff,dr,dy,src,cp,cm,route)
        if not np.isfinite(X).all():raise ValueError('nonfinite state')
    raw=[]
    for rx in rxs:
        bank=receiver_bank(12,rx,.04,dr,dy,h,vel,nt,nr,ny)
        raw.append(np.einsum('csiqyr,siqyr->cq',bank,np.array(slots)))
    return dict(route=route,dr=dr,dy=dy,nr=nr,ny=ny,nt=nt,h=h,cap=cap,rx=rxs,delta=delta,source_cells=np.count_nonzero(src,axis=1).tolist(),raw=np.array(raw).tolist(),window=window.tolist(),shrink=shrink.tolist(),max_final_state=float(abs(X).max()),seconds=time.monotonic()-start)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('route',choices=['paired','ledger']);print(json.dumps(run(p.parse_args().route)))
