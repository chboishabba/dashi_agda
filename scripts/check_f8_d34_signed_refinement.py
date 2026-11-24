"""D3.4: LVII overlap + LXIV signed reverse ledger on matched-clock trajectories.

Reduced replay, not a full t12 production receipt. Normal endpoints must coincide.
"""
import numpy as np
import sympy as sp
from check_f8_lvii_radial_fibre import overlap,coefficients
from ksw668_f8_signed_route_stage import step,receiver_defect_ledger
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_tt_multipole import F
from warp_native_geometric_receiver import receiver_bank
from warp_israel_affine import radial_source_at_receiver,offsets
from scipy.optimize import brentq

def transfer_builder(drc,nrc,dyc,nyc,drf,nrf,dyf,nyf):
    hc,hf=map(lambda x:sp.Rational(str(x)),(drc,drf))
    yc,yf=map(lambda x:sp.Rational(str(x)),(dyc,dyf))
    if yc*(nyc-1)!=yf*(nyf-1):raise ValueError('unmatched physical normal boundaries')
    maps=[overlap(hc,nrc-1,hf,nrf-1,d)[0] for d in (3,7,11)]
    # Piecewise linear nodal chart; exact endpoint incidence, no extrapolation.
    Y=np.zeros((nyf,nyc))
    for i in range(nyf):
        x=i*yf/yc;j=min(int(x),nyc-2);a=float(x-j)
        Y[i,j]=1-a;Y[i,j+1]=a
    def transfer(X):
        if X.shape!=(6,3,nyc,nrc) or np.any(X[..., -1]):
            raise ValueError('invalid active carrier')
        if np.any(X[4,:,1:,:]) or np.any(X[5,:,:-1,:]):
            raise ValueError('history boundary incidence violated')
        Z=np.zeros((6,3,nyf,nrf))
        for q,I in enumerate(maps):
            a=X[:4,q,:,:-1]
            radial=(I@a.reshape(-1,nrc-1).T).T.reshape(4,nyc,nrf-1)
            Z[:4,q,:,:-1]=Y@radial
            Z[4,q,0,:-1]=I@X[4,q,0,:-1]
            Z[5,q,-1,:-1]=I@X[5,q,-1,:-1]
        return Z
    return transfer,maps

def run(route='ledger',steps=12):
    drc,drf=.008,.006;dyc,dyf=.012,.009
    nc,nf,mc,mf=13,17,4,5
    dt=.0003;eps=.04;T0=F(1);t_end=brentq(lambda t:F(t)-T0-steps*dt,1,2)
    def coeff(T):
        t=brentq(lambda t:F(t)-T,.5,25)
        v=-1/np.sqrt(1+t*t);q=2*(T-T0)/.065-1
        amp=-6*np.sqrt(1-v*v)*t*np.exp(1-1/(1-q*q)) if abs(q)<1 else 0.
        return v,1/t,amp
    S,maps=transfer_builder(drc,nc,dyc,mc,drf,nf,dyf,mf)
    def grid(dr,dy,nr,ny):
        src=exact_cell_averages(eps,np.arange(nr)*dr,dr)
        cp,cm=coefficients(nr,dr)
        return src,lambda x,T:step(x,T,dt,coeff,dr,dy,src,cp,cm,route),np.zeros((6,3,ny,nr))
    sc,C,xc=grid(drc,dyc,nc,mc);sf,Ff,xf=grid(drf,dyf,nf,mf)
    mapped_source=np.zeros_like(sf)
    for q,I in enumerate(maps):mapped_source[q,:-1]=I@sc[q,:-1]
    cp,cm=coefficients(nf,drf)
    def mapped_step(x,T):return step(x,T,dt,coeff,drf,dyf,mapped_source,cp,cm,route)
    coarse=[xc];fine=[xf];errors=[xf-S(xc)];defects=[];source=[];transport=[]
    for n in range(steps+1):
        T=T0+n*dt;z=S(coarse[-1]);cn=C(coarse[-1],T);fn=Ff(fine[-1],T)
        a=Ff(z,T);m=mapped_step(z,T);b=S(cn)
        source.append(a-m);transport.append(m-b);defects.append(a-b)
        np.testing.assert_allclose(source[-1]+transport[-1],defects[-1],rtol=1e-10,atol=1e-12)
        coarse.append(cn);fine.append(fn);errors.append(fn-b)
    vel=np.array([coeff(T0+i*dt/2)[0] for i in range(2*(steps+1)+1)])
    result={}
    # Diagnostic probes on the reduced carrier, NOT original physical near/far.
    for rx in (.025,.065):
        banks=[receiver_bank(t_end,rx,eps,dr,dy,dt,vel,steps,nr,ny)
               for dr,dy,nr,ny in ((drc,dyc,nc,mc),(drf,dyf,nf,mf))]
        gc=radial_source_at_receiver(sc,coeff(T0+steps*dt)[2],rx,eps,drc)
        gf=radial_source_at_receiver(sf,coeff(T0+steps*dt)[2],rx,eps,drf)
        rows=[]
        for ch,(oc,of) in enumerate(zip(*banks)):
            obs=np.zeros((steps+2,6,3,mf,nf));obs[steps-1:steps+2,:3]=of
            total=receiver_defect_ledger(obs,errors,defects,T0,dt,coeff,drf,dyf,route)
            # Reverse separate source/transport without inventing separate errors.
            from ksw668_f8_signed_route_stage import reverse_step
            lam=obs[-1].copy();ss=np.zeros(3);tt=np.zeros(3)
            for n in range(steps,-1,-1):
                ss+=np.sum(lam*source[n],axis=(0,2,3))
                tt+=np.sum(lam*transport[n],axis=(0,2,3))
                lam=obs[n]+reverse_step(lam,T0+n*dt,dt,coeff,drf,dyf,route)
            def read(o,x):return np.sum(o*x,axis=(0,2,3))
            mismatch=sum(read(of[i],S(coarse[n])[:3])-read(oc[i],coarse[n][:3])
                         for i,n in enumerate(range(steps-1,steps+2)))
            offset=offsets(gf)[ch]-offsets(gc)[ch]
            direct=sum(read(of[i],fine[n][:3])-read(oc[i],coarse[n][:3])
                       for i,n in enumerate(range(steps-1,steps+2)))+offset
            pred=total['initial']+ss+tt+mismatch+offset
            np.testing.assert_allclose(pred,direct,rtol=1e-8,atol=1e-10)
            rows.append(dict(source=ss.tolist(),transport=tt.tolist(),observer=mismatch.tolist(),
                             offset=offset.tolist(),total=direct.tolist()))
        result[str(rx)]=rows
    return result

if __name__=='__main__':
    import json
    print(json.dumps({r:run(r) for r in ('paired','ledger')}))
