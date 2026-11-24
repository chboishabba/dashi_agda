"""Reduced source-driven windowed D4.B replay; NOT t12 production/convergence."""
import json
import numpy as np
from scipy.optimize import brentq
from check_f8_d34_signed_refinement import transfer_builder, coefficients
from ksw668_f8_tt_multipole import F
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_signed_route_stage import step, reverse_step
from check_f8_signed_window import window_rows


def run():
    h=.0003;nt=256;T0=F(1);eps=.04
    drc,drf,dyc,dyf=.008,.006,.012,.009
    nc,nf,mc,mf=13,17,4,5
    S,maps=transfer_builder(drc,nc,dyc,mc,drf,nf,mf)
    def coeff(T):
        t=brentq(lambda t:F(t)-T,.5,25);v=-1/np.sqrt(1+t*t);q=2*(T-T0)/.065-1
        amp=-6*np.sqrt(1-v*v)*t*np.exp(1-1/(1-q*q)) if abs(q)<1 else 0.
        return v,1/t,amp
    t=np.array([1/coeff(T0+n*h)[1] for n in range(nt+1)])
    sc=exact_cell_averages(eps,np.arange(nc)*drc,drc);sf=exact_cell_averages(eps,np.arange(nf)*drf,drf)
    sm=np.zeros_like(sf)
    for q,I in enumerate(maps):sm[q,:-1]=I@sc[q,:-1]
    pc,cc=coefficients(nc,drc);pf,cf=coefficients(nf,drf)
    result=[]
    for route in ('paired','ledger'):
        C=[np.zeros((6,3,mc,nc))];G=[np.zeros((6,3,mf,nf))];ds=[]
        for n in range(nt):
            T=T0+n*h;z=S(C[-1]);c=step(C[-1],T,h,coeff,drc,dyc,sc,pc,cc,route)
            f=step(G[-1],T,h,coeff,drf,dyf,sf,pf,cf,route)
            a=step(z,T,h,coeff,drf,dyf,sf,pf,cf,route);m=step(z,T,h,coeff,drf,dyf,sm,pf,cf,route)
            ds.append((a-m,m-S(c)));C.append(c);G.append(f)
        for rx in (.065,.075):
            ic,wc,*_=window_rows(t,h,rx,eps,drc,nc,.05,.018)
            jf,wf,*_=window_rows(t,h,rx,eps,drf,nf,.05,.018)
            assert not np.any(sc[:,ic]) and not np.any(sf[:,jf])
            for ch in range(2):
                def obs(n):
                    o=np.zeros_like(G[0]);o[0,:,0,:][:,jf]=wf[ch,n];return o
                lam=obs(nt);signed=np.zeros((2,6,3));absolute=signed.copy();mismatch=np.zeros(3);direct=np.zeros(3)
                for n in range(nt-1,-1,-1):
                    for j,d in enumerate(ds[n]):
                        val=np.sum(lam*d,axis=(2,3));signed[j]+=val;absolute[j]+=abs(val)
                    lam=obs(n)+reverse_step(lam,T0+n*h,h,coeff,drf,dyf,route)
                    oc=np.sum(wc[ch,n]*C[n][0,:,0,:][:,ic],axis=1)
                    of=np.sum(wf[ch,n]*G[n][0,:,0,:][:,jf],axis=1)
                    oz=np.sum(wf[ch,n]*S(C[n])[0,:,0,:][:,jf],axis=1)
                    mismatch+=oz-oc;direct+=of-oc
                assert not np.any(wc[ch,nt]) and not np.any(wf[ch,nt])
                pred=signed.sum(axis=(0,1))+mismatch;bound=absolute.sum(axis=(0,1))+abs(mismatch)
                err=abs(pred-direct);rel=err/np.maximum(bound,1e-300)
                assert np.isfinite([pred,direct,bound]).all() and np.all(rel<1e-9)
                result.append(dict(route=route,rx=rx,row=ch,direct=direct.tolist(),signed=signed.tolist(),absolute=absolute.tolist(),observer=mismatch.tolist(),max_abs_error=float(max(err)),max_scaled_error=float(max(rel))))
    return result


if __name__=='__main__':print(json.dumps(run()))
