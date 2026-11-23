"""Native order-3/4 projected SSPRK3 source and moving-support regression.
Run locally; finite algebraic parity only, not a convergence/energy certificate.
"""
import numpy as np
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import stage, F
from ksw668_f8_fv_source_flux import exact_cell_averages, total_scaled_moments
from warp_frame_attribution import metric, project, lower, native_reverse

def check(order):
    dr,dy,h,eps=.008,.012,.001,.04
    nr,ny=13,7
    rg=np.arange(nr)*dr
    src=exact_cell_averages(eps,rg,dr)
    cp=np.zeros((3,nr)); cm=cp.copy()
    for q,d in enumerate((3,7,11)):
        j=np.arange(1,nr)
        den=(j+.5)**d-(j-.5)**d
        cp[q,1:]=d*(j+.5)**(d-1)/den
        cm[q,1:]=d*(j-.5)**(d-1)/den
        vol=((rg+dr/2)**d-np.maximum(rg-dr/2,0)**d)/d
        np.testing.assert_allclose(vol@src[q]/eps**d,
            total_scaled_moments()['l'+str(2*q)],atol=1e-7,rtol=0)
    assert not np.any(src[:,-1])
    T=F(1)+.02
    def geom(t):
        s=brentq(lambda s:F(s)-t,.5,3.)
        return 1/s,-1/np.sqrt(1+s*s)
    g0,g1,gm=map(geom,(T,T+h,T+h/2))
    shape=(3,3,ny,nr)
    rng=np.random.default_rng(1530+order)
    x=project(rng.normal(size=shape))
    lam=project(rng.normal(size=shape))
    def euler(x,g,f=0.):
        out=np.empty_like(x)
        stage(*x,*out,dr,dy,*g,f,src,cp,cm,order)
        return project(x+h*out)
    A,B,C=[lambda x,g=g:euler(x,g) for g in (g0,g1,gm)]
    amps=(.013,-.021,.034)
    zero=np.zeros(shape)
    a,b,c=[euler(zero,g,f) for g,f in zip((g0,g1,gm),amps)]
    for g,f,r in zip((g0,g1,gm),amps,(a,b,c)):
        expected=np.zeros(shape);expected[2,:,0,:]=-4*h*f*src/dy
        np.testing.assert_allclose(r,expected,rtol=1e-12,atol=1e-12)
        np.testing.assert_allclose(euler(x,g,f),euler(x,g)+r,rtol=1e-11,atol=1e-11)
    def evolve(x,a,b,c):
        u=A(x)+a
        v=.75*x+.25*(B(u)+b)
        return u,v,x/3+2*(C(v)+c)/3
    u,v,y=evolve(x,a,b,c)
    w0=metric(ny,nr,dr,dy,g0[0]);w1=metric(ny,nr,dr,dy,g1[0])
    adj,dual=native_reverse(lam,w0,w1,dr,dy,h,(g0,g1,gm),order)
    p=lower(lam,w1)
    def pair(a,b):return np.sum(a*b)
    def close(a,b,scale):
        assert abs(a-b)<=1e-11*max(1.,scale), (a,b,scale)
    rhs=[pair(lower(adj,w0),x)]+[pair(d,r) for d,r in zip(dual,(a,b,c))]
    close(pair(p,y),sum(rhs),sum(map(abs,rhs)))
    def ledger(masks):
        Q0,QA,QB,Q1=[lambda x,m=m:m*x for m in masks]
        KA=QA(A(x))-A(Q0(x))
        KB=QB(B(u))-B(QA(u))
        KC=Q1(C(v))-C(QB(v))
        terms=[C(B(KA))/6,C(KB)/6,2*KC/3,
               C(QB(x)-Q0(x))/2,(Q1(x)-Q0(x))/3]
        _,_,base=evolve(Q0(x),QA(a),QB(b),Q1(c))
        defect=Q1(y)-base
        np.testing.assert_allclose(defect,sum(terms),rtol=1e-10,atol=1e-10)
        vals=[pair(p,t) for t in terms]
        close(pair(p,defect),sum(vals),sum(map(abs,vals)))
        return terms,base
    # Synthetic moving observation cuts on actual physical z coordinates.
    # Threshold crosses one node; the support is not physical wall flux.
    threshold=g0[0]+2*dy+(g1[0]-g0[0])/2
    masks=[(g[0]+dy*np.arange(ny))[None,None,:,None]<threshold
           for g in (g0,g1,gm,g1)]
    assert np.any(masks[0]!=masks[-1])
    t,base=ledger(masks);tc,basec=ledger([~m for m in masks])
    for a0,b0 in zip(t,tc):
        np.testing.assert_allclose(a0+b0,0,atol=1e-10,rtol=0)
    np.testing.assert_allclose(base+basec,y,rtol=1e-10,atol=1e-10)
    assert np.linalg.norm(t[-1])>0
    print('PASS native order',order,'source moments, weighted transpose, five channels, complements')
if __name__=='__main__':
    for order in (3,4):check(order)
