"""Original native E4/SMS displacement window; sparse wall-only covectors.
Reuses midpoint-window temporal SBP, not a pointwise or direct E5 estimate.
"""
import numpy as np


def window_rows(t,h,rx,eps,dr,nr,center,half):
    t=np.asarray(t);n=len(t);T=np.arange(n)*h
    if n<5 or min(h,rx,eps,dr,half)<=0 or np.any(t<=0):raise ValueError('window geometry')
    if not (h<center-half and center+half<T[-1]-h):raise ValueError('window must be strictly interior')
    z=(T-center)/half;chi=np.zeros(n);inside=abs(z)<1
    chi[inside]=np.exp(1-1/(1-z[inside]**2));chi/=h*chi.sum()
    if not np.isfinite(chi).all():raise ValueError('unresolved window')
    idx=np.arange(int(rx/dr)-1,int(rx/dr)+3)
    if idx[0]<0 or idx[-1]>=nr-1:raise ValueError('active receiver stencil')
    V=(idx-rx/dr)[None,:]**np.arange(4)[:,None]
    w,dw,dd=np.linalg.solve(V,np.diag([1,1/dr,2/dr**2,0])[:,:3]).T
    fac=(rx/eps)**np.arange(0,6,2);W=fac[:,None]*w
    L=fac[:,None]*(dd+(2*np.arange(0,6,2)+2)[:,None]*dw/rx)
    b=1/t;S=np.sqrt(1+t*t)/t;J=-1/(t*np.sqrt(1+t*t))
    rows=[];original=[]
    for scale,extra,sign in ((.25,0,-1),(.5,2,1)):
        a2=-scale*b*b*S*S*chi;a1=-scale*b*b*(J+extra*S)*chi;a0=sign*scale*b*b*chi
        p=np.zeros(n);p[:-2]+=a2[1:-1]/h**2-a1[1:-1]/(2*h)
        p[1:-1]-=2*a2[1:-1]/h**2;p[2:]+=a2[1:-1]/h**2+a1[1:-1]/(2*h)
        rows.append(h*(p[:,None,None]*W+a0[:,None,None]*L));original.append((a2,a1,a0))
    return idx,np.array(rows),original,W,L


def check():
    rng=np.random.default_rng(1547);worst=0.;count=0
    for n in (41,81,161):
        h=1/(n-1);t=1+11*np.arange(n)*h
        for dr in (.008,.006):
            idx,rows,coef,W,L=window_rows(t,h,.053,.04,dr,20,.65,.1)
            u=rng.normal(size=(n,3,4));u0=np.sum(u*W,axis=-1);lap=np.sum(u*L,axis=-1)
            d1=(u0[2:]-u0[:-2])/(2*h);d2=(u0[2:]-2*u0[1:-1]+u0[:-2])/h**2
            for row,(a2,a1,a0) in zip(rows,coef):
                terms=h*(a2[1:-1,None]*d2+a1[1:-1,None]*d1+a0[1:-1,None]*lap[1:-1])
                got=np.sum(row*u,axis=(0,2));want=terms.sum(0)
                err=np.max(abs(got-want)/np.maximum(1,abs(terms).sum(0)))
                assert err<1e-12;worst=max(worst,err);count+=3
            assert not np.any(rows[:,[0,-1]])
    print(dict(checks=count,max_normalized_error=worst))

if __name__=='__main__':check()
