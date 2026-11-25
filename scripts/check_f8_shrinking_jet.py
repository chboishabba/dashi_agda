"""Independent displacement-based local Weyl jet covector on an interior patch.
The patch shrinks to the original brane event; not the raw three-slot receiver.
Only local patch arrays are required. Coefficients use existing native rows(t).
"""
import numpy as np


def diff(x,h,axis,order):
    x=np.moveaxis(x,axis,0);out=np.zeros_like(x)
    if order==1:
        out[:-1]+=x[1:]/(2*h);out[1:]-=x[:-1]/(2*h)
    elif order==2:
        out-=2*x/h**2;out[:-1]+=x[1:]/h**2;out[1:]+=x[:-1]/h**2
    else:raise ValueError('derivative order')
    return np.moveaxis(out,0,axis)


def bump(x,center,half):
    z=(x-center)/half;w=np.zeros(len(x));ok=abs(z)<1
    w[ok]=np.exp(1-1/(1-z[ok]**2))
    if not np.any(w) or np.any(w[:2]) or np.any(w[-2:]):raise ValueError('unresolved interior patch')
    return w/w.sum()


def patch(T,y,r,Tstar,rstar,delta):
    if delta<=0 or min(r)<=0:raise ValueError('positive interior radial patch')
    return (bump(T,Tstar-delta,delta/2)[:,None,None]*
            bump(y,1.5*delta,delta/2)[None,:,None]*
            bump(r,rstar,delta/2)[None,None,:])


def covector(c,weight,r,eps,ell,steps):
    """c[time,7] is a selected existing geometric row; no PDE substitution."""
    ht,hy,hr=steps;r=r[None,None,:];fac=(r/eps)**ell
    a=[weight*fac*c[:,i,None,None] for i in range(7)]
    D=lambda x,axis,order=1:diff(x,steps[axis],axis,order)
    return (-D(a[0],0)+D(a[1],0,2)-D(a[2],1)+D(D(a[3],0),1)
            +D(a[4],1,2)+D(a[5]+a[6],2,2)
            -D(((2*ell+2)*a[5]+2*ell*a[6])/r,2)
            +ell*(ell-1)*a[6]/r**2)


def direct(u,c,weight,r,eps,ell,steps):
    r=r[None,None,:];fac=(r/eps)**ell
    D=lambda axis,order=1:diff(u,steps[axis],axis,order)
    dr=D(2);drr=D(2,2)
    jets=[D(0),D(0,2),D(1),diff(D(0),steps[1],1,1),D(1,2),
          drr+(2*ell+2)*dr/r,drr+2*ell*dr/r+ell*(ell-1)*u/r**2]
    terms=[weight*fac*c[:,i,None,None]*z for i,z in enumerate(jets)]
    return sum(z.sum() for z in terms),sum(abs(z).sum() for z in terms)


def check():
    rng=np.random.default_rng(1547);worst=0.;count=0
    for n in (21,41,81):
        T=np.linspace(0,1,n);y=T.copy();r=1+T;h=1/(n-1)
        w=patch(T,y,r,.8,1.5,.2)
        u=rng.normal(size=(n,n,n))
        for ell in (0,2,4):
            for _ in range(6):
                c=rng.normal(size=(n,7));v,b=direct(u,c,w,r,.04,ell,(h,h,h))
                a=np.sum(covector(c,w,r,.04,ell,(h,h,h))*u)
                e=abs(a-v)/max(b,1e-300);assert e<1e-12
                worst=max(worst,e);count+=1
    return dict(checks=count,max_scaled_error=worst)


if __name__=='__main__':print(check())
