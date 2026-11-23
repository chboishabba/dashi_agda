"""Diagnostic r^2 hat-function weak source load on native FV mass; no emitter replacement."""
import numpy as np
import sympy as s
from scipy.special import roots_legendre, spherical_jn
from ksw668_f8_fv_source_flux import exact_cell_averages, primitives, cell_mass


def run():
    a,b,u=s.symbols('a b u', real=True)
    left=(b*b-u*u)/(b*b-a*a);right=(u*u-a*a)/(b*b-a*a)
    assert s.cancel(left+right-1)==0
    assert s.cancel(a*a*left+b*b*right-u*u)==0
    k=np.array([.1,.25,.5,1.,2.,4.,8.,16.,32.]); eps=.04
    for nodes in (128,256):
        x,w=roots_legendre(nodes);x=(x+1)/2; w=w/2
        B=(w*x*x*np.exp(1-1/(1-x*x)))@np.sinc(x[:,None]*k/np.pi)
        target=np.array([.4*k**4,-60/7*k*k,np.full_like(k,27)])*B
        rows=[]
        for dr in (.008,.006,.004,.003,.002):
            h=dr/eps;r=np.arange(int(np.ceil(1/h))+2)*h
            src=exact_cell_averages(eps,r*eps,dr)
            for q,ell in enumerate((0,2,4)):
                d=3+2*ell; W=((r+h/2)**d-np.maximum(0,r-h/2)**d)/d
                load=np.zeros_like(r); p=primitives()[q]
                for j in range(len(r)-1):
                    a,b=r[j:j+2];c=min(b,1.)
                    if a>=c:continue
                    z=a+(c-a)*x
                    # Integral of u^2 times weighted source via integration by parts.
                    m0=cell_mass(ell,a,c)
                    m2=(0 if c==1 else c*c*p(c))-(0 if a==0 else a*a*p(a))-(c-a)*np.dot(w,2*z*p(z))
                    if ell==4:m2+=(c-a)*np.dot(w,27*z**4*np.exp(1-1/(1-z*z)))
                    load[j]+=(b*b*m0-m2)/(b*b-a*a)
                    load[j+1]+=(m2-a*a*m0)/(b*b-a*a)
                m0=load.sum();m1=load@(r*r)
                expected0=0 if ell<4 else 27*B[0] # replace below with zero-frequency integral
                B0=np.dot(w,x*x*np.exp(1-1/(1-x*x)));B4=np.dot(w,x**4*np.exp(1-1/(1-x*x)))
                expected0=0 if ell<4 else 27*B0;expected1=[0,120*B0,99*B4][q]
                assert abs(m0-expected0)<1e-8 and abs(m1-expected1)<1e-8,(dr,ell,m0,m1)
                z=r[:,None]*k; phi=np.ones_like(z);np.divide(spherical_jn(ell,z)*[1,15,945][q],z**ell,out=phi,where=z!=0)
                old=(W*src[q])@phi;new=load@phi
                olderr=np.linalg.norm(old-target[q])/np.linalg.norm(target[q]);newerr=np.linalg.norm(new-target[q])/np.linalg.norm(target[q])
                rows.append([dr,ell,m0,m1,old[0],new[0],olderr,newerr,r[np.flatnonzero(load)[-1]]*eps])
        if nodes==128: previous=np.array(rows)
        else:
            np.testing.assert_allclose(rows,previous,rtol=1e-7,atol=1e-8)
            for row in rows:print('dr ell M0 M1 old(k=.1) new(k=.1) olderr newerr maxnode',*row)
    print('PASS 2 exact basis identities, 30 moment checks per quadrature, 128/256 parity')
if __name__=='__main__':run()
