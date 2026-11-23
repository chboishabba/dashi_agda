"""Independent original TT source moment and weighted native spectral audit.
No change to the production emitter; dimensionless radius u=r/eps.
"""
import numpy as np
import sympy as s
from scipy.special import roots_legendre
from scipy.linalg import eigh_tridiagonal

def run():
    u=s.symbols('u', positive=True); f=s.Function('f')(u)
    D=lambda n:s.diff(f,u,n)
    forms=[s.Rational(2,5)*(D(4)+4*D(3)/u),s.Rational(4,7)*(D(4)+D(3)/u-6*D(2)/u**2+6*D(1)/u**3)/u**2,s.Rational(1,35)*(D(4)-6*D(3)/u+15*D(2)/u**2-15*D(1)/u**3)/u**4]
    # Formal adjoint under integration by parts; boundary terms checked below.
    bump=s.exp(1-1/(1-u*u)); x,w=roots_legendre(512); x=(x+1)/2;w=w/2
    for q,form in enumerate(forms):
        d=3+4*q
        coeff=[]
        for j in range(5):
            p=s.expand(u**(d-1+2*j)*form)
            adj=s.expand(sum((-1)**k*s.diff(p.coeff(D(k)),u,k) for k in range(1,5)))
            expected=s.simplify(adj/u**(d-5-2*q+2*j)) if q==0 else None
            # Lower-end boundary terms vanish for even smooth bumps, or by powers of u.
            boundary=s.expand(sum(sum((-1)**k*s.diff(p.coeff(D(n)),u,k)*D(n-k-1) if n-k-1 else (-1)**k*s.diff(p.coeff(D(n)),u,k)*f for k in range(n)) for n in range(1,5)))
            assert s.limit(boundary.subs(f,1+u**2+u**4+u**6).doit(),u,0)==0
            fun=s.lambdify(u,form.subs(f,bump).doit(),'numpy')
            val=np.dot(w,x**(d-1+2*j)*fun(x)); target=0. if adj==0 else np.dot(w,s.lambdify(u,adj*bump,'numpy')(x))
            assert abs(val-target)<1e-8*max(1,abs(target)),(q,j,val,target)
            coeff.append(str(adj))
        print('ell',2*q,'moment kernels',coeff,flush=True)
        for h in (.2,.15,.1,.075,.05):
            # Original physical outer radius 3.01 / .04, active Dirichlet nodes.
            n=int(np.ceil(3.01/(.04*h))); rg=np.arange(n)*h
            lo=np.maximum(0,rg-h/2);hi=rg+h/2; mass=(hi**d-lo**d)/d
            src=np.zeros(n)
            for i in np.where(lo<1)[0]:
                a,b=lo[i],min(1,hi[i]); z=a+(b-a)*x
                src[i]=(b-a)*np.dot(w,z**(d-1)*fun(z))/mass[i]
            moments=[np.dot(mass*src,rg**(2*j)) for j in range(5)]
            # Native weighted Green form uses shell face flux; origin consistent.
            face=hi**(d-1)/h; diagonal=-(face+np.r_[0,face[:-1]])/mass
            off=face[:-1]/np.sqrt(mass[:-1]*mass[1:]); lam,V=eigh_tridiagonal(-diagonal,-off)
            assert lam[0]>0
            z=V.T@(np.sqrt(mass)*src); norm=np.dot(z,z)
            assert np.isclose(norm,np.dot(mass,src*src),rtol=1e-11)
            print('h',h,'moments',moments,'spectral energy fraction kh>1',np.dot(z[lam*h*h>1],z[lam*h*h>1])/norm,flush=True)
if __name__=='__main__':run()
