import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize_scalar
import sympy as s
# a=1, c/a=r, z/a=x; exterior axial depolarization integral

def N(r,x):
    # substitution t=sqrt(c²+u); lower bound x
    return r*quad(lambda t:1/(t*t*(t*t+1-r*r)),x,np.inf,epsabs=1e-11)[0]
def L(r,x): return r/(x*(1+x*x-r*r))-N(r,x)
def response(r,x,k):
    n=N(r,r); T=1/(1+n*(k-1)); return T,1+(k-1)*T*L(r,x)
for r in [.001,.01,.05,.1,.5,1.]:
    x=r+.1/.1375; n=N(r,r); ell=L(r,x)
    assert ell>0 and abs(L(r,r)-(1-n))<1e-10
    for k in [.001,.1,1,10,1000]:
        T,E=response(r,r,k); assert abs(E-k*T)<1e-9
    print(r,n,response(r,x,.1)[1],1+ell/n,1-ell/(1-n))
# fixed clearance, optimize conductor limit over oblate aspect ratios
res=minimize_scalar(lambda r:-L(r,r+.1/.1375)/N(r,r),bounds=(.0001,1),method='bounded')
print('max numerical',res.x,1-res.fun,'total f=.25',1-.25*res.fun)
# sheet kernel, positive tangential stiffness: uniform normal field is unaffected
p,K,B=s.symbols('p K B',positive=True)
assert s.simplify(1/(2*K*p+B*p*p)/(1/(2*K*p))-2*K/(2*K+B*p))==0
print('PASS interface, sign, sheet propagator ratio')
