"""AU: weighted impulse inverse, anisotropic noncompact response, OS controls."""
from itertools import product
from math import comb, factorial
import numpy as np
import sympy as s


def weighted():
    sites=list(product(range(5),repeat=3)); n=len(sites); idx={x:i for i,x in enumerate(sites)}
    W=np.zeros((n,n),dtype=np.int64)
    for i,x in enumerate(sites):
        for j in range(3):
            y=list(x); y[j]=(y[j]+1)%5; k=idx[tuple(y)]
            W[i,k]=W[k,i]=1+(3*i+7*k+j)%11
    mass=np.arange(n,dtype=np.int64)%7
    L=np.diag(mass+W.sum(axis=1))-W
    # The observed column is q'''(0) from unit velocity at each marked source.
    J=np.column_stack([-L@v for v in np.eye(n,dtype=np.int64)])
    recovered=J.copy(); np.fill_diagonal(recovered,0)
    assert np.array_equal(recovered,W)
    assert np.array_equal(-J.sum(axis=0),mass)
    assert np.array_equal(np.diag(mass+recovered.sum(axis=1))-recovered,L)
    # Weighted shortest path first response from original origin.
    distance=np.array([sum(min(i,5-i) for i in x) for x in sites])
    v=np.eye(n,dtype=np.int64)[:,0]; walk=v.copy(); count=0
    for d in range(7):
        assert np.all(v[distance>d]==0)
        assert np.array_equal(v[distance==d],walk[distance==d])
        count+=np.count_nonzero(distance>=d)
        v=-L@v; walk=W@walk
    # Signed diamond: two equal length products cancel, although L is positive.
    M=s.Matrix([[5,-1,-1,0],[-1,5,0,-1],[-1,0,5,1],[0,-1,1,5]])
    assert (M**2)[3,0]==0 and all(sum(abs(M[i,j]) for j in range(4) if i!=j)<M[i,i] for i in range(4))
    print('PASS',n*n,'marked matrix entries,',n,'mass residuals,',count,'weighted shortest/preceding controls; signed cancellation')


def anisotropic():
    # Direction stencil: three axes and three pairwise diagonal directions.
    V=s.Matrix([[1,0,0],[0,1,0],[0,0,1],[1,1,0],[1,0,1],[0,1,1]])
    k=s.symbols('k0:6'); p=s.Matrix(s.symbols('p0:3'))
    D=V.T*s.diag(*k)*V
    back=[D[0,0]-D[0,1]-D[0,2],D[1,1]-D[0,1]-D[1,2],D[2,2]-D[0,2]-D[1,2],D[0,1],D[0,2],D[1,2]]
    assert all(s.expand(a-b)==0 for a,b in zip(back,k))
    assert s.expand((p.T*D*p)[0]-sum(k[j]*(V[j,:]*p)[0]**2 for j in range(6)))==0
    # Distinct positive stencil sets with same continuum D, but different quartic dispersion.
    ex=s.Matrix([1,0,0]); ey=s.Matrix([0,1,0]); ep=ex+ey; em=ex-ey
    assert ep*ep.T+em*em.T==2*(ex*ex.T+ey*ey.T)
    assert s.expand((ep.dot(p))**4+(em.dot(p))**4-2*(ex.dot(p)**4+ey.dot(p)**4))==12*p[0]**2*p[1]**2
    print('PASS six-coefficient principal inverse; same principal/different fourth moment')


def continuum():
    # Gaussian Fourier test; full R^3 continuum integral approximated by
    # a common finite quadrature. Numerical comparison is not a certificate.
    c=np.array([1.5,1.,.75]); mu=.7; t=.3
    grid=np.linspace(-16,16,129); dp=grid[1]-grid[0]
    p=np.meshgrid(grid,grid,grid,indexing='ij',sparse=True)
    lam=mu**2+sum(c[j]**2*p[j]**2 for j in range(3))
    weight=np.exp(-sum(x*x for x in p)/2)/(2*np.pi)**3
    K=lambda x: t*np.sinc(t*np.sqrt(x)/np.pi)
    target=np.sum(weight*K(lam))*dp**3; prev=None
    for a in (1/8,1/16,1/32,1/64):
        la=mu**2+sum(4*c[j]**2/a**2*np.sin(a*p[j]/2)**2 for j in range(3))
        delta=a*a*sum(c[j]**2*p[j]**4 for j in range(3))/12
        assert np.all(lam-la>=-1e-10) and np.all(lam-la<=delta+1e-10)
        err=abs(np.sum(weight*K(la))*dp**3-target)
        bound=a*a*t**3*3*sum(c*c)/(72*(2*np.pi)**1.5)
        assert err<=bound
        print('noncompact Gaussian paired response',a,'error',err,'analytic bound',bound,'order',None if prev is None else np.log2(prev/err)); prev=err
    # Exact zero branch and stable positive-transfer inverse at sampled modes.
    assert K(0)==t
    omega=np.sqrt(np.array([0.,.49,1.,25.,100.]))
    assert np.allclose(-np.log(np.exp(-.125*omega))/.125,omega)
    assert abs(np.exp(-1j*.125*(1+2*np.pi/.125))-np.exp(-1j*.125))<1e-14
    print('PASS zero response and positive-transfer/phase alias control')


if __name__=='__main__':
    weighted(); anisotropic(); continuum()
