"""AT: Delannoy coordination, original torus response and conditional instrument.
Selected model controls, not an empirical observer or native kernel receipt.
"""
from itertools import product
from collections import Counter, deque
from math import comb, factorial, prod
import numpy as np
import sympy as s


def geometry():
    for m in range(1,6):
        h=Counter(sum(map(abs,x)) for x in product(range(-4,5),repeat=m))
        for r in range(5):
            assert sum(h[j] for j in range(r+1))==sum(2**k*comb(m,k)*comb(r,k) for k in range(min(m,r)+1))
    clip=Counter(abs(x)+abs(y) for x,y in product(range(-3,4),range(-2,3)) if abs(x)+abs(y)<=4)
    assert [clip[r] for r in range(5)]==[1,4,8,10,8]
    o=(0,0,0); dist={o:0}; paths={o:1}; todo=deque([o])
    while todo:
        x=todo.popleft()
        for j in range(3):
            for sign in (-1,1):
                y=list(x); y[j]=(y[j]+sign)%5; y=tuple(y)
                if y not in dist:
                    dist[y]=dist[x]+1; paths[y]=0; todo.append(y)
                if dist[y]==dist[x]+1: paths[y]+=paths[x]
    h=Counter(dist.values()); w=Counter()
    for x,d in dist.items():
        a=[min(i,5-i) for i in x]
        assert d==sum(a) and paths[x]==factorial(d)//prod(factorial(i) for i in a)
        w[d]+=paths[x]
    assert [h[r] for r in range(7)]==[1,6,18,32,36,24,8]
    assert [w[r] for r in range(7)]==[factorial(r)*comb(6,r) for r in range(7)]
    print('PASS 25 Delannoy balls, clipped 31 sites, 125 exact torus path counts')
    print('shells',list(h[r] for r in range(7)),'path sums',list(w[r] for r in range(7)))


def algebra():
    a,b,u,v,p,q=s.symbols('a b u v p q',real=True)
    # Derivative of a normalized conditional weight, and reconstruction.
    assert s.expand(u*(a+b)-a*(u+v)-(u*b-a*v))==0
    assert s.expand((u*b-a*v)+a*(u+v)-u*(a+b))==0
    assert s.expand((a+b)*(p*a+q*b)-(p*a+q*b)*(a+b))==0
    # Binary covariance numerator: E[AS]-E[A]E[S].
    x,y,t=s.symbols('x y t',real=True)
    cov=t*x*a+(1-t)*y*b-(t*x+(1-t)*y)*(t*a+(1-t)*b)
    assert s.expand(cov-t*(1-t)*(x-y)*(a-b))==0
    print('PASS conditional quotient and binary selection covariance identities')


def field():
    # Original N=5, a=1/5,c=3/2,mu=7/10. Local reference Fock vacuum,
    # not coupled ground state. One source-owned (3/5,4/5) pulse at origin.
    n=5; a=.2; c=1.5; mu=.7; ell=.4; theta=.7
    k=2*np.pi*np.fft.fftfreq(n,d=a)
    kx,ky,kz=np.meshgrid(k,k,k,indexing='ij')
    omega=np.sqrt(mu**2+4*c*c/a**2*(np.sin(a*kx/2)**2+np.sin(a*ky/2)**2+np.sin(a*kz/2)**2))
    # Characteristic functions of the right and wrong embedded records.
    count=0; maxerr=0.; examples=[]
    for t in (.02,.05,.1,.2):
        C=np.fft.ifftn(np.cos(t*omega)).real
        K=np.fft.ifftn(np.sin(t*omega)/omega).real
        for receiver in [(0,0,0),(1,0,0),(2,0,0),(1,1,0)]:
            # Translation-invariant row coefficients; kick at origin.
            alpha=ell*(1j*C-K)/np.sqrt(2)
            z=alpha[receiver]; ground=np.exp(-np.sum(abs(alpha)**2)/2)
            chi=np.array([ground,ground*(1-(4/5)**2*abs(z)**2+(3/5)*(4/5)*(z-z.conjugate()))])
            phase=ell*K[receiver]; h=1e-5
            def weights(e):
                return (1+np.real(np.exp(1j*(theta+e*phase))*chi))/4
            w=weights(0); dw=np.real(1j*phase*np.exp(1j*theta)*chi)/4
            D=w.sum(); dD=dw.sum(); p=w[0]/D
            dp=(dw[0]*D-w[0]*dD)/D**2
            numerical=(weights(h)[0]/weights(h).sum()-weights(-h)[0]/weights(-h).sum())/(2*h)
            maxerr=max(maxerr,abs(dp-numerical)); assert abs(dp-numerical)<1e-9
            assert np.all(w>=0) and np.all(w<=.5)
            # Complete final binary effect: success + failure retains each earlier record.
            assert np.allclose(w+(.5-w),[.5,.5])
            assert abs(D*dp+p*dD-dw[0])<1e-15
            count+=1
            if t==.1: examples.append((receiver,phase,D,p,dp))
    print('PASS',count,'field conditional response controls; max finite-difference error',maxerr)
    print('examples (receiver, kick phase slope, success, conditional right, derivative)',examples)
    # Positive Euclidean transfer differs from unitary transfer; same frequencies.
    tau=np.array([0.,.03,.08,.2]); w=omega.ravel()
    gram=np.exp(-(tau[:,None,None]+tau[None,:,None])*w)/(2*w)
    factor=np.exp(-tau[:,None]*w)/np.sqrt(2*w)
    assert np.max(abs(gram-factor[:,None,:]*factor[None,:,:]))<1e-15
    assert np.max(abs(-np.log(np.exp(-.1*w))/.1-w))<1e-12
    print('PASS 125 selected free-field OS mode Gram factors and positive-transfer inverse')


if __name__=='__main__':
    geometry(); algebra(); field()
