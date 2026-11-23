"""Fixed-N bosonic C3 ring; dimensionless model, not calibrated gravity."""
import numpy as np
from scipy.linalg import eigh
from math import sqrt, pi

def operators(N,U,J,theta):
    states=[(i,j,N-i-j) for i in range(N+1) for j in range(N-i+1)]
    idx={v:i for i,v in enumerate(states)}; n=len(states)
    C=np.zeros((n,n)); H=np.zeros((n,n),complex); O=np.zeros((n,n)); Q=np.zeros((n,n)); V=np.zeros((n,n),complex)
    for k,v in enumerate(states):
        C[idx[(v[2],v[0],v[1])],k]=1
        Q[k,k]=sum(i*(i-1) for i in v)/2
        H[k,k]=U*Q[k,k]; O[k,k]=v[0]-(v[1]+v[2])/2
        for i in range(3):
            j=(i+1)%3
            if not v[i]:continue
            w=list(v);w[i]-=1;w[j]+=1;l=idx[tuple(w)]
            a=-J*np.exp(1j*theta)*sqrt(v[i]*(v[j]+1))
            H[l,k]+=a;H[k,l]+=a.conjugate()
            V[l,k]+=a*(1j);V[k,l]+=(a*1j).conjugate()
    assert np.allclose(C@C@C,np.eye(n)) and np.allclose(C@H,H@C)
    return H,O,Q,V,C

def response(N,U,J,theta):
    H,O,Q,V,C=operators(N,U,J,theta);e,W=eigh(H);gap=e[1:]-e[0];g=W[:,0]
    if gap[0]<1e-9:return None
    def chi(A,B):
        a=W[:,1:].conj().T@A@g;b=W[:,1:].conj().T@B@g
        return 2*np.real(np.sum(a.conj()*b/gap))
    # gauge-invariant modulus coupling to U: U(q)=U exp(-3q/2)
    A=-1.5*U*Q
    c=chi(O,O);mixed=chi(O,A)
    assert abs(mixed)<1e-7*max(1,c)
    assert abs(chi(O,V))<1e-7*max(1,c)
    h=1e-4
    fd=-(eigh(H+h*O,eigvals_only=True)[0]+eigh(H-h*O,eigvals_only=True)[0]-2*e[0])/h**2
    assert abs(fd-c)<1e-3*max(1,c)
    return len(e),gap[0],c,chi(A,A),mixed
if __name__=='__main__':
    for N in (1,2,3,6,9):
        for U in (0,1,4):
            for f in (0,.9,.99):
                print(N,U,f,response(N,U,1,f*pi/3))
    print('PASS symmetry, interacting spectra, forbidden mixed vertices and finite-difference susceptibility')
