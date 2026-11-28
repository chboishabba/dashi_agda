"""F8 Fourier-pair off-shell Bianchi transport.
Consumes ordered Ricci kernel and geometric_constraints. Third jets are derivatives
of the actual interpolant, never silently replaced by the vacuum equation.
Finite diagnostics are not interval enclosures or full histories.
"""
import numpy as np
from check_f8_full_pair_source import ordered, connection, eta


def background(z):
    return np.array([[[-(int(a==m)*int(b==4)+int(a==b)*int(m==4))+eta[m,b]*eta[a,4] for b in range(5)] for a in range(5)] for m in range(5)])/z


def divergence(A,dA,z):
    B=background(z)
    cov=np.array([dA[m]-B[m].T@A-A@B[m] for m in range(5)])
    return z*z*np.einsum('ac,acb->b',eta,cov)


def linear(p,z):
    H,dH,ddH,dddH=p
    L=-(np.einsum('ab,abij->ij',eta,ddH)-3*dH[4]/z)/2
    dL=-(np.einsum('ab,mabij->mij',eta,dddH)-3*ddH[:,4]/z)/2
    dL[4]-=3*dH[4]/(2*z*z)
    return L,dL


def trace_reverse(A):
    return A-eta*np.trace(eta@A)/2


def pair(p,q,z):
    """Sum both orders; no angular symmetry projection or PDE residual removal."""
    H,dh,_,_=p; G,dg,_,_=q
    Q=ordered(p[:3],q[:3],z)+ordered(q[:3],p[:3],z)
    dQ=np.array([ordered(tuple(a[m] for a in p[1:]),q[:3],z)
                 +ordered(p[:3],tuple(a[m] for a in q[1:]),z)
                 +ordered(tuple(a[m] for a in q[1:]),p[:3],z)
                 +ordered(q[:3],tuple(a[m] for a in p[1:]),z) for m in range(5)])
    dQ[4]+=eta*(np.trace(H@dg[4])+np.trace(G@dh[4]))/(2*z*z)
    R=divergence(trace_reverse(Q),np.array([trace_reverse(a) for a in dQ]),z)
    L,dL=linear(p,z); M,dM=linear(q,z)
    corr=eta*(np.trace(H@M)+np.trace(G@L))/2
    dcorr=np.array([eta*(np.trace(dh[m]@M+H@dM[m]+dg[m]@L+G@dL[m]))/2 for m in range(5)])
    B=background(z)
    # C indexed (upper, derivative, lower), covariant divergence correction.
    def work(H,dh,M,dM):
        C=connection(dh); C[4]+=H/z
        cov=np.array([dM[m]-B[m].T@M-M@B[m] for m in range(5)])
        return (z*z*np.einsum('ac,cab->b',eta@H@eta,cov)
                +z*z*np.einsum('ac,dca,db->b',eta,C,M)
                +z*z*np.einsum('ac,dcb,ad->b',eta,C,M))
    predicted=work(H,dh,M,dM)+work(G,dg,L,dL)-divergence(corr,dcorr,z)
    return Q,R,predicted,L,M


def polynomial_jets(k,E,f,T,z):
    """Independent polynomial Fourier derivative oracle through order three."""
    import sympy as s
    from itertools import product
    t,y=s.symbols('t y'); A=np.zeros((5,5),complex); A[1:4,1:4]=E
    def scalar(ids):
        return complex(s.diff(f,t,ids.count(0),y,ids.count(4)).subs({t:T,y:z}))*np.prod([1j*k[i-1] for i in ids if 1<=i<=3])
    out=[scalar(())*A]
    for n in (1,2,3):
        a=np.empty((5,)*n+(5,5),complex)
        for ids in product(range(5),repeat=n):a[ids]=scalar(ids)*A
        out.append(a)
    return tuple(out)


def run():
    import sympy as s
    t,y=s.symbols('t y'); T,z=.67,.75
    E=np.diag([0.,1.,-1.]); G=np.array([[0.,0.,1.],[0.,0.,0.],[1.,0.,0.]])
    p=polynomial_jets([1,0,0],E,1+t*y+t**3,T,z)
    q=polynomial_jets([0,2,0],G,t*t+y**3+t*y*y,T,z)
    Q,R,pred,L,M=pair(p,q,z)
    print('off-shell R',R,'predicted',pred,'defect',np.max(abs(R-pred)))
    assert np.max(abs(R))>1e-4 and np.allclose(R,pred,rtol=1e-11,atol=1e-11)
    # On-shell nonparallel spatial Fourier solutions e^(ikT), z independent.
    # Complex polynomial oracle not needed: jets are plane-wave products.
    def wave(k,E):
        a=np.r_[np.linalg.norm(k),k,0.]*1j; A=np.zeros((5,5),complex);A[1:4,1:4]=E
        return (A,np.einsum('a,ij->aij',a,A),np.einsum('a,b,ij->abij',a,a,A),np.einsum('a,b,c,ij->abcij',a,a,a,A))
    Q,R,pred,L,M=pair(wave([1,0,0],E),wave([0,2,0],G),z)
    assert np.max(abs(Q))>0 and np.max(abs(L))+np.max(abs(M))<1e-12
    assert np.max(abs(R))+np.max(abs(pred))<1e-11
    print('on-shell source nonzero; Bianchi defect',np.max(abs(R)))

if __name__=='__main__':run()
