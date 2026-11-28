"""Full quadratic covariant Ricci ordered Fourier kernel, scalar/vector/TT attachment."""
import numpy as np
import sympy as s
from itertools import product

eta=np.diag([-1.,1.,1.,1.,1.])

def connection(dh):
    return np.einsum('al,lbc->abc',eta,(dh.transpose(1,0,2)+dh.transpose(1,2,0)-dh)/2)


def ordered(p,q,z):
    """Relative conformal TT jets (H, dH, ddH), index order T,x,y,w,z.
    Return ordered lower Ricci coefficient; integrate all ordered pairs.
    Derivative indices precede matrix indices. Supports complex Fourier jets.
    """
    H,dh,_=p; G,dg,ddg=q
    C=connection(dh); D=connection(dg)
    dD=np.array([connection(ddg[a]) for a in range(5)])
    P=-eta@H
    C2=np.einsum('al,lbc->abc',P,D)
    dC2=np.einsum('mal,lbc->mabc',-np.einsum('al,mlb->mab',eta,dh),D)+np.einsum('al,mlbc->mabc',P,dD)
    R=np.einsum('aaij->ij',dC2)-np.einsum('jaia->ij',dC2)+np.einsum('aal,lij->ij',C,D)-np.einsum('ajl,lia->ij',C,D)
    # Conformal transformation: H has only spatial components and trace zero.
    R-=eta*np.trace(H@dg[4])/(2*z)
    return R


def jets(k,E,f,ft,fz,ftt,ftz,fzz):
    k=np.asarray(k); A=np.zeros((5,5),complex);A[1:4,1:4]=E
    v=np.r_[ft,1j*k*f,fz]; M=np.zeros((5,5),complex)
    M[0,0]=ftt;M[4,4]=fzz;M[0,4]=M[4,0]=ftz
    M[1:4,1:4]=-np.outer(k,k)*f;M[0,1:4]=M[1:4,0]=1j*k*ft;M[4,1:4]=M[1:4,4]=1j*k*fz
    return f*A,v[:,None,None]*A,M[:,:,None,None]*A


def split(Q,k,z):
    """Physical source -Q for on-shell first-order TT, rotate k to x externally.
    Scalar Einstein-frame source and vector mixed Ricci current; Poincare chart.
    Nonzero k along x. No division by k in this attachment.
    """
    F=-np.asarray(Q); idx=[0,4,1]; perp=z*z*(F[2,2]+F[3,3])/2
    S=F[np.ix_(idx,idx)]+2*perp*eta[np.ix_(idx,idx)]/z**2
    # vector current in base (T,z,x), sqrt|g3|*a^2=z^-5 in Poincare coordinates.
    J=-2/z**5*(z*z*eta[np.ix_(idx,idx)]@F[np.ix_(idx,[2,3])])
    return S,perp,J


def exact():
    # Independent coordinate Christoffel expansion on complex cross pair.
    T,x,y,w,z=s.symbols('T x y w z',real=True); X=(T,x,y,w,z); ix=range(5)
    E=s.diag(0,1,-1); G=s.Matrix([[0,0,1],[0,0,0],[1,0,0]])
    f=1+T*z; j=T*T+z**3; a,b=s.symbols('a b')
    h=s.diag(0,E*f*s.exp(s.I*x)*a+G*j*s.exp(2*s.I*y)*b,0)/z**2
    e=s.diag(-1,1,1,1,1); g=e/z**2; gi=z*z*e
    def conn(d,inv):return {(i,k,l):sum(inv[i,m]*(d[m,l].diff(X[k])+d[m,k].diff(X[l])-d[k,l].diff(X[m]))/2 for m in ix) for i,k,l in product(ix,repeat=3)}
    C0=conn(g,gi); C1a=conn(h,gi); C1b=conn(g,-gi*h*gi); C1={i:s.expand(C1a[i]+C1b[i]) for i in C0}
    C2a=conn(h,-gi*h*gi); C2b=conn(g,gi*h*gi*h*gi); C2={i:s.expand(C2a[i]+C2b[i]) for i in C0}
    def ric(i,j):
        R=sum(C2[k,i,j].diff(X[k])-C2[k,i,k].diff(X[j]) for k in ix)+sum(C0[k,k,l]*C2[l,i,j]+C1[k,k,l]*C1[l,i,j]+C2[k,k,l]*C0[l,i,j]-C0[k,j,l]*C2[l,i,k]-C1[k,j,l]*C1[l,i,k]-C2[k,j,l]*C0[l,i,k] for k,l in product(ix,repeat=2))
        return s.expand(R).coeff(a,1).coeff(b,1)
    pt={T:s.Rational(2,3),z:s.Rational(3,4),x:0,y:0,w:0}; ev=lambda F:complex(F.subs(pt))
    actual=np.array([[ev(ric(i,j)) for j in ix] for i in ix])
    def js(k,A,F):return jets(k,np.array(A,float),*[ev(v) for v in (F,F.diff(T),F.diff(z),F.diff(T,2),F.diff(T,z),F.diff(z,2))])
    P=js([1,0,0],E,f);Q=js([0,2,0],G,j)
    got=ordered(P,Q,.75)+ordered(Q,P,.75)
    assert np.allclose(got,actual,rtol=1e-12,atol=1e-12),np.max(abs(got-actual))
    assert np.allclose(got,got.T)
    assert np.max(abs(got.imag))>0 and np.max(abs(got.real))>0
    print('25 full complex Ricci cross-pair components agree; max defect',np.max(abs(got-actual)))

if __name__=='__main__':exact()
