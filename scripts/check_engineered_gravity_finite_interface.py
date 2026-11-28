"""Conditional finite two-channel radion/material interface from a shared energy.

Reuse check_kk_same_action_stress, check_kk_radion_spherical_match and
check_kk_rebco_vortex_screening_maxcut. This is a linear EFT boundary problem,
not a microscopic REBCO constitutive derivation or a tensor gravity shield.
Canonical units; channel 1 is scalar, channel 2 material amplitude.
"""
import sympy as s

def block(K,V):
    """Hamiltonian first-order spatial transport, state (q, K q')."""
    n=K.rows
    if K.shape!=V.shape or K.cols!=n:
        raise ValueError("square matching matrices required")
    return s.zeros(n).row_join(K.inv()).col_join(V.row_join(s.zeros(n)))

def transfer(K,V,d):
    """Exact propagator in a constant region, including off-diagonal flux."""
    return (d*block(K,V)).exp()

def boundary_solve(P,left,right):
    """q(0)=left, p(d)=-right*q(d); return p(0), q(d).
    right is positive semidefinite exterior impedance. Singular solve fails.
    """
    n=len(left)
    A,B,C,D=P[:n,:n],P[:n,n:],P[n:,:n],P[n:,n:]
    p0=-(D+right*B).inv()*(C+right*A)*left
    return p0,A*left+B*p0

def check():
    # Shared variational principle E=int( q'^T K q'+q^T V q )/2 dx.
    # Flux continuity is Kq', not generally q'; preserves Green pairing.
    a,b,c,d,e,f=s.symbols('a b c d e f',real=True)
    K=s.Matrix([[a,b],[b,c]])
    V=s.Matrix([[d,e],[e,f]])
    J=s.zeros(2).row_join(s.eye(2)).col_join((-s.eye(2)).row_join(s.zeros(2)))
    L=block(K,V)
    assert all(s.factor(x)==0 for x in L.T*J+J*L)
    # Inhabited mixed geometry with noncommuting K,V, positive both.
    K=s.Matrix([[2,1],[1,2]])
    V=s.Matrix([[3,0],[0,1]])
    assert K*V!=V*K and K.det()>0 and V.det()>0
    # Explicit exact rational Cayley step: discrete symplectic control,
    # not substituted for the continuum matrix exponential.
    L=block(K,V)
    step=(s.eye(4)-L/20).inv()*(s.eye(4)+L/20)
    assert step.T*J*step==J
    # Exact continuum two-channel fixture via orthogonal mode decomposition.
    O=s.Matrix([[3,-4],[4,3]])/5
    K=s.eye(2); V=O*s.diag(1,4)*O.T
    h=s.symbols('h',positive=True)
    C=O*s.diag(s.cosh(h),s.cosh(2*h))*O.T
    B=O*s.diag(s.sinh(h),s.sinh(2*h)/2)*O.T
    D=O*s.diag(s.sinh(h),2*s.sinh(2*h))*O.T
    P=C.row_join(B).col_join(D.row_join(C))
    assert all(s.trigsimp(x)==0 for x in P.diff(h)-block(K,V)*P)
    assert P.subs(h,0)==s.eye(4)
    assert all(s.trigsimp(s.expand(x))==0 for x in P.T*J*P-J)
    # Zero outgoing impedance: explicit mixed transmission and source split.
    incident=s.Matrix([1,0])
    T=O*s.diag(1/s.cosh(h),1/s.cosh(2*h))*O.T
    receiver=T*incident
    assert s.factor(receiver[1]-s.Rational(12,25)*(1/s.cosh(h)-1/s.cosh(2*h)))==0
    assert receiver.subs(h,0)==incident
    # Finite nonzero exterior impedance, exact algebraic check at h=log(2).
    P0=P.subs(h,s.log(2)).applyfunc(s.simplify)
    Z=s.diag(1,2)
    p0,q1=boundary_solve(P0,incident,Z)
    end=P0*incident.col_join(p0)
    assert end[:2,:]==q1 and end[2:,:]==-Z*q1
    assert all(x.is_Rational for x in q1)
    # Receiver observable: exterior scalar acceleration proportional to
    # derivative, not amplitude. A constant scalar offset is invisible.
    beta,m=s.symbols('beta m',positive=True)
    x=s.symbols('x',nonnegative=True)
    phi=q1[0]*s.exp(-m*x)
    assert s.diff(phi,x).subs(x,0)==-m*q1[0]
    assert s.diff(phi+7,x)==s.diff(phi,x)
    # Ordinary tensor baseline remains independent in this EFT.
    gn=s.symbols('g_N',positive=True)
    assert (gn+beta*s.diff(phi,x)).subs(beta,0)==gn
    print("PASS mixed finite interface, canonical flux, Green pairing, inverse boundary and derivative receiver")
    print("OPEN physical material Hessian, 5D parent, tensor channel and calibrated source")

if __name__=="__main__":check()
