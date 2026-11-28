"""Second-order synchronous shell curvature and forced stress energy.
Classical Gauss/Codazzi and ADM identities; original F8 specialization.
No claim of a coupled 5D evolution or independent matter realization.
"""
import sympy as s
from itertools import product


def scalar_curvature_coefficients(t, xyz, H, J):
    """g4=-dt²+t²(I+e H+e² J), TT H. Return R1,R2 and expansion rate theta2."""
    D=lambda X,i: X.diff(xyz[i])
    lap=lambda X: sum((D(D(X,i),i) for i in range(3)),s.zeros(3))
    lin=lambda X: sum(s.diff(X[i,j],xyz[i],xyz[j]) for i,j in product(range(3),repeat=2))-sum(s.diff(s.trace(X),x,2) for x in xyz)
    grad2=sum(D(H,k)[i,j]**2 for i,j,k in product(range(3),repeat=3))
    cross=sum(D(H,l)[k,i]*D(H,k)[i,l] for i,k,l in product(range(3),repeat=3))
    theta=s.trace(J.diff(t)-H*H.diff(t))/2
    R1=lin(H)/t**2+4*s.trace(H.diff(t))/t+s.trace(H.diff(t,2))
    R2=(lin(J)+s.trace(H*lap(H))+3*grad2/4-cross/2)/t**2+8*theta/t+2*s.diff(theta,t)+s.trace(H.diff(t)**2)/4
    return s.expand(R1),s.expand(R2),s.expand(theta)


def direct_ricci3(H,J,xyz):
    # independent coefficient expansion of Christoffel and Ricci scalar.
    n=3; ix=range(n); g1=H;g2=J
    G=lambda h,k,i,j:(s.diff(h[k,j],xyz[i])+s.diff(h[k,i],xyz[j])-s.diff(h[i,j],xyz[k]))/2
    C=s.MutableDenseNDimArray.zeros(n,n,n); D=s.MutableDenseNDimArray.zeros(n,n,n)
    for k,i,j in product(ix,repeat=3):
        C[k,i,j]=G(g1,k,i,j)
        D[k,i,j]=G(g2,k,i,j)-sum(H[k,l]*G(g1,l,i,j) for l in ix)
    R1=s.zeros(n); R2=s.zeros(n)
    for i,j in product(ix,repeat=2):
        R1[i,j]=sum(s.diff(C[k,i,j],xyz[k])-s.diff(C[k,i,k],xyz[j]) for k in ix)
        R2[i,j]=sum(s.diff(D[k,i,j],xyz[k])-s.diff(D[k,i,k],xyz[j]) for k in ix)+sum(C[k,k,l]*C[l,i,j]-C[k,j,l]*C[l,i,k] for k,l in product(ix,repeat=2))
    return s.expand(s.trace(R1)),s.expand(s.trace(R2-H*R1))


def run():
    t=s.symbols('t',positive=True); x,y,z=s.symbols('x y z',real=True); xyz=(x,y,z)
    # Three nonparallel transverse waves with mixed polarization and arbitrary J.
    H=s.diag(0,(t-x)**2,-(t-x)**2)+s.Matrix([[0,0,(t-y)**2],[0,0,0],[(t-y)**2,0,0]])+s.diag((t-z)**2,-(t-z)**2,0)
    J=s.Matrix([[x*x*t,y*z,t*x],[y*z,t*y*y,x*z],[t*x,x*z,z*z*t*t]])
    assert s.trace(H)==0
    assert all(sum(s.diff(H[i,j],xyz[i]) for i in range(3))==0 for j in range(3))
    R1,R2,theta=scalar_curvature_coefficients(t,xyz,H,J)
    S1,S2=direct_ricci3(H,J,xyz)
    assert R1==0 and S1==0
    # independent expansion of mixed temporal extrinsic curvature
    e=s.symbols('e'); B=s.eye(3)+e*H+e**2*J
    inv=s.eye(3)-e*H+e**2*(H*H-J)
    K=(s.eye(3)/t+inv*B.diff(t)/2).applyfunc(s.expand)
    K0=K.subs(e,0); K1=K.diff(e).subs(e,0); K2=K.diff(e,2).subs(e,0)/2
    time2=2*s.trace(K0*K2)+s.trace(K1*K1)+2*s.trace(K0)*s.trace(K2)+s.trace(K1)**2+2*s.diff(s.trace(K2),t)
    assert s.expand(s.trace(K2)-theta)==0
    assert s.expand(R2-S2/t**2-time2)==0
    # exact scalar/vector Codazzi forcing for synchronous TT first-order geometry
    # and full symmetric mixed stress: q_i=T^0_i at second order,
    # T^i_0=-t^-2 q_i. Use independent Christoffel expansion at order two.
    rho,p=s.symbols('rho p'); dr=s.Function('dr')(t,x,y,z); dp=s.Function('dp')(t,x,y,z)
    q=s.Matrix([s.Function('q'+str(i))(t,x,y,z) for i in range(3)])
    P=H.diff(t) # a TT first-order stress test, independent of chosen curvature formula
    P2=s.zeros(3)
    T0=s.diag(-rho,p,p,p); T1=s.diag(0,P)
    T2=s.diag(-dr,dp*s.eye(3)+P2)
    for i in range(3): T2[0,i+1]=q[i]; T2[i+1,0]=-q[i]/t**2
    C0=s.MutableDenseNDimArray.zeros(4,4,4); C1=s.MutableDenseNDimArray.zeros(4,4,4); C2=s.MutableDenseNDimArray.zeros(4,4,4)
    for i,j in product(range(3),repeat=2):
        C0[0,i+1,j+1]=t*s.KroneckerDelta(i,j)
        C0[i+1,0,j+1]=C0[i+1,j+1,0]=s.KroneckerDelta(i,j)/t
        C1[0,i+1,j+1]=s.diff(t*t*H[i,j],t)/2
        C1[i+1,0,j+1]=C1[i+1,j+1,0]=H[i,j].diff(t)/2
        C2[i+1,0,j+1]=C2[i+1,j+1,0]=K2[i,j]
    for k,i,j in product(range(3),repeat=3):
        C1[k+1,i+1,j+1]=(s.diff(H[k,j],xyz[i])+s.diff(H[k,i],xyz[j])-s.diff(H[i,j],xyz[k]))/2
    # For C2*T0 only trace differences matter; omitted C2 terms multiply zero differences.
    def conn(C,T,nu):return sum(C[a,a,l]*T[l,nu]-C[l,a,nu]*T[a,l] for a,l in product(range(4),repeat=2))
    coords=(t,)+xyz
    def residual(nu):return sum(s.diff(T2[a,nu],coords[a]) for a in range(4))+conn(C0,T2,nu)+conn(C1,T1,nu)+conn(C2,T0,nu)
    energy=-dr.diff(t)-sum(q[i].diff(xyz[i]) for i in range(3))/t**2-3*(dr+dp)/t-(rho+p)*theta-s.trace(P*H.diff(t))/2
    assert s.expand(residual(0)-energy)==0
    for i in range(3):
        mom=q[i].diff(t)+3*q[i]/t+dp.diff(xyz[i])-s.trace(P*H.diff(xyz[i]))/2
        assert s.expand(residual(i+1)-mom)==0
    print(s.__version__,'9 exact checks PASS')

if __name__=='__main__':run()
