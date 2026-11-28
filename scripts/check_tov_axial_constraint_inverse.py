"""Higher axial ADM momentum constraint and variational inverse.
Uses unit-normalized scalar spherical harmonics; l>=2. Kinetic sector only.
No polar inverse, spatial Hessian, or physical moving-interface theorem.
"""
import sympy as s


def main():
    r,N,f,a,L=s.symbols('r N f a L',positive=True)
    v,z,b,br,u=s.symbols('v z b br u',real=True)
    # h_rA=r² B S_A, h_AB=r² C S_AB; shift beta^A=b S^A.
    # K1_rA=r²(v-b') S_A/(2N), K1_AB=r²(z-2b) S_AB/(2N).
    # Norms int S_A S^A=L, int S_AB S^AB=L(L-2)/2.
    # Axial trace vanishes. Matter Y1=r u_angle S^A partial_A n.
    g=L*r**4*s.sqrt(f)/(32*s.pi*N)
    d=L*(L-2)*r*r/(128*s.pi*N*s.sqrt(f))
    k=L*r**4*a/(N*s.sqrt(f))
    density=N*r*r/s.sqrt(f)
    assert s.simplify(density/(16*s.pi)*(f*r*r*L*(v-br)**2/(2*N*N)+L*(L-2)*(z-2*b)**2/(8*N*N))-g*(v-br)**2-d*(z-2*b)**2)==0
    E=g*(v-br)**2+d*(z-2*b)**2+k*(u-b)**2
    assert s.expand(s.diff(E,b)/2-((4*d+k)*b-2*d*z-k*u))==0
    assert s.expand(s.diff(E,br)/2-g*(br-v))==0
    # l=1 normalized m=0 rotation S=-sin(theta)e_phi, scalar norm 4pi/3.
    assert s.simplify(g.subs(L,2)*4*s.pi/3-r**4*s.sqrt(f)/(12*N))==0
    assert d.subs(L,2)==0
    assert s.simplify(k.subs(L,2)*4*s.pi/3-8*s.pi*r**4*a/(3*N*s.sqrt(f)))==0
    # Exact angular normalization, independently from Legendre modes.
    x=s.symbols('x',real=True)
    for ell in range(1,9):
        Y=s.legendre(ell,x); lam=ell*(ell+1)
        norm=s.integrate(Y**2,(x,-1,1))
        assert s.integrate((1-x*x)*s.diff(Y,x)**2,(x,-1,1))==lam*norm
        assert s.integrate((1-x*x)**2*s.diff(Y,x,2)**2/2,(x,-1,1))==lam*(lam-2)*norm/2
    # Finite comparator: arbitrary velocity data, Schur projection is
    # orthogonal in the positive kinetic metric. Not continuum discretization.
    A=s.Matrix([[1,-1,0],[0,1,-1],[0,0,1],[2,0,0],[0,2,0],[0,0,2],[1,0,0],[0,1,0]])
    W=s.diag(2,3,5,7,11,13,17,19)
    H=A.T*W*A; P=A*H.inv()*A.T*W
    assert H.is_positive_definite and P*P==P and P.T*W==W*P
    y=s.Matrix([1,-2,3,4,-1,2,5,-3]); shift=H.inv()*A.T*W*y
    e=y-A*shift
    assert A.T*W*e==s.zeros(3,1)
    assert (y.T*W*y)[0]==(e.T*W*e)[0]+(shift.T*H*shift)[0]
    assert (e.T*W*e)[0]>0
    assert (s.eye(8)-P)*A==s.zeros(8,3)
    print('PASS exact higher axial ADM kinetic coefficients, dipole regression, 8 angular checks, weighted projection')
    print('OPEN polar inverse, spatial Hessian, moving junction and master symplectic normalization')


if __name__=='__main__':main()
