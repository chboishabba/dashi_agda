"""Fixed-radius axial RW gauge canonical symplectic current, vacuum.
Unit scalar harmonic norm, common increasing-r normal; canonical momentum
chosen +sqrt(-gamma)(K^ab-K gamma^ab)/(16pi). Overall orientation explicit.
No moving corners, polar normalization or interior physical trace claim.
"""
import sympy as s


def main():
    r,F,Fp,S,L,n=s.symbols('r F Fp S L n',positive=True)
    b1,b2,c1,c2,p1,p2,q1,q2=s.symbols('b1 b2 c1 c2 p1 p2 q1 q2',real=True)
    # Angular point: S is the covariant phi component; sin(theta)=sigma.
    sig=s.symbols('sigma',positive=True)
    gamma=s.diag(-F,r*r,r*r*sig**2); A=gamma.inv()
    K=s.sqrt(F)*s.diag(-Fp,2*r,2*r*sig**2)/2
    def jets(b,c):
        # c=partial_r b_t-partial_t b_r; other delta K components
        # do not pair with the RW induced metric perturbation.
        H=s.zeros(3); H[0,2]=H[2,0]=r*r*b*S
        J=s.zeros(3); J[0,2]=J[2,0]=s.sqrt(F)*S*(2*r*b+r*r*c)/2
        return H,J
    def momentum(H,J):
        dA=-A*H*A; tr=s.trace(A*K); dt=s.trace(dA*K+A*J)
        return s.sqrt(F)*r*r*sig*(s.trace(A*H)/2*(A*K*A-tr*A)+dA*K*A+A*J*A+A*K*dA-dt*A-tr*dA)/(16*s.pi)
    H1,J1=jets(b1,c1);H2,J2=jets(b2,c2)
    omega=s.factor(s.trace(momentum(H1,J1)*H2-momentum(H2,J2)*H1))
    assert s.simplify(omega+r**4*S**2*(c1*b2-c2*b1)/(16*s.pi*sig))==0
    # CPM psi=-r³ c/n; b_t=-(Q+F psi/r)/(2r).
    val=s.factor(omega.subs({c1:-n*p1/r**3,c2:-n*p2/r**3,b1:-(q1+F*p1/r)/(2*r),b2:-(q2+F*p2/r)/(2*r)}))
    # Integral S²/sigma dtheta dphi = L for axial m=0, unit norm.
    integrated=s.cancel(val*sig*L/S**2)
    assert s.expand(integrated+n*L*(p1*q2-p2*q1)/(32*s.pi))==0
    assert s.factor((n*L/(32*s.pi)).subs(n,(L-2)/2)-L*(L-2)/(64*s.pi))==0
    # With delta2=partial_t delta1, symplectic current differs from
    # the energy flux by an exact time derivative, not a pointwise equality.
    t=s.symbols('t'); p=s.Function('p')(t); q=s.Function('q')(t)
    assert s.expand(-(p*q.diff(t)-p.diff(t)*q)-(2*p.diff(t)*q-(p*q).diff(t)))==0
    print('PASS axial canonical momentum bilinear, CPM normalization and total time derivative')
    print('OPEN polar flux, moving embedding/corners, interior trace and full spatial energy')


if __name__=='__main__':main()
