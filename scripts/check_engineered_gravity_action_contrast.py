"""Action-derived kinetic contrast and weak metric source constraints.
Conditional EFT checks, not a physical shield or original F8 evolution.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def contrast():
    K,H,l,X=s.symbols('K H l X',positive=True)
    G=s.Matrix([[K,-l*X],[-l*X,H+l*l*X*X/K]])
    Ke=s.factor(G[0,0]-G[0,1]**2/G[1,1])
    eq(Ke/K,K*H/(K*H+l*l*X*X))
    z=s.symbols('z',positive=True)
    eq((Ke/K).subs(l*l*X*X,K*H*(1/z-1)),z)
    p=s.symbols('p',real=True)
    q=l*X*p/G[1,1]
    v=s.Matrix([p,q])
    eq((v.T*G*v)[0],Ke*p*p)
    # Free reference flux zero versus clamped reference gradient zero.
    eq(G[1,0]*p+G[1,1]*q)
    eq(G[0,0],K)
    # Nonminimal curvature action, Einstein-frame kinetic and coupling.
    F0,xi,O,M,k=s.symbols('F0 xi O M k',positive=True)
    F=F0+2*xi*O*O
    f=s.diff(F,O)
    D=M*M*(k/F+3*f*f/(2*F*F))
    beta=-M*f/(2*F*s.sqrt(D))
    eq(beta**2,f*f/(4*k*F+6*f*f))
    eq(1-6*beta**2,4*k*F/(4*k*F+6*f*f))
    eq(D.subs(O,0),M*M*k/F0)
    eq(beta.subs(O,0))

def spherical():
    # Exact two-field massless divergence-form spherical shell, same
    # exterior/interior kinetic identity after constant normalization.
    # Constant orthogonal diagonalization makes two independent l=1 modes.
    a,b,z1,z2=s.symbols('a b z1 z2',positive=True)
    tau=lambda z:9*z/(9*z+2*(z-1)**2*(1-(a/b)**3))
    U=s.Matrix([[3,-4],[4,3]])/5
    P=U*s.diag(tau(z1),tau(z2))*U.T
    eq(P[1,0],s.Rational(12,25)*(tau(z1)-tau(z2)))
    assert (P.subs(z2,z1)-s.eye(2)*tau(z1)).applyfunc(s.simplify)==s.zeros(2)
    assert P.subs({z1:1,z2:1})==s.eye(2)
    # Reciprocal eigencontrasts give no conversion although both attenuate.
    eq(P[1,0].subs(z2,1/z1))
    # With same universal matter coupling, scalar suppression alone
    # leaves tensor contribution unchanged in this weak-field comparator.
    alpha,T=s.symbols('alpha T',nonnegative=True)
    eq(1-(1+alpha*T)/(1+alpha),alpha*(1-T)/(1+alpha))

def metric():
    # Linear static metric around flat constant F0, compact delta F.
    # 2F0 Lap Psi = rho + Lap deltaF; F0(Psi-Phi)=deltaF
    # when independent anisotropic stress vanishes.
    r,R,F0,A=s.symbols('r R F0 A',positive=True)
    f=A*(1-r*r/R**2)**4
    lap=lambda v:s.diff(v,r,2)+2*s.diff(v,r)/r
    Psi=f/(2*F0); Phi=-f/(2*F0)
    eq(2*F0*lap(Psi),lap(f));eq(F0*(Psi-Phi),f)
    eq(Phi+Psi)
    for v in (f,s.diff(f,r),s.diff(f,r,2)):
        eq(v.subs(r,R))
    eq(s.integrate(r*r*lap(f),(r,0,R)))
    # This compact conformal correction is NOT a full sourced solution:
    # scalar EOM and material/controller stress must still be supplied.

def main():
    for fn in (contrast,spherical,metric):
        fn(); print('PASS',fn.__name__,flush=True)
    print('OPEN physical material, complete metric and original F8 history')

if __name__=='__main__':main()
