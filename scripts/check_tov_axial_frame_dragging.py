"""Axial l=1 Einstein-material quadratic action and shift Schur complement.

Convention: ADM beta^phi=beta, Y=r U(alpha)n, asymptotic shift zero.
Uses original repaired TOV background. No l>=2 or polar stability claim.
"""
import sympy as s

def main():
    r,N,f,a,c=s.symbols('r N f a c',positive=True)
    th=s.symbols('theta',real=True)
    br,bt,ar,at=s.symbols('beta_r beta alpha_r alpha_t',real=True)
    # Independent ADM spatial connection: h=diag(1/f,r²,r²sin²theta).
    h=s.diag(1/f,r*r,r*r*s.sin(th)**2)
    # Lie_beta h has only r-phi and phi-r entries for beta(r,t).
    Lie=s.zeros(3); Lie[0,2]=Lie[2,0]=h[2,2]*br
    K=Lie/(2*N); mixed=h.inv()*K
    assert s.trace(mixed)==0
    assert s.simplify(s.trace(mixed*mixed)-f*r*r*s.sin(th)**2*br**2/(2*N*N))==0
    volume=N*r*r*s.sin(th)/s.sqrt(f)
    integrate=lambda e:s.simplify(2*s.pi*s.integrate(e,(th,0,s.pi)))
    grav=integrate(volume*s.trace(mixed*mixed)/(16*s.pi))
    matter=integrate(volume*r*r*s.sin(th)**2*(a*(at-bt)**2/N**2-(a-c)*f*ar**2))
    g=r**4*s.sqrt(f)/(12*N); k=8*s.pi*r**4*a/(3*N*s.sqrt(f)); q=8*s.pi*r**4*N*s.sqrt(f)*(a-c)/3
    assert s.simplify(grav-g*br**2)==0
    assert s.simplify(matter-k*(at-bt)**2+q*ar**2)==0
    # Exterior Schwarzschild N=sqrt(f), beta=C/r³, decays at infinity.
    R=s.symbols('R',positive=True); b=s.symbols('b',real=True)
    ext=b*(R/r)**3; ge=r**4/12
    assert s.simplify(s.diff(ge*s.diff(ext,r),r))==0
    assert s.integrate(ge*s.diff(ext,r)**2,(r,R,s.oo))==R**3*b*b/4
    assert s.simplify((ge*s.diff(ext,r)).subs(r,R)+R**3*b/4)==0
    # Finite exact Schur diagnostic: derivative + exterior Robin energy
    # SPD, no artificial rigid shift kernel. Matrix is a comparator,
    # not the actual continuum radial discretization.
    D=s.Matrix([[-1,1,0],[0,-1,1]])
    G=D.T*s.diag(2,3)*D+s.diag(0,0,s.Rational(1,4))
    K=s.diag(1,2,3)
    S=K-K*(G+K).inv()*K
    assert G.is_positive_definite and S.is_positive_definite
    assert (K-S).is_positive_definite
    assert s.simplify(S-(K.inv()+G.inv()).inv())==s.zeros(3)
    z=s.Matrix([1,-2,3]); b0=(G+K).inv()*K*z
    assert s.simplify((z.T*S*z)[0]-((z-b0).T*K*(z-b0)+b0.T*G*b0)[0])==0
    print('PASS ADM axial shift coefficient, exterior Robin and finite Schur identities')
    print('OPEN continuum uniform Schur bound, physical domain, polar and higher axial modes')

if __name__=='__main__':main()
