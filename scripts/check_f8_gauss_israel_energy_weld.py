"""F8 Gauss/Israel compatibility and ADM energy donor crosswalk.
Exact algebraic welds; no continuum IBVP or uniform trace claim.
"""
import sympy as s

def exact():
    t,k=s.symbols('t k',positive=True); b=1/t; B=s.sqrt(1+b*b)
    f,l,J,Y=[s.Function(a)(t) for a in ('f','l','J','Y')]
    p,rho,Q,A,Rtt=s.symbols('p rho Q A Rtt')
    L=l+2*f/B; Jind=J-6*B*f; Yind=Y-2*B*f
    R=s.expand(Jind.diff(t,2)+4*b*Jind.diff(t)+3*b*L.diff(t)+6*b*b*L-k*k*b*b*(L-2*Yind))
    Rstar=s.expand(R+6*B*f.diff(t,2))
    assert not Rstar.has(f.diff(t,2))
    gauss=R+Rtt-6*rho/B+18*B*p-Q
    temporal=f.diff(t,2)-3*p-A
    compatibility=Rstar+Rtt-6*B*A-6*rho/B-Q
    assert s.simplify(gauss+6*B*temporal-compatibility)==0
    assert not compatibility.has(p,f.diff(t,2))
    # Both directions: any two residual equations imply the third.
    assert s.simplify(gauss.subs(f.diff(t,2),3*p+A)-compatibility)==0
    # Exact first-order traceless Israel defect correction.
    P=s.Matrix([[1,2,0],[2,-1,3],[0,3,0]])
    e=s.Matrix([[0,1,2],[1,2,0],[2,0,-2]])
    a,c=s.symbols('a c'); U=-3*a*P+c*e
    assert s.expand(-s.trace(U*U)+9*a*a*s.trace(P*P)-6*a*c*s.trace(P*e)+c*c*s.trace(e*e))==0
    # F8 Poincare slice/wall tilt; BR73/76/77 donor specialized.
    eta=s.diag(-1,1,1,1,1); tau=s.Matrix([1,0,0,0,0]); n=s.Matrix([-b,0,0,0,B]); u=s.Matrix(s.symbols('u0:5',real=True))
    assert s.simplify((n.T*eta*n)[0]-1)==0
    norm=(u.T*eta*u)[0]; energy=sum(v*v for v in u)/2
    flux=(tau.T*(u*u.T-eta*norm/2)*n)[0]
    assert s.simplify(flux+b*energy-B*u[0]*u[4])==0
    assert s.expand(B*energy-B*u[0]*u[4]-B*((u[0]-u[4])**2+sum(v*v for v in u[1:4]))/2)==0
    assert s.expand(B*energy+B*u[0]*u[4]-B*((u[0]+u[4])**2+sum(v*v for v in u[1:4]))/2)==0
    # Wall-orthogonal GN observer has exactly zero tilt.
    tauw=s.Matrix([B,0,0,0,-b]); assert s.simplify((tauw.T*eta*n)[0])==0
    assert s.simplify((tauw.T*eta*tauw)[0]+1)==0
    # BR44 weighted majorant, symbolic coefficientwise certificate.
    E,D,a,c,d,h,lam=s.symbols('E D a c d h lam',nonnegative=True); m=s.symbols('m',positive=True)
    assert s.expand(m*(E+lam*D)-((a+lam*c)*E+(h+lam*d)*D)-(m-a-lam*c)*E-(lam*m-h-lam*d)*D)==0
    print('12 exact assertions PASS; Gauss-Israel bidi, off-shell trace, F8 ADM tilt, two-level energy')
if __name__=='__main__': exact()
