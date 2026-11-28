"""Geometry-forward extension of existing KK/SC and same-action stress donors.
Exact symbolic conditional results, natural units; no microscopic source fit.
"""
import sympy as s

def check():
    phi,X,M,F2=s.symbols("phi X M F2",real=True)
    Z=s.exp(s.sqrt(6)*phi/M)
    A=s.exp(-phi/(s.sqrt(6)*M))
    beta=s.simplify(M*s.diff(s.log(A),phi))
    assert beta==-1/s.sqrt(6)
    assert 2*beta**2==s.Rational(1,3)
    # Same-action magnetic material vertex: F²=f(X), not an arbitrary
    # independently prescribed scalar source. This is a local fixed-field
    # ensemble; Maxwell/interface dynamics must be supplied separately.
    f=s.Function("f")(X)
    V=s.Function("V")(phi)+s.Function("U")(X)+Z*f/4
    lam=s.diff(V,phi,X)
    assert s.simplify(lam.subs(phi,0)-s.sqrt(6)*s.diff(f,X)/(4*M))==0
    assert s.simplify(s.diff(V,phi,2).subs(phi,0)-s.diff(s.Function("V")(phi),phi,2).subs(phi,0)-3*f/(2*M**2))==0
    assert s.simplify(lam.subs(f,0).doit())==0
    # Existing derivative vertex positive completion: background orientation
    # grad Zref supplies a preferred spatial direction. Distinct from mass mixing.
    K,H,l,k,x0=s.symbols("K H l k x0", positive=True)
    G=s.Matrix([[K,-l*x0],[-l*x0,H+l*l*x0*x0/K]])
    assert s.factor(G.det())==K*H
    # Integrating out a static material degree of freedom with stiffness B:
    a,b,g,J,S=s.symbols("a b g J S",positive=True)
    D=a*b-g*g
    q=s.Matrix([[a,g],[g,b]]).adjugate()*s.Matrix([S,J])/D
    E=(s.Matrix([S,J]).T*q)[0]/2
    assert s.factor(E-(b*S*S-2*g*S*J+a*J*J)/(2*D))==0
    # Fixed achievable scalar response p: minimum stored quadratic energy
    # over material displacement, not over unrestricted source geometry.
    p,u=s.symbols("p u",real=True)
    W=(a*p*p+2*g*p*u+b*u*u)/2
    assert s.factor(W.subs(u,-g*p/b)-D*p*p/(2*b))==0
    # Canonical unscreened attractive KK scalar fraction alpha=1/3.
    # For scalar-only attenuation T in [0,1], total normalized reduction
    # is at most 1/4 of the original Newton+scalar attraction.
    alpha,tau=s.symbols("alpha tau",nonnegative=True)
    shield=1-(1+alpha*tau)/(1+alpha)
    assert s.factor(shield-alpha*(1-tau)/(1+alpha))==0
    assert shield.subs({alpha:s.Rational(1,3),tau:0})==s.Rational(1,4)
    assert shield.subs(tau,1)==0
    # Finite screened slab matched to exterior homogeneous massive channel:
    # propagate [phi,phi'] across each interval, continuity of both.
    mu,d,z=s.symbols("mu d z",positive=True)
    P=s.Matrix([[s.cosh(mu*d),s.sinh(mu*d)/mu],
                [mu*s.sinh(mu*d),s.cosh(mu*d)]])
    assert s.trigsimp(P.det())==1
    assert (P.subs(d,0)-s.eye(2))==s.zeros(2)
    assert all(s.trigsimp(v)==0 for v in P*P.subs(d,-d)-s.eye(2))
    # Static isolated conserved source: Laue integral of spatial stress
    # vanishes, by integrating div(x_i T_ij) with vanishing boundary flux.
    # Explicit compact 1D stress potential illustrates boundary ledger.
    r=s.symbols("r",real=True)
    f0=(1-r*r)**3
    stress=s.diff(f0,r,2)
    assert s.integrate(stress,(r,-1,1))==0
    # Local negative active stress alone does not establish net repulsive
    # far monopole of an isolated stationary weak-field apparatus.
    print("PASS canonical KK coupling, same-action mixed vertex, positive completion, inverse energy, scalar shielding cap and boundary ledger")
    print("OPEN actual material F²(X), ensemble, curved 5D equations, tensor channel, conserved apparatus and SI calibration")

if __name__=="__main__":check()
