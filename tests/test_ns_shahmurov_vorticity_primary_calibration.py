"""Primary-paper integration: exact smooth-field vorticity threshold donor.

Original theorem: Rishad Shahmurov, arXiv:2605.01873v3,
Lemma 2.1 and Theorem 2.2. This checks ONLY a concrete smooth
nonvanishing-vorticity calibration of Lemma 2.1 and elementary Z algebra.
Not a proof of Theorem 2.2 or Navier--Stokes B.
"""
import sympy as s

def test_vorticity_magnitude_identity_on_exact_heat_shear():
    x,y,z,t=s.symbols("x y z t",real=True)
    # One spatial-mode smooth shear u=(0,0,2 exp(-t)cos(x)).
    u=s.Matrix([0,0,2*s.exp(-t)*s.cos(x)])
    omega=s.Matrix([s.diff(u[2],y)-s.diff(u[1],z),
                    s.diff(u[0],z)-s.diff(u[2],x),
                    s.diff(u[1],x)-s.diff(u[0],y)])
    assert omega==s.Matrix([0,2*s.exp(-t)*s.sin(x),0])
    # Work in 0<x<pi where f>0 and direction is constant.
    f=2*s.exp(-t)*s.sin(x)
    direction=s.Matrix([0,1,0])
    S=(u.jacobian([x,y,z])+u.jacobian([x,y,z]).T)/2
    alpha=s.simplify((direction.T*S*direction)[0])
    assert alpha==0
    transport=sum(u[j]*s.diff(f,v) for j,v in enumerate((x,y,z)))
    laplace=sum(s.diff(f,v,2) for v in (x,y,z))
    lhs=s.simplify(s.diff(f,t)+transport-laplace)
    rhs=s.simplify(alpha*f-f*sum(s.diff(direction[j],v)**2
                    for j in range(3) for v in (x,y,z)))
    assert lhs==rhs==0

def test_critical_root_exponent_exact():
    # |Z|²=|omega|^(3/2) for Z=|omega|^(-1/4)*omega
    # at all nonzero omega. This is the algebraic normal form, not
    # a general differential estimate.
    r=s.symbols("r",positive=True)
    assert s.simplify((r**s.Rational(-1,4)*r)**2 -
                      r**s.Rational(3,2))==0
