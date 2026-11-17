"""Exact outgoing-radiation sheet-source Green for a restricted Maxwell slab.
Reuse SmithFilsinger tangential 4x4 Maxwell transfer. No calibrated
soil/air/ionosphere data, original source or hyperbolic dyadic proof.
Four tangential phasors [Ex,Ey,Hx,Hy], exp(-iwt+ikx), ky=0.
Exterior media must be lossless homogeneous and qz real positive.
Cayley propagation is an exact rational finite scheme, NOT exp(Md).
"""
import sympy as S
from smith_filsinger_tangential_maxwell_sympy import (
    tangential_generator,three_layer_tangential_transfer)
R=S.Matrix([[0,-1],[1,0]])
F=S.zeros(4)
F[0,3]=F[3,0]=S.Rational(1,2)
F[1,2]=F[2,1]=-S.Rational(1,2)

def outgoing_admittance(omega,kx,mu,epsilon):
    w,k,m,e=map(S.sympify,(omega,kx,mu,epsilon))
    if any(a.is_positive is not True for a in (w,m,e)):
        raise ValueError("positive frequency and exterior material required")
    q2=S.simplify(w*w*m*e-k*k)
    if q2.is_positive is not True:
        raise ValueError("evanescent/branch-point requires independent radiation certificate")
    q=S.sqrt(q2)
    return S.Matrix([[0,-q/(w*m)],[w*e/q,0]])

def outgoing_sheet_green(T,omega,kx,mu_bottom=1,eps_bottom=1,
                         mu_top=1,eps_top=1):
    """Exact finite-scheme map top tangential sheet current to exterior E.
    Bottom outgoing H=-Yb E, top outgoing H=Yt E, field E continuous.
    Jump R*(H_inside-H_outside)=J_sheet; R rotates x/y by +90deg.
    """
    Yb=outgoing_admittance(omega,kx,mu_bottom,eps_bottom)
    Yt=outgoing_admittance(omega,kx,mu_top,eps_top)
    A,B,C,D=T[:2,:2],T[:2,2:],T[2:,:2],T[2:,2:]
    Emap=A-B*Yb
    Hmap=C-D*Yb
    boundary=S.simplify(R*(Hmap-Yt*Emap))
    if boundary.det()==0:
        raise ValueError("singular source/radiation boundary")
    Eb=S.simplify(boundary.inv())
    Et=S.simplify(Emap*Eb)
    return dict(upper_E=Et,lower_E=Eb,upper_H=S.simplify(Yt*Et),
                lower_H=S.simplify(-Yb*Eb),inside_H=S.simplify(Hmap*Eb),
                boundary_matrix=boundary,upper_Y=Yt,lower_Y=Yb)

def flux_z(E,H):
    return S.simplify((E.conjugate().T*(-R)*H)[0]/2)

def sheet_power_identity(response,J):
    """P_sheet = P_exterior + P_absorption, no source twice."""
    Et,Eb=response["upper_E"]*J,response["lower_E"]*J
    Hu,Hb=response["upper_H"]*J,response["lower_H"]*J
    Hi=response["inside_H"]*J
    source=S.simplify(S.re((Et.conjugate().T*J)[0])/2)
    outward=S.simplify(S.re(flux_z(Et,Hu)-flux_z(Eb,Hb)))
    absorb=S.simplify(S.re(flux_z(Eb,Hb)-flux_z(Et,Hi)))
    return dict(source=source,exterior=outward,absorption=absorb,
                residual=S.simplify(source-outward-absorb))

def fixtures(kx=S.Rational(0),hall=S.Rational(0)):
    w=S.Rational(2)
    layers=[(S.Rational(1),S.Rational(1),S.Rational(1)),
            (S.Rational(1),S.Rational(3,2),S.Rational(3,2)),
            (S.Rational(1),S.Rational(2),S.Rational(2))]
    gens=[tangential_generator(w,kx,mu,ex,ey,ex,S.I*hall,-S.I*hall)
          for mu,ex,ey in layers]
    return gens,[S.Rational(1,7),S.Rational(1,9),S.Rational(1,11)]
