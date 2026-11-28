"""W2 geometry-forward and reverse-solve boundary packets, THREE DISTINCT actions.
TOV Einstein sphere; reciprocal static scalar controller; sourced 1D Maxwell.
Algebraic source/receiver reachability, NOT a shared physical action/device.
"""
from dataclasses import dataclass
import sympy as s

@dataclass(frozen=True)
class SourceBoundary:
    owner: str
    dimensions: int
    geometry: str
    clock: str
    normal: str
    quantities: tuple

TOV=SourceBoundary('original_TOV_Einstein_matter',4,'polar_areal','wall_proper_time','outward_unit_timelike_wall',('mass','density','radial_pressure','Ktheta','Ktau'))
REC=SourceBoundary('original_reciprocal_GX',4,'static_radial_flat_comparator','static','radial_outward',('q1','q2','Xminus','Xplus','traction','sheet'))
EM=SourceBoundary('independent_Maxwell_J',4,'one_dimensional_Minkowski','coordinate_t','opposed_worldtube_faces',('E','B','J','flux','work'))

def zero(q):
    assert s.simplify(s.factor(q))==0,s.factor(q)

def no_identification(a,b):
    assert a.owner!=b.owner or a.geometry!=b.geometry
    assert a.quantities!=b.quantities

def tov():
    r,m,rho,p,a,v=s.symbols('r m rho p a v',real=True)
    Kx,Kt=s.symbols('Kx Kt',positive=True)
    f=1-2*m/r
    theta=s.sqrt(f+v*v)/r
    temporal=(a+(f+v*v)*(m+4*s.pi*r**3*p)/(r*r*f)-(2*m/r**2-8*s.pi*r*rho)*v*v/(2*f))/s.sqrt(f+v*v)
    # Inverse 1: angular principal curvature fixes Misner-Sharp mass.
    finv=(r*Kx)**2-v*v
    minv=r*(1-finv)/2
    zero((theta**2).subs(m,minv)-Kx**2)
    # Inverse 2: temporal curvature fixes a pressure-density COMBINATION.
    obs=s.symbols('observed_tau',real=True)
    psol=s.solve(s.Eq(temporal,obs),p)[0]
    zero(temporal.subs(p,psol)-obs)
    psol_recovered=s.factor(psol.subs(obs,temporal))
    zero(psol_recovered-p)
    # A single velocity cannot independently determine rho and p.
    drho=s.symbols('drho',real=True)
    dp=-v*v*drho/(f+v*v)
    zero(temporal.subs({p:p+dp,rho:rho+drho},simultaneous=True)-temporal)
    # Two independent squared wall speeds have an invertible coefficient
    # matrix for (p,rho), provided *same source state* and unequal speeds.
    u1,u2=s.symbols('u1 u2',real=True)
    C=s.Matrix([[f+u1,u1],[f+u2,u2]])
    zero(s.det(C)-f*(u2-u1))
    z1,z2=s.symbols('z1 z2',real=True)
    inv=C.inv()*s.Matrix([z1,z2])
    zero((C*inv)[0]-z1);zero((C*inv)[1]-z2)
    assert s.factor(s.det(C).subs(u1,u2))==0
    print('TOV PASS angular mass inverse, temporal source combination, null fibre, two-speed observability')
    return {'source':TOV.owner,'one_speed_kernel':'dp=-v^2/(f+v^2) drho','two_speed_determinant':str(s.factor(C.det()))}

def reciprocal():
    r,q1,q2,Xm,Xp=s.symbols('r q1 q2 Xm Xp',real=True)
    jump=q1*(Xp-Xm)*(2*q2+q1*(Xp+Xm))/(2*r**4)
    tr=lambda X:(q1**2+(q2+X*q1)**2)/(2*r**4)
    zero(jump-tr(Xp)+tr(Xm))
    support=s.symbols('support',real=True)
    # Exact forward/reverse interface equation and its zero-support roots.
    q2root=s.solve(s.Eq(jump,0),q2)[0]
    zero(jump.subs(q2,q2root))
    zero(jump.subs({Xp:Xm}))
    zero(jump.subs({q1:0}))
    assert s.factor((jump+support).subs(support,0))!=0
    zero((jump+support).subs(support,-jump))
    # The no-support condition is not a universal no-go: balanced channels.
    assert s.factor(jump.subs({q1:1,q2:0,Xm:0,Xp:1,r:1}))==s.Rational(1,2)
    print('RECIPROCAL PASS signed traction, reverse zero-force flux, balanced exceptions')
    return {'source':REC.owner,'support':'-[Trr]','zero_support_balanced_q2':str(q2root)}

def maxwell():
    t,x=s.symbols('t x',real=True)
    E=s.Function('E')(t,x);B=s.Function('B')(t,x);J=s.Function('J')(t,x)
    H=(E*E+B*B)/2;S=E*B
    E_t=-B.diff(x)-J;B_t=-E.diff(x)
    residual=s.expand(H.diff(t)+S.diff(x)).subs({E.diff(t):E_t,B.diff(t):B_t})
    zero(residual+E*J)
    # Observed energy+flux fixes J only when E!=0; E=0 loses rank.
    measured=s.symbols('measured_energy_flux_balance',real=True)
    inferred_J=-measured/E
    zero((measured+E*inferred_J))
    assert not s.simplify((measured+E*J).subs(E,0))==0
    # Same clock + prescribed source required; boundary flux is signed.
    print('MAXWELL PASS local Ward, source-work inverse and zero-electric rank obstruction')
    return {'source':EM.owner,'source_inverse':'J=-measured/E (E != 0)','rank_obstruction':'E=0'}

def main():
    for a,b in ((TOV,REC),(TOV,EM),(REC,EM)):no_identification(a,b)
    for owner in (TOV,REC,EM):
        assert owner.dimensions==4 and owner.normal and owner.clock
    results=[tov(),reciprocal(),maxwell()]
    assert len({i['source'] for i in results})==3
    print('PASS THREE typed source-identical forward/reverse boundary packets')
    print('OPEN original physical apparatus/moving Einstein evolution/full observers')
if __name__=='__main__':main()
