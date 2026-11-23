"""F8 XCVI: original native normal_order=3 kinematic constraint at SAT faces.

Same-source literal algebra from ksw668_f8_tt_multipole.stage:
  Q = (P-M)/2 - D_y U
  G = ((1+v)P + (v-1)M)/2
  target = (2*amp*source-(1+v)P)/(v-1)
The common radial/warp force cancels from Q_T. No surrogate PDE, no CI.
This is a geometry/constructor diagnostic, not a measured finite-grid
run nor proof that the defect causes the far receiver amplitude.

Existing original owners: KSW668F8MovingWarpEnergyCancellationDefectExact;
KSW668F8YMNSNonlinearCurvatureRoadmap20261120 variational constructor
and weighted SBP4; original Israel background/TT source.
"""
import json
import sympy as s
def audit():
    v,dy,A,F=s.symbols("v dy A F",real=True,nonzero=True)
    P0,P1,M0,M1,PN,Pprev,MN,Mprev=s.symbols(
       "P0 P1 M0 M1 PN Pprev MN Mprev",real=True)
    a=1+v;c=1-v
    assert s.factor((v-1)+c)==0
    target=(2*A-a*P0)/(v-1)
    G=(a*P0+(v-1)*M0)/2
    dU0=(a*P0+c*M0)/2;dU1=(a*P1+c*M1)/2
    dP0=a*(P1-P0)/dy+F
    dM0=(v-1)*(M1-M0)/dy+F+2*c*(target-M0)/dy
    Qdot0=s.factor((dP0-dM0)/2-(dU1-dU0)/dy)
    assert s.simplify(Qdot0-2*(A-G)/dy)==0
    # SAT penalty is nonzero off-shell; do not equate target=M unless
    # incoming boundary Israel condition was actually paid.
    assert s.simplify(Qdot0.subs(M0,target))==0
    upperP=a*(PN-Pprev)/dy+F-2*a*PN/dy
    upperM=(v-1)*(MN-Mprev)/dy+F
    upperUN=(a*PN+c*MN)/2
    upperUp=(a*Pprev+c*Mprev)/2
    QdotN=s.factor((upperP-upperM)/2-(upperUN-upperUp)/dy)
    assert s.simplify(QdotN+a*PN/dy)==0
    # At interior, use common central difference D for ALL 3 fields:
    dP,dM=s.symbols("dP dM")
    qInterior=s.factor((a*dP-(v-1)*dM)/2 -
                (a*dP+c*dM)/2)
    assert qInterior==0
    # Explicit rational off-shell control: even with initially
    # compatible U/P/M, a forced weak SAT face creates Qdot.
    example=s.simplify(Qdot0.subs({
        v:-s.Rational(3,5),dy:s.Rational(1,10),A:1,
        P0:0,M0:0,P1:0,M1:0,F:0}))
    assert example==20
    # Exact original sourced-physical normal conversion:
    t=s.symbols("t",positive=True)
    ss=s.sqrt(1+t*t)
    vv=-1/ss
    b=1/t
    pulse=s.symbols("pulse",real=True)
    amp=-6*s.sqrt(1-vv*vv)/b*pulse
    # physical n dot dH = sqrt(1+t²)/t² * G,
    # and the stage's SAT enforces G=amp*source on-shell.
    normal_factor=ss/t**2
    assert s.simplify(normal_factor*amp+6*pulse)==0
    return {"status":"PASS exact SymPy original SAT kinematic constraint",
      "original_wall_Qdot":str(Qdot0),
      "original_upper_Qdot":str(QdotN),
      "interior_Qdot_zero":True,
      "sourced_boundary_negative_control":str(example),
      "physical_normalization":"(sqrt(1+t²)/t²)*amp = -6*pulse",
      "limitation":"Original weak SAT does not identically enforce P-M=2 D_y U at faces when Israel/upper SAT residual is nonzero; not measured source-to-far error, proof of continuum failure or completed geometry-first reference."}
if __name__=="__main__":
    print(json.dumps(audit(),indent=2))
