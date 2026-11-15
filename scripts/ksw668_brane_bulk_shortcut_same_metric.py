#!/usr/bin/env python3
"""KSW/KK max cut: same-metric 5D bulk versus curved test-brane null arrival.

Actual ambient metric throughout: ds5²=-dt²+dX²+dY²+du²+dv².
Cylindrical test brane: X=R*cos(theta), Y=R*sin(theta), R>0.
Induced metric: ds4²=-dt²+R²*dtheta²+du²+dv².
Antipodal brane source/receiver: brane photon time=pi*R,
5D null-chord bulk time=2*R. Earlier BULK arrival is causal in 5D
and spacelike on the brane; no 5D-superluminal propagation.
One must have a propagating bulk field and source/detector coupling:
those are not provided by the geometric example.

Critical dynamical limitation: this cylindrical brane has extrinsic
mean curvature -1/R. Free isolated Nambu-Goto tension does NOT support
it as stationary. Israel junction conditions, 5D gravitating matter,
brane backreaction and experimental reception are OPEN.

Negative control: a static warped metric
ds²=a(y)²(-dt²+dx²+du²+dv²)+dy², a(y)>0, has dt>=|dx|,
so mere static warping of BOTH time and space does not create a shortcut.
This is a new kinematic illustration, NOT the original AdS/Friedmann
result of Caldwell & Langlois (2001), DOI 10.1016/S0370-2693(01)00631-1.
"""
import argparse
import json
import sympy as s
import mpmath as mp

def audit():
    t,th,u,v,R=s.symbols("t theta u v R",real=True,positive=True)
    coords=(t,th,u,v)
    g5=s.diag(-1,1,1,1,1)
    i=s.Matrix([t,R*s.cos(th),R*s.sin(th),u,v])
    J=i.jacobian(coords)
    g4=(J.T*g5*J).applyfunc(s.simplify)
    assert g4==s.diag(-1,R*R,1,1)
    n=s.Matrix([0,s.cos(th),s.sin(th),0,0])
    assert s.simplify((n.T*g5*n)[0])==1
    Kth=s.simplify((n.T*g5*s.diff(i,th,2))[0])
    Ktrace=s.simplify(Kth/(R*R))
    assert Kth==-R and Ktrace==-1/R
    tau=s.symbols("tau",real=True)
    chord=s.Matrix([tau,R-tau,0,0,0])
    vel=s.diff(chord,tau)
    assert s.simplify((vel.T*g5*vel)[0])==0
    assert s.diff(chord,tau,2)==s.zeros(5,1)
    assert chord.subs(tau,0)==i.subs({t:0,th:0,u:0,v:0})
    assert chord.subs(tau,2*R)==i.subs({t:2*R,th:s.pi,u:0,v:0})
    arc=i.subs({t:tau,th:tau/R,u:0,v:0})
    v_arc=s.diff(arc,tau)
    assert s.trigsimp((v_arc.T*g5*v_arc)[0])==0
    v4=s.Matrix([1,1/R,0,0])
    assert s.simplify((v4.T*g4*v4)[0])==0
    assert arc.subs(tau,0)==i.subs({t:0,th:0,u:0,v:0})
    assert arc.subs(tau,s.pi*R)==i.subs({t:s.pi*R,th:s.pi,u:0,v:0})
    acc=s.diff(arc,tau,2)
    assert s.simplify(acc[1].subs(tau,0))==-1/R
    assert float(s.N(s.pi**2-4))>0
    assert s.simplify(-4*R**2+s.pi**2*R**2)==R**2*(s.pi**2-4)
    assert s.simplify((s.pi*R)/(2*R))==s.pi/2
    # Rational polygonal same-ambient-metric negative control:
    # brane constrained to (0,0)->(3,4)->(6,0), legs 5+5,
    # direct 5D chord 6. This has a non-smooth corner.
    assert 3**2+4**2==5**2 and 10==6+4
    # A static RS-type metric conformally multiplies BOTH t and x:
    # ds5²=a(y)²(-dt²+dx²+...)+dy²<=0 implies
    # dt²>=dx²+dy²/a(y)² => duration >= |delta x|.
    k=mp.mpf("0.7");L=mp.mpf("3");A=mp.mpf("0.4")
    def dt_ds(z):
        y=A*mp.sin(mp.pi*z)
        yp=A*mp.pi*mp.cos(mp.pi*z)
        return mp.sqrt(L**2+mp.exp(2*k*abs(y))*yp**2)
    detour=mp.quad(dt_ds,[0,mp.mpf(".5"),1])
    assert detour>L
    return {
      "status":"PASS geometric same-metric kinematic counterexample, NOT dynamical brane/real observation",
      "ambient":"5D Minkowski (-++++): t,X,Y,u,v",
      "embedding":"t,R cos(theta),R sin(theta),u,v",
      "induced_4D_metric":"diag(-1,R^2,1,1)",
      "5D_bulk_null_straight_geodesic":True,
      "4D_brane_confined_intrinsically_null_curve":True,
      "bulk_arrival_time_in_units_R":2,
      "brane_light_arrival_time_in_units_R":float(s.N(s.pi,30)),
      "bulk_earlier_by_units_R":float(s.N(s.pi-2,30)),
      "apparent_speed_ratio":str(s.pi/2),
      "induced_interval_squared_at_early_arrival_units_R2":float(s.N(s.pi**2-4,30)),
      "brane_spacelike_at_bulk_arrival":True,
      "5D_global_causality_not_violated":True,
      "cylindrical_extrinsic_trace":str(Ktrace),
      "tension_only_brane_stationary":False,
      "5D_Einstein_with_brane_backreaction_solved":False,
      "bulk_excitation_source_detector_coupling":False,
      "independent_gravitational_signal_measured":False,
      "static_warp_same_time_space_bulk_shortcut":False,
      "static_warp_detour_time":float(detour),
      "static_warp_onbrane_time":float(L),
      "rational_polygon_source_3_4_5":{"intrinsic_length":10,"bulk_chord":6,"saving":4,"smooth":False},
      "original_research_DOI":"10.1016/S0370-2693(01)00631-1",
      "paper_reproduction":False,
      "physical_FTL_or_closed_timelike_curve":False,
    }

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out")
    a=p.parse_args()
    report=json.dumps(audit(),indent=2,sort_keys=True)+"\n"
    if a.out:open(a.out,"w",encoding="utf-8").write(report)
    print(report)
