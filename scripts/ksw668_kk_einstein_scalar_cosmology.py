#!/usr/bin/env python3
"""D1/D2 nonvacuum 5D Einstein-scalar compact KK solution and SAME detector.

With kappa5=8*pi*G5=1 and Lambda=0, in cosmic time t>0:
  ds5^2=-dt^2 + t^(1/2)*(dx^2+dy^2+dz^2+dw^2)
  phi(t)=sqrt(3)/2*log(t), w identified mod 4 (spacelike S1 fibre).
G_AB=partial_A phi partial_B phi - (1/2)g_AB(grad phi)^2.
Checks all 125 Christoffel slots, 625 Riemann slots, 25 Einstein/stress
components, scalar Klein-Gordon equation and stress continuity.
Two actual null geodesics reach the SAME comoving detector x=3, w=0 mod 4:
one direct and one wrapped once around the compact extra dimension.
This is a genuine curved interacting Einstein-matter *mathematical* solution;
not an empirical or observer-Hilbert verification of KSW transport/FTL.
"""
import json
import sympy as s

def audit():
    t,x,y,z,w=s.symbols('t x y z w',positive=True,real=True)
    coords=(t,x,y,z,w)
    D=5
    a2=s.sqrt(t)
    g=s.diag(-1,a2,a2,a2,a2)
    inv=s.diag(-1,1/a2,1/a2,1/a2,1/a2)
    simplify=s.simplify
    Gamma={}
    for k in range(D):
        for i in range(D):
            for j in range(D):
                Gamma[k,i,j]=simplify(s.Rational(1,2)*sum(
                    inv[k,h]*(s.diff(g[h,j],coords[i])+s.diff(g[h,i],coords[j])-s.diff(g[i,j],coords[h]))
                    for h in range(D)))
    assert len(Gamma)==125
    assert sum(v!=0 for v in Gamma.values())==12
    R={}
    for k in range(D):
        for l in range(D):
            for i in range(D):
                for j in range(D):
                    R[k,l,i,j]=simplify(
                        s.diff(Gamma[k,j,l],coords[i])-s.diff(Gamma[k,i,l],coords[j])
                        +sum(Gamma[k,i,h]*Gamma[h,j,l]-Gamma[k,j,h]*Gamma[h,i,l] for h in range(D)))
    assert len(R)==625
    Ric=s.Matrix(D,D,lambda i,j:simplify(sum(R[h,i,h,j] for h in range(D))))
    scalar=simplify(s.trace(inv*Ric))
    Einstein=(Ric-g*scalar/2).applyfunc(simplify)
    phi=s.sqrt(3)*s.log(t)/2
    grad=s.Matrix([s.diff(phi,c) for c in coords])
    grad2=simplify((grad.T*inv*grad)[0])
    stress=(grad*grad.T-g*grad2/2).applyfunc(simplify)
    assert Einstein==stress and Einstein!=s.zeros(5)
    assert simplify(Einstein[0,0]-s.Rational(3,8)/t**2)==0
    for i in range(1,5):
        assert simplify(Einstein[i,i]-s.Rational(3,8)/t**s.Rational(3,2))==0
    H=s.Rational(1,4)/t
    assert simplify(-s.diff(phi,t,2)-4*H*s.diff(phi,t))==0
    assert simplify(s.diff(stress[0,0],t)+4*H*(stress[0,0]+stress[1,1]/a2))==0
    L=s.Integer(3)
    circumference=s.Integer(4)
    eta=lambda T:s.Rational(4,3)*(T**s.Rational(3,4)-1)
    arrive=lambda vx:(1+s.Rational(3,4)*L/vx)**s.Rational(4,3)
    rays=[]
    for vx,vw in ((s.Integer(1),s.Integer(0)),(s.Rational(3,5),s.Rational(4,5))):
        assert simplify(vx*vx+vw*vw-1)==0
        arrival=arrive(vx)
        X=lambda T:vx*eta(T)
        W=lambda T:vw*eta(T)
        assert simplify(X(arrival)-L)==0
        winding=simplify(W(arrival)/circumference)
        assert winding in (0,1)
        velocity=s.Matrix([1,s.diff(X(t),t),0,0,s.diff(W(t),t)])
        assert simplify((velocity.T*g*velocity)[0])==0
        acceleration=s.Matrix([
            simplify(s.diff(velocity[k],t)+sum(
                Gamma[k,i,j]*velocity[i]*velocity[j] for i in range(5) for j in range(5)))
            for k in range(5)])
        reparameter=simplify(acceleration[0])
        assert all(simplify(acceleration[k]-reparameter*velocity[k])==0 for k in range(5))
        assert simplify(reparameter-H)==0
        rays.append({"vx":str(vx),"vw":str(vw),"detector_x":3,
                     "w_mod_4":0,"fibre_winding":str(winding),
                     "same_detector_proper_t":str(arrival),
                     "arrival_numeric":float(arrival.evalf(14)),
                     "null_geodesic":True})
    assert rays[0]["arrival_numeric"]<rays[1]["arrival_numeric"]
    return {
        "status":"PASS exact symbolic 5D interacting Einstein–massless-scalar",
        "physical_model":"kappa5=1, Lambda=0, minimally coupled canonical scalar",
        "spacetime":"(0,infinity) x R^3 x S1 of w-coordinate period 4",
        "g5":"diag(-1,sqrt(t),sqrt(t),sqrt(t),sqrt(t))",
        "phi":"sqrt(3)/2 log(t)",
        "Gamma_slots":125,"Gamma_nonzero":12,
        "Riemann_slots":625,"Riemann_nonzero":sum(v!=0 for v in R.values()),
        "Ricci_diagonal":[str(v) for v in Ric.diagonal()],
        "scalar_curvature":str(scalar),
        "Einstein_equals_matter_all_25":True,
        "rho":"3/(8*t**2)","rho_positive":True,
        "scalar_wave_equation":"PASS",
        "stress_energy_conservation":"PASS",
        "same_observer_two_5D_null_geodesics":rays,
        "interacting_matter":True,"nonflat":True,
        "fibre_radius_time_dependent":True,
        "actual_external_instrument_observation":False,
        "proposed_KSW_transport_established":False,
        "superluminal_4D_signal":False,
    }

if __name__=="__main__":
    print(json.dumps(audit(),indent=2))
