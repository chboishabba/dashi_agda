#!/usr/bin/env python3
"""Original Caldwell–Langlois (2001) 5D AdS Z2 thin-brane Israel junction.

DOI 10.1016/S0370-2693(01)00631-1, original Eqs(1),(4),(6).
ell=1, Lambda5=-6, kappa5²=6, sigma=1, 5D AdS
g5=diag(-R²,R^-2,R²,R²,R²) in T,R,x,y,z.
Moving flat FRW brane: R_b(t)=a(t)=t, dT_b/dt=sqrt(1+t²)/t².
h=diag(-1,t²,t²,t²), inward unit normal covector
n=(1,-dT_b/dt,0,0,0).
rho=sqrt(1+t^-2)-1, p=-rho-rho'/(3H), H=1/t.
Compute geometric full extrinsic K_ab, source stress S_ab and the
original Z2 Israel equation:
 K_ab= -kappa5²/2 * (S_ab - h_ab*S/3), S=h^ab S_ab.
All 16 component differences vanish as exact SymPy identities.
Positive rho, rho+p (NEC), and fixed cosmological sigma.
This closes the local classical Z2 junction *equation* for this
source model, NOT gravitational perturbation spectra, localization,
source/detector coupling, quantum/string UV or measured transport.
"""
import sympy as s
import json

def audit():
    t=s.symbols("t",positive=True,real=True)
    R,T=s.symbols("R T",positive=True,real=True)
    coords=(T,R,s.symbols("x"),s.symbols("y"),s.symbols("z"))
    g=s.diag(-R**2,R**-2,R**2,R**2,R**2)
    inv=s.diag(-R**-2,R**2,R**-2,R**-2,R**-2)
    Gamma={}
    for k in range(5):
        for i in range(5):
            for j in range(5):
                Gamma[k,i,j]=s.simplify(s.Rational(1,2)*sum(
                  inv[k,h]*(s.diff(g[h,j],coords[i])+s.diff(g[h,i],coords[j])-s.diff(g[i,j],coords[h]))
                  for h in range(5)))
    Tp=s.sqrt(t*t+1)/t**2
    u=s.Matrix([Tp,1,0,0,0])
    n=s.Matrix([1,-Tp,0,0,0])
    assert s.simplify((n.T*inv.subs(R,t)*n)[0])==1
    assert s.simplify((n.T*u)[0])==0
    assert s.simplify((u.T*g.subs(R,t)*u)[0])==-1
    h=s.diag(-1,t*t,t*t,t*t)
    hinv=s.diag(-1,t**-2,t**-2,t**-2)
    acceleration=s.Matrix([
      s.diff(u[k],t)+sum(Gamma[k,i,j].subs(R,t)*u[i]*u[j] for i in range(5) for j in range(5))
      for k in range(5)]).applyfunc(s.simplify)
    K=s.zeros(4)
    K[0,0]=s.simplify(-(n.T*acceleration)[0])
    for i in range(1,4):
        for j in range(1,4):
            K[i,j]=s.simplify(
              -sum(n[k]*Gamma[k,i+1,j+1].subs(R,t) for k in range(5)))
    A=s.sqrt(1+t**-2)
    mixed=(hinv*K).applyfunc(s.simplify)
    assert s.simplify(mixed[0,0]+1/A)==0
    assert all(s.simplify(mixed[i,i]+A)==0 for i in range(1,4))
    rho=s.sqrt(1+t**-2)-1
    H=1/t
    pressure=s.simplify(-rho-s.diff(rho,t)/(3*H))
    sigma=s.Integer(1)
    kappa5sq=s.Integer(6)
    S=s.diag(rho+sigma,(pressure-sigma)*t*t,
             (pressure-sigma)*t*t,(pressure-sigma)*t*t)
    trace=s.simplify(sum(hinv[i,i]*S[i,i] for i in range(4)))
    israel=(-s.Rational(1,2)*kappa5sq*(S-trace*h/3)).applyfunc(s.simplify)
    assert all(s.simplify(K[i,j]-israel[i,j])==0 for i in range(4) for j in range(4))
    assert s.simplify(rho+pressure-1/(3*t*t*A))==0
    return {
      "status":"PASS original 5D AdS Z2 thin-brane Israel source all 16 equalities",
      "original_paper_DOI":"10.1016/S0370-2693(01)00631-1",
      "original_metric":"5D AdS k=mu=0 ell=1, Lambda=-6",
      "induced_h":"diag(-1,t²,t²,t²)",
      "inward_unit_normal_cov":"(1,-sqrt(1+t²)/t²,0,0,0)",
      "geometric_K_mixed_t":"-1/sqrt(1+t^-2)",
      "geometric_K_mixed_i":"-sqrt(1+t^-2)",
      "S_source":"S_ab=-sigma*h_ab + T_matter_ab, sigma=1",
      "original_kappa5_squared":6,
      "unit_normal_and_induced_clock":True,
      "classical_Z2_Israel_all_16":True,
      "rho_positive":True,"rho_plus_p_positive":True,
      "bulk_linearised_graviton_and_stability_proved":False,
      "physical_bulk_source_detector_response":False,
      "same_receiver_measurement_or_GW170817_constraint":False
    }

if __name__=="__main__":
    print(json.dumps(audit(),sort_keys=True,indent=2))
