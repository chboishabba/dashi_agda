#!/usr/bin/env python3
"""D2 exact 5D Kaluza-Klein VACUUM Einstein solution and coordinate detector.

g5 = Minkowski(-+++) + (dw + (2/3)dt)^2.
The constant gauge A_t=2/3 is pure gauge; phi=1 and no interacting matter.
Ricci=G=0, T=0 and Lambda=0 constitute a genuine exact vacuum solution,
but NOT a dynamic Einstein-matter solution or observed transport mechanism.
Null rays arriving at x=L=4 have coordinate times 4 (zero fibre motion)
and 5 (nonzero fibre motion); standard KK produces no FTL shortcut.
"""
import sympy as s
import json

def audit():
    t,x,y,z,w=s.symbols('t x y z w',real=True)
    coords=(t,x,y,z,w)
    a=s.Rational(2,3)
    fibre=s.Matrix([a,0,0,0,1])
    g=s.diag(-1,1,1,1,0)+fibre*fibre.T
    inv=g.inv()
    assert g.det()==-1 and g*inv==s.eye(5)
    gamma={}
    for k in range(5):
      for i in range(5):
       for j in range(5):
        gamma[k,i,j]=s.simplify(s.Rational(1,2)*sum(
         inv[k,h]*(s.diff(g[h,j],coords[i])+s.diff(g[h,i],coords[j])
                   -s.diff(g[i,j],coords[h]))
         for h in range(5)))
    assert len(gamma)==125 and all(value==0 for value in gamma.values())
    R={}
    for k in range(5):
      for l in range(5):
       for i in range(5):
        for j in range(5):
         R[k,l,i,j]=s.simplify(
          s.diff(gamma[k,j,l],coords[i])-s.diff(gamma[k,i,l],coords[j])
          +sum(gamma[k,i,h]*gamma[h,j,l]
               -gamma[k,j,h]*gamma[h,i,l] for h in range(5)))
    assert len(R)==625 and all(x==0 for x in R.values())
    ricci=s.Matrix(5,5,lambda i,j:sum(R[h,i,h,j] for h in range(5)))
    assert ricci==s.zeros(5)
    scalar=s.trace(inv*ricci)
    G=ricci-s.Rational(1,2)*scalar*g
    assert G==s.zeros(5)
    direct=s.Matrix([1,1,0,0,-a])
    fibre_ray=s.Matrix([s.Rational(5,4),1,0,0,
                        s.Rational(3,4)-a*s.Rational(5,4)])
    for ray in (direct,fibre_ray):
        assert (ray.T*g*ray)[0]==0
    eta=s.diag(-1,1,1,1)
    assert (direct[:4,0].T*eta*direct[:4,0])[0]==0
    assert (fibre_ray[:4,0].T*eta*fibre_ray[:4,0])[0]==-s.Rational(9,16)
    L=4
    t0=L*direct[0]/direct[1]
    t1=L*fibre_ray[0]/fibre_ray[1]
    assert (t0,t1)==(4,5)
    return {
      "status":"PASS","same_metric":"full 5D constant Lorentzian KK vacuum",
      "original_metric_matrix":str(g),
      "full_Christoffel_count":125,"nonzero_Christoffel":0,
      "full_Riemann_count":625,"nonzero_Riemann":0,
      "Ricci_components":25,"nonzero_Ricci":0,
      "Einstein_tensor_components":25,"nonzero_Einstein":0,
      "field_equations":"G_AB=0, Lambda=0, T_AB=0 exact",
      "direct_null_ray_arrival_at_x4_t":str(t0),
      "fibre_moving_null_ray_arrival_at_x4_t":str(t1),
      "4D_projection_of_second_ray":"timelike interval squared -9/16",
      "real_detector_observation_acquired":False,
      "nontrivial_interacting_Einstein_matter":False,
      "physical_FTL_not_produced":True
    }
if __name__=="__main__":print(json.dumps(audit(),indent=2))
