#!/usr/bin/env python3
"""OCT369 P0.19: cubic T1g axial-octupole / hypothetical curvature selection rules.
Established prior: O_h representation and scalar-tensor EFT. The external B
term is ONLY a symmetry candidate; a real covariant magnetic field requires
an observer and Maxwell tensor. No PtMn3 gravity effect is claimed.
"""
import json
from itertools import permutations,product
import sympy as s
x,y,z,bx,by,bz,xi,eta,M2,q=s.symbols('O_x O_y O_z B_x B_y B_z xi eta M2 q',real=True)
O=s.Matrix([x,y,z]); B=s.Matrix([bx,by,bz]); I=s.eye(3)
rot=[]
for perm in permutations(range(3)):
 for signs in product((-1,1),repeat=3):
  R=s.zeros(3)
  for i in range(3):R[i,perm[i]]=signs[i]
  rot.append(R)
axial=[R.det()*R for R in rot]
O2=s.expand(O.dot(O)); O4=sum(u**4 for u in O); OB=s.expand(O.dot(B))
checks={}
def ok(label,value):
 assert bool(value),label
 checks[label]=True
ok('48_cubic_operations',len(rot)==48)
ok('24_proper_operations',sum(R.det()==1 for R in rot)==24)
ok('24_improper_operations',sum(R.det()==-1 for R in rot)==24)
ok('axial_inversion_even',(-I).det()*(-I)*O==O)
ok('quadratic_O2_invariant',all(s.expand((A*O).dot(A*O)-O2)==0 for A in axial))
ok('quartic_anisotropy_invariant',all(s.expand(sum(u**4 for u in A*O)-O4)==0 for A in axial))
ok('linear_order_not_scalar',any(A*O!=O for A in axial))
ok('no_nonzero_linear_invariant',s.Matrix.vstack(*[A.T-I for A in axial]).rank()==3)
ok('O_dot_B_scalar_under_Oh',all(s.expand((A*O).dot(A*B)-OB)==0 for A in axial))
ok('O_squared_time_even',s.expand(O2.subs({x:-x,y:-y,z:-z})-O2)==0)
ok('O_dot_B_simultaneously_time_even',s.expand(OB.subs({x:-x,y:-y,z:-z,bx:-bx,by:-by,bz:-bz})-OB)==0)
ok('O_dot_fixed_B_time_odd_under_order_flip',s.expand(OB.subs({x:-x,y:-y,z:-z})+OB)==0)
# Proposed curvature coefficient in action sqrt(-g)*F R/2.
F=M2+2*xi*O2+2*eta*OB
ok('candidate_F_simultaneously_time_even',s.expand(F.subs({x:-x,y:-y,z:-z,bx:-bx,by:-by,bz:-bz})-F)==0)
ok('candidate_F_cubic_scalar',all(s.expand(M2+2*xi*(A*O).dot(A*O)+2*eta*(A*O).dot(A*B)-F)==0 for A in axial))
ok('quadratic_fixed_magnitude_reversal_same_F',
  s.expand(F.subs({bx:0,by:0,bz:0,x:-x,y:-y,z:-z})-F.subs({bx:0,by:0,bz:0}))==0)
# Only for an IDEALIZED homogeneous medium (no boundary): G_eff/G=M2/F.
ratio=s.simplify(M2/F.subs({bx:0,by:0,bz:0}))
required=M2*(1/q-1)/(2*O2)
sol=s.solve(s.Eq(ratio,q),xi)
ok('homogeneous_ratio_inverse_solve',len(sol)==1 and s.simplify(sol[0]-required)==0)
ok('xi_zero_reduces_to_standard',s.simplify(ratio.subs(xi,0)-1)==0)
ok('positive_M2_original_sector',s.simplify(F.subs({xi:0,eta:0})-M2)==0)
r=s.symbols('r',real=True); u=s.Function('u')(r)
Fprofile=M2+2*xi*u**2
second=s.diff(Fprofile,r,2)
ok('variable_order_gradient_terms',s.simplify(second-4*xi*(s.diff(u,r)**2+u*s.diff(u,r,2)))==0)
ok('uniform_order_no_gradient_term',s.simplify(second.subs({s.diff(u,r):0,s.diff(u,r,2):0}))==0)
ok('healthy_standard_kinetic_coefficient_control',s.simplify(F.subs({xi:0,eta:0})/M2-1)==0)
receipt={
 'scope':'symmetry-permitted speculative octupole-curvature EFT, not a measured PtMn3 gravity source',
 'checks_passed':len(checks),'checks':checks,
 'O_h_operations':len(rot),'time_even_order_scalar':str(O2),
 'candidate_field_dependent_Planck_coefficient':str(F),
 'ideal_homogeneous_Geff_over_G':str(ratio),
 'ideal_homogeneous_inverse_xi':str(required),
 'inhomogeneous_F_double_gradient':str(second),
 'opposite_domains_same_quadratic_gravity_source':True,
 'fixed_external_B_allows_sign_dependent_candidate':True,
 'observer_covariant_B_and_octupole_tensor_supplied':False,
 'measured_xi_eta':False,'complete_diffeomorphism_invariant_action_and_Tmunu':False,
 'measured_gravity_or_human_lift':False,
 'attribution':{'original_experiment':'Kang et al. Nature 2026 PtMn3 OTT/TMR',
 'established':'cubic representation and scalar-tensor effective-field-theory constraints',
 'new_DASHI':'exact selection-rule, source-gradient and inverse hypothesis audit'}}
if __name__=='__main__':print(json.dumps(receipt,sort_keys=True,indent=2))
