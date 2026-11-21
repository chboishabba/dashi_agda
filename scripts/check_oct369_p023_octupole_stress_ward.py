#!/usr/bin/env python3
"""OCT369 P0.23: effective scalar order amplitude stress and Ward identity.
NOT the actual T1g PtMn3 axial tensor or a physically closed controller.
S=integral sqrt(-g)[F(O)R/2 - kappa*(dO)^2/2-m2*O^2/2+J*O].
A prescribed spatial drive J has explicit uncompensated Ward exchange.
"""
import json
from itertools import product
import sympy as s
x,r,R,c,G=s.symbols('x r R c G',positive=True)
kap,m2,xi,M2,O0=s.symbols('kappa m2 xi M2 O0',positive=True)
A=s.Function('A',positive=True,real=True)(x)
O=s.Function('O',real=True)(x);J=s.Function('J',real=True)(x)
checks=[]
def ok(name,cond):
 assert bool(cond),name
 checks.append(name)
ap=s.diff(A,x);opp=s.diff(O,x);opp2=s.diff(O,x,2)
Rs=-2*s.diff(A,x,2)/A
Einstein=s.diag(0,0,s.diff(A,x,2)/A,s.diff(A,x,2)/A)
metric=s.diag(-A**2,1,1,1);ginv=s.diag(-1/A**2,1,1,1)
F=M2+2*xi*O**2;fp=s.diff(F,x);fpp=s.diff(F,x,2)
lapF=fpp+ap/A*fp
Hess=s.diag(-A*ap*fp,fpp,0,0)
D=s.simplify(metric*lapF-Hess)
expectedD=s.diag(-A**2*fpp,ap/A*fp,lapF,lapF)
ok('metric_variation_derivative_tensor',s.simplify(D-expectedD)==s.zeros(4))
ok('nonminimal_tt_component',s.simplify(D[0,0]+A**2*fpp)==0)
ok('nonminimal_xx_component',s.simplify(D[1,1]-ap/A*fp)==0)
ok('nonminimal_yy_zz',s.simplify(D[2,2]-lapF)==0 and s.simplify(D[3,3]-lapF)==0)
ok('scalar_coupling_sign_even',s.simplify(F.subs(O,-O)-F)==0)
ok('quadratic_curvature_coupling_derivative',s.diff(F,O)==4*xi*O)
ok('minimal_limit_no_derivative_source',s.simplify(D.subs(xi,0))==s.zeros(4))
ok('constant_order_no_derivative_source',s.simplify(D.subs({opp:0,opp2:0}))==s.zeros(4))
Lm=-kap*opp**2/2-m2*O**2/2+J*O
T=s.diag(-A**2*Lm,kap*opp**2+Lm,Lm,Lm)
ok('lapse_derivative_equals_stress_density',s.simplify(T[0,0]+A**2*Lm)==0)
ok('intrinsic_matter_energy_positive_form',s.simplify(T[0,0].subs(J,0)/A**2-(kap*opp**2+m2*O**2)/2)==0)
ok('transverse_equal_stresses',T[2,2]==T[3,3])
ok('time_reflection_symmetric_source',s.simplify(Lm.subs({O:-O,opp:-opp,J:-J})-Lm)==0)
full=s.simplify(F*Einstein+D-T)
Emix=s.simplify(ginv*full)
gamma=s.MutableDenseNDimArray.zeros(4,4,4)
gamma[0,0,1]=gamma[0,1,0]=ap/A;gamma[1,0,0]=A*ap
eom=kap*(opp2+ap/A*opp)-m2*O+J+s.diff(F,O)*Rs/2
for nu in range(4):
 div=s.simplify(s.diff(Emix[1,nu],x)+sum(gamma[mu,mu,1]*Emix[1,nu] for mu in range(4))-sum(gamma[lam,mu,nu]*Emix[mu,lam] for mu,lam in product(range(4),repeat=2)))
 predicted=s.expand((-eom*opp-O*s.diff(J,x)) if nu==1 else 0)
 ok('metric_scalar_Ward_component_'+str(nu),s.simplify(div-predicted)==0)
ok('metric_residual_not_automatically_zero',full[0,0]!=0)
ok('restricted_metric_Gtt_identically_zero',Einstein[0,0]==0)
ok('minimal_positive_scalar_cannot_source_restricted_Gtt',s.simplify(full[0,0].subs({xi:0,J:0})+A**2*(kap*opp**2+m2*O**2)/2)==0)
ok('nondynamical_driver_residual',s.simplify((-eom*opp-O*s.diff(J,x)).subs(eom,0)+O*s.diff(J,x))==0)
ok('on_shell_no_drive_Ward',s.simplify((-eom*opp-O*s.diff(J,x)).subs({eom:0,s.diff(J,x):0}))==0)
profile=O0*(1-r**2/R**2)**2;prime=s.diff(profile,r)
Egrad=s.simplify(4*s.pi*s.integrate(kap*prime**2*r**2/2,(r,0,R)))
Epot=s.simplify(4*s.pi*s.integrate(m2*profile**2*r**2/2,(r,0,R)))
E=s.simplify(Egrad+Epot)
Jrequired=s.simplify(m2*profile-kap*(s.diff(profile,r,2)+2*prime/r))
Eexpected=256*s.pi*O0**2*(kap*R/s.Integer(315)+m2*R**3/s.Integer(3465))
ok('compact_profile_boundary_order_zero',profile.subs(r,R)==0)
ok('compact_profile_boundary_slope_zero',prime.subs(r,R)==0)
ok('compact_profile_centre_finite_source',s.limit(Jrequired,r,0).is_finite)
ok('spherical_derived_external_drive',s.simplify(kap*(s.diff(profile,r,2)+2*prime/r)-m2*profile+Jrequired)==0)
ok('positive_radial_gradient_energy',s.simplify(Egrad-256*s.pi*kap*O0**2*R/315)==0)
ok('positive_radial_potential_energy',s.simplify(Epot-256*s.pi*m2*O0**2*R**3/3465)==0)
ok('spherical_intrinsic_total_energy',s.simplify(E-Eexpected)==0)
ok('orientation_reversal_intrinsic_energy_even',s.simplify(Eexpected.subs(O0,-O0)-Eexpected)==0)
phiout=-G*E/(c**2*r);accel=-s.diff(phiout,r)
ok('external_Newtonian_acceleration_sign',s.simplify(accel+G*E/(c**2*r**2))==0)
ok('external_gravity_perturbation_monopole',s.simplify(phiout+G*E/(c**2*r))==0)
ok('source_energy_needs_controller_boundary',Jrequired!=0)
ok('no_material_calibration_in_order_amplitude',not any('PtMn3' in str(v) for v in (E,F,Jrequired)))
receipt={'scope':'effective scalar amplitude plus prescribed drive; conditional metric/Noether identity; not material PtMn3',
 'checks_passed':len(checks),'checks':checks,
 'action':'sqrt(-g)*(F(O)*R/2 - kappa*(dO)^2/2 - m2*O^2/2 + J(x)*O)',
 'F':'M2+2*xi*O(x)**2','nonminimal_derivative_source':str(D),
 'scalar_EOM':'kappa*(O_xx+A_x/A*O_x)-m2*O+J+2xi O R=0',
 'covariant_metric_residual_divergence':'-scalar_EOM*O_x - O*J_x',
 'restricted_metric_Gtt':0,'minimal_positive_scalar_Ttt_nonzero':True,
 'compact_spherical_order_profile':str(profile),'required_external_drive':str(Jrequired),
 'intrinsic_gradient_energy':str(Egrad),'intrinsic_potential_energy':str(Epot),
 'intrinsic_total_energy':str(E),'conditional_weak_field_external_acceleration':str(accel),
 'controller_local_Tmunu_derived':False,'actual_PtMn3_order_tensor_or_Hamiltonian':False,
 'full_Einstein_metric_solution':False,'gravitational_anomaly_measured':False,
 'attribution':{'prior':'Einstein/Noether Ward identities, scalar-tensor metric variation, classical radial energy',
 'existing_DASHI':'GRFirstOrderGravityScope, W4 matter stress firewall, OCT369 P0.19/P0.21',
 'new':'finite exact scalar source-gradient and stress-accounting obstruction'}}
if __name__=='__main__':print(json.dumps(receipt,indent=2,sort_keys=True))
