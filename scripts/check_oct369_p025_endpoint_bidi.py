#!/usr/bin/env python3
"""OCT369 P0.25 steelman BIDI: native geometry address and endpoint inverse.
Original owners: DASHI L12 T1g (P0.14), balanced-ternary cube/13 antipodes,
DASHI AntigravityMaterialBidiCrossPollinationExact six typed claims,
DASHI CMP119 trace/active-stress. This finite chart is NOT a physical
coordinates equivalence, measured PtMn3 coupling or gravitational proof.
Experiment credit: Kang et al. Nature (2026), DOI 10.1038/s41586-026-11172-5.
"""
import json
from itertools import permutations,product
import sympy as s
Q=s.Rational;I=s.eye(3)
sites=[s.Matrix(v) for v in ((0,Q(1,2),Q(1,2)),(Q(1,2),0,Q(1,2)),(Q(1,2),Q(1,2),0))]
center=sum(sites,s.zeros(3,1))/3
spins=[v-center for v in sites]
C3=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
chart=[(-1,0,1),(1,-1,0),(0,1,-1)]
def xyz(v):return tuple(v)
def cycle(v):return xyz(C3*s.Matrix(v))
def encode(i,d):return xyz(s.Integer(d)*s.Matrix(chart[i]))
decode={encode(i,d):(i,d) for i in range(3) for d in (-1,1)}
cube=set(product((-1,0,1),repeat=3));punct=cube-{(0,0,0)}
pairs={frozenset((v,tuple(-t for t in v))) for v in punct}
covered={frozenset((v,tuple(-t for t in v))) for v in decode}
rot=[]
for p in permutations(range(3)):
 for signs in product((-1,1),repeat=3):
  R=s.zeros(3)
  for i in range(3):R[i,p[i]]=signs[i]
  if R.det()==1:rot.append(R)
def mod1(v):return tuple(t%1 for t in v)
def site_perm(R):
 P=s.zeros(3)
 for a,v in enumerate(sites):
  b=next(i for i,w in enumerate(sites) if mod1(R*v)==mod1(w))
  P[b,a]=1
 return P
D=[s.kronecker_product(site_perm(R),R) for R in rot]
PT1=Q(3,24)*sum((s.trace(R)*d for R,d in zip(rot,D)),s.zeros(9))
PD=s.kronecker_product(s.ones(3)/3,I);PA=PT1-PD;PT2=s.eye(9)-PT1
X=s.Matrix.vstack(*spins);probe=PA*X
overlap=(X.T*probe)[0];overlap_flip=((-X).T*probe)[0];O2=(X.T*PA*X)[0]
checks={}
def ok(label,cond):
 assert bool(cond),label
 checks[label]=True
ok('three_crystal_sites',len(sites)==3)
ok('C3_crystal_sites',all(C3*sites[i]==sites[(i+1)%3] for i in range(3)))
ok('zero_total_spin',sum(spins,s.zeros(3,1))==s.zeros(3,1))
ok('120_degree_spins',all(spins[i].dot(spins[j])==-spins[i].dot(spins[i])/2 for i in range(3) for j in range(i+1,3)))
ok('24_cubic_operations',len(rot)==24)
ok('T1g_projector_resolution',PA+PD+PT2==s.eye(9))
ok('T1g_AFM_projector',PA*PA==PA)
ok('T1g_AFM_rank3',PA.rank()==3)
ok('trial_inside_T1g_AFM',PA*X==X)
ok('zero_uniform_dipole',PD*X==s.zeros(9,1))
ok('zero_T2g_projection',PT2*X==s.zeros(9,1))
ok('order_norm_half',O2==Q(1,2))
ok('probe_overlap_half',overlap==Q(1,2))
ok('domain_reversal_odd_probe_overlap',overlap_flip==-overlap)
ok('27_cells',len(cube)==27)
ok('26_punctured',len(punct)==26)
ok('13_antipodal_pairs',len(pairs)==13)
ok('six_unique_address_states',len(decode)==6)
ok('three_occupied_antipodal_pairs',len(covered)==3)
ok('20_residual_punctured_cells',len(punct-set(decode))==20)
ok('10_unoccupied_antipodal_pairs',len(pairs-covered)==10)
ok('21_unassigned_cube_cells',len(cube-set(decode))==21)
ok('cube_center_unassigned',(0,0,0) not in decode)
ok('encoding_C3_covariant',all(cycle(encode(i,d))==encode((i+1)%3,d) for i in range(3) for d in (-1,1)))
ok('encoding_antipodal_sign',all(encode(i,-d)==tuple(-t for t in encode(i,d)) for i in range(3) for d in (-1,1)))
ok('forward_backward_BIDI',all(decode[encode(i,d)]==(i,d) for i in range(3) for d in (-1,1)))
ok('backward_forward_BIDI',all(encode(*decode[v])==v for v in decode))
ok('residuals_do_not_decode',all(v not in decode for v in cube-set(decode)))
ok('each_z_sheet_two_selected',all(sum(v[2]==z for v in decode)==2 for z in (-1,0,1)))
ok('middle_punctured_sheet_eight',sum(v[2]==0 for v in punct)==8)
# EXACT native six typed antigravity claim/discriminator names.
claims={
 'reducedPassiveWeight':'staticLoadDiscriminator',
 'changedFreeFallResponse':'freeFallDiscriminator',
 'remoteRepulsiveField':'externalTestMassDiscriminator',
 'alteredInertialResponse':'inertialComparisonDiscriminator',
 'persistentPropulsiveImpulse':'momentumClosureDiscriminator',
 'engineeredMetricResponse':'metricClockDiscriminator'}
ok('six_typed_claims',len(claims)==6)
ok('six_distinct_discriminators',len(set(claims.values()))==6)
m,g,N,grad=s.symbols('m g N grad_h',positive=True)
body=N*grad*overlap;support=-body
required=s.solve(s.Eq(body,m*g),grad)[0]
ok('force_backward_solve',s.simplify(required-2*m*g/N)==0)
ok('gradient_zero_no_force',body.subs(grad,0)==0)
ok('external_reaction_balance',body+support==0)
ok('spin_domain_flip_force_reverses',s.simplify(N*grad*overlap_flip+body)==0)
ok('70kg_inverse_source',required.subs({m:70,g:Q(980665,100000)})==Q(1372931,1000)/N)
M2,xi,qratio=s.symbols('M2 xi q',positive=True)
Fc=M2+2*xi*O2;ratio=M2/Fc
inverse_xi=s.solve(s.Eq(ratio,qratio),xi)[0]
ok('quadratic_curvature_order_sign_even',s.simplify(((-X).T*PA*(-X))[0]-O2)==0)
ok('healthy_homogeneous_ratio_positive',ratio>0)
ok('curvature_ratio_inverse',s.simplify(inverse_xi-M2*(1/qratio-1)/(2*O2))==0)
ok('healthy_finite_ratio_nonzero',s.simplify(ratio*Fc-M2)==0)
Gc=s.Rational(667430,10**16);c=s.Integer(299792458);r=s.symbols('r',positive=True)
mass_equiv=g*r*r/Gc;energy_equiv=mass_equiv*c*c
ok('minimal_remote_GR_reverse',s.simplify(Gc*energy_equiv/(c*c*r*r)-g)==0)
ok('minimal_GR_target_not_magnetic_lift',mass_equiv.has(g,r))
EM,a,p,k=s.symbols('F_EM a_grav p_pickup k_pickup',real=True)
obs=s.Matrix([[1,-m,1],[0,1,k],[0,0,1]])
reduced=obs[:2,:]
load,remote,pick=s.symbols('load remote pickup',real=True)
back=obs.inv()*s.Matrix([load,remote,pick])
ok('three_sensors_full_rank',obs.det()==1 and obs.rank()==3)
ok('two_sensors_rank_deficient',reduced.rank()==2 and reduced.nullspace()==[s.Matrix([-m*k-1,-k,1])])
ok('inverse_gravity',s.simplify(back[1]-(remote-k*pick))==0)
ok('inverse_EM_force',s.simplify(back[0]-(load+m*(remote-k*pick)-pick))==0)
ok('inverse_pickup',back[2]==pick)
ok('EM_only_observables',obs*s.Matrix([EM,0,0])==s.Matrix([EM,0,0]))
ok('gravity_only_observables',obs*s.Matrix([0,a,0])==s.Matrix([-m*a,a,0]))
ok('pickup_only_observables',obs*s.Matrix([0,0,p])==s.Matrix([p,k*p,p]))
rho,p1,p2,p3=s.symbols('rho p_x p_y p_z',real=True)
tr=-rho+p1+p2+p3;active=rho+p1+p2+p3
ok('active_stress_equals_trace_plus_twice_rho',s.simplify(active-tr-2*rho)==0)
ok('negative_trace_not_negative_active_source',tr.subs({rho:1,p1:0,p2:0,p3:0})<0 and active.subs({rho:1,p1:0,p2:0,p3:0})>0)
psi=s.Matrix([1,0]);sig=s.diag(1,-1)
ok('spinor_center_sign_not_domain_reversal',(((-psi).H*sig*(-psi))[0]==(psi.H*sig*psi)[0]))
receipt={
 'scope':'steelman P0.25: source BIDI on native 27/26/13 ADDRESSES, not physical coordinate identity',
 'checks_passed':len(checks),'checks':checks,
 'L12_Mn_sites':[[str(t) for t in v] for v in sites],
 'C3_chart_orbit':chart,'site_domain_labels':6,'antipodal_pairs_covered':3,
 'residual_antipodal_pairs':10,'residual_cube_addresses':21,
 'AFM_T1g_projector_rank':PA.rank(),'selected_order_overlap':str(overlap),
 'typed_claims':claims,
 'EM_lift_required_conjugate_gradient':'2*m*g/N (unmeasured generalized source units)',
 'minimal_GR_mass_equivalent_magnitude':'g*r**2/G',
 'minimal_GR_energy_equivalent_magnitude':'g*c**2*r**2/G',
 'homogeneous_curvature_xi_inverse':str(inverse_xi),
 'rank_with_pickup_measurement':obs.rank(),
 'rank_without_pickup_measurement':reduced.rank(),
 'rank_two_null_direction':[str(t) for t in reduced.nullspace()[0]],
 'negative_trace_not_sufficient_for_active_repulsion':True,
 'actual_crystal_to_ternary_metric_isometry':False,
 'measured_PtMn3_hamiltonian_and_couplings':False,
 'Maxwell_SC_battery_controller_stress_from_action':False,
 'measured_gravitational_field_or_human_lift':False,
 'Agda_kernel_typecheck':'not_run',
 'source_owners':{
  'native':'AntigravityMaterialBidiCrossPollinationExact, CMP119AntigravityTraceVsActiveStressFirewallExact, Base369Ternary27HypervoxelFabricGeometryExact, Punctured27NineSheetBridgeExact, HyperfabricPunctured27Projective13OrientationExact, OCT369 P0.14-24',
  'science':'Hamilton/Cartan, cubic group representation, Maxwell/Newton/Einstein',
  'experiment':'Kang et al Nature 2026 DOI:10.1038/s41586-026-11172-5',
  'new_DASHI':'finite same-carrier six-address partial codec, endpoint reverse-solver and three-channel sensor-rank certificate'}
}
if __name__=='__main__':print(json.dumps(receipt,sort_keys=True,indent=2))
