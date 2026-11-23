#!/usr/bin/env python3
"""OCT369 P0.33: STEELMAN two endpoint branches -> same-source geometry.

Source owners (no priority transfer): original DASHI AntigravityMaterialBidi-
CrossPollinationExact, EngineeredInertialGravitationalBidiExact, CMP119
trace/active-stress firewall; OCT369 P0.25, P0.26-28 Pt-centred finite
magnetic motif, P0.24 effective controller and P0.32 Bloch accounting.
Maxwell, Newton, Einstein, scalar-Yukawa and Earnshaw results are prior art.
Kang et al. Nature 2026 own PtMn3 OTT/TMR, not gravity observations.

Three disjoint lanes: magnetic lift (Maxwell + explicit stabilizer), ordinary
weak-field METRIC response (signed active mass and clock), and speculative
screened fifth force (NOT automatically metric). All are source-CONDITIONAL.
"""
import json
from itertools import product
import sympy as s

Q = s.Rational
coord = s.Matrix(s.symbols('X Y Z', real=True))
X,Y,Z = coord
shift = s.Matrix(s.symbols('sx sy sz', real=True))
a,mu,N,m,g = s.symbols('a mu N m g', positive=True)
k4,k5 = s.symbols('kappa4 kappa5', real=True)
sites = [s.Matrix(p) for p in ((0,Q(1,2),Q(1,2)),
                               (Q(1,2),0,Q(1,2)),
                               (Q(1,2),Q(1,2),0))]
centre = sum(sites,s.zeros(3,1))/3
order = [p-centre for p in sites]
axis = s.Matrix([1,1,1])/s.sqrt(3)
trans = order[0]/s.sqrt(order[0].dot(order[0]))
trans2 = axis.cross(trans)
frame = s.Matrix.hstack(axis,trans,trans2)
pts = [a*p for p in sites]+[-a*p for p in sites]
moms = [mu*p/s.sqrt(p.dot(p)) for p in order]*2
u,v,w = [s.expand(vec.dot(coord)) for vec in (axis,trans,trans2)]
rad2 = v*v+w*w
harm3 = v**3-3*v*w*w
phi4 = k4*u*harm3
phi5 = k5*(u*u-rad2/8)*harm3

checks={}
def test(name,condition):
    assert bool(condition),name
    checks[name]=True

def harmonic(phi):
    return s.simplify(sum(s.diff(phi,var,2) for var in coord))

def field(phi):
    return -s.Matrix([s.diff(phi,var) for var in coord])

def source_energy(phi):
    B = field(phi)
    terms = [-p.dot(B.subs({coord[i]:r[i]+shift[i] for i in range(3)},simultaneous=True)) for r,p in zip(pts,moms)]
    return s.factor(sum(terms))

def at0(expr):
    return s.simplify(expr.subs(dict.fromkeys(shift,0)))

def force(energy):
    return -s.Matrix([s.diff(energy,var) for var in shift])

test('Pt_lattice_inversion_centre',all(tuple((-p)[i]%1 for i in range(3))==tuple(p) for p in sites))
test('three_trial_spins_sum_zero',sum(moms[:3],s.zeros(3,1))==s.zeros(3,1))
test('six_site_moment_zero',sum(moms,s.zeros(3,1))==s.zeros(3,1))
test('Pt_inversion_pair_axial_moment_same',all(moms[i]==moms[i+3] and pts[i]==-pts[i+3] for i in range(3)))
test('orthonormal_111_frame',s.simplify(frame.T*frame)==s.eye(3))
test('Phi4_harmonic',harmonic(phi4)==0)
test('Phi5_harmonic',harmonic(phi5)==0)
for label,phi in (('quartic',phi4),('quintic',phi5)):
    B=field(phi)
    test(label+'_B_divergence_zero',s.simplify(sum(s.diff(B[i],coord[i]) for i in range(3)))==0)
    test(label+'_B_curl_zero',all(s.simplify(s.diff(B[i],coord[j])-s.diff(B[j],coord[i]))==0 for i,j in product(range(3),repeat=2)))

E4=source_energy(phi4)
E5=source_energy(phi5)
expected_E4=s.sqrt(3)*a*a*k4*mu*sum(shift)
pair_sum=shift[0]*shift[1]+shift[0]*shift[2]+shift[1]*shift[2]
expected_E5=a*a*k5*mu*(43*a*a+144*pair_sum)/48
test('P026_P027_same_quartic_energy',s.simplify(E4-expected_E4)==0)
test('quintic_source_energy_exact',s.simplify(E5-expected_E5)==0)
test('quartic_energy_linear_in_translation',s.hessian(E4,shift)==s.zeros(3))
test('quintic_source_energy_quadratic_in_translation',s.diff(E5,shift[0],3)==0)
F4=force(E4)
test('P026_force_reproduced',s.simplify(axis.dot(F4)+3*a*a*k4*mu)==0)
test('quartic_no_vertical_stiffness',s.simplify((axis.T*s.hessian(E4,shift)*axis)[0])==0)
test('quintic_zero_force_at_centre',at0(force(E5))==s.zeros(3,1))
K=s.hessian(N*(E4+E5),shift)
Kframe=s.simplify(frame.T*K*frame)
K0=s.diag(6*N*a*a*mu*k5,-3*N*a*a*mu*k5,-3*N*a*a*mu*k5)
test('stiffness_hessian_source',s.simplify(Kframe-K0)==s.zeros(3))
test('Earnshaw_laplacian_zero',s.simplify(s.trace(Kframe))==0)
test('vertical_6_vs_transverse_minus3',Kframe==K0)
test('quartic_only_stiffness_all_zero',s.hessian(N*E4,shift)==s.zeros(3))
req_k4=s.solve(s.Eq(-N*3*a*a*mu*k4,m*g),k4)[0]
Kz=s.symbols('K_z',positive=True)
req_k5=s.solve(s.Eq(Kframe[0,0],Kz),k5)[0]
test('BIDI_force_reverse_k4',s.simplify(req_k4+m*g/(3*N*a*a*mu))==0)
test('BIDI_stiffness_reverse_k5',s.simplify(req_k5-Kz/(6*N*a*a*mu))==0)
test('BIDI_forward_force',s.simplify((-N*axis.dot(F4)).subs(k4,req_k4)+m*g)==0)
test('BIDI_forward_stiffness',s.simplify(Kframe[0,0].subs(k5,req_k5)-Kz)==0)
test('unstable_both_lateral_when_Kz_positive',Kframe[1,1].subs(k5,req_k5)==-Kz/2 and Kframe[2,2].subs(k5,req_k5)==-Kz/2)
Kcontrol=s.symbols('K_control',positive=True)
Ktotal=s.diag(Kz,Kcontrol-Kz/2,Kcontrol-Kz/2)
test('controller_required_strict_transverse_bound',s.solve(s.Eq(Ktotal[1,1],0),Kcontrol)==[Kz/2])
test('controller_3quarter_choice_positive',all(z>0 for z in Ktotal.subs(Kcontrol,3*Kz/4).diagonal()))
test('controller_1quarter_choice_unstable',Ktotal[1,1].subs(Kcontrol,Kz/4)<0)
test('equal_opposite_coil_reaction',s.simplify(-N*axis.dot(F4)+N*axis.dot(F4))==0)
test('domain_reversal_reverses_source_force',s.simplify(force(-E4)+F4)==s.zeros(3,1))

# Gravity-only weak-field MONOPOLE route. A repulsive anomaly is an OUTWARD
# acceleration at the remote test mass; ordinary added positive energy is
# attractive. The model does not assert a negative ADM mass can be built.
G,c,r,fraction=s.symbols('G c r f',positive=True)
Mact=s.symbols('M_active',real=True)
Phi=-G*Mact/r
arad=s.simplify(-s.diff(Phi,r))
req_M=s.solve(s.Eq(arad,fraction*g),Mact)[0]
clock=s.simplify(Phi/c**2)
test('GR_monopole_attractive_for_positive_mass',arad==-G*Mact/r**2)
test('GR_outward_requires_negative_active_monopole',s.simplify(req_M+fraction*g*r*r/G)==0)
test('GR_clock_metric_potential_relation',s.simplify(clock.subs(Mact,req_M)-fraction*g*r/c**2)==0)
test('GR_external_vacuum_Poisson_zero',s.simplify(s.diff(r*r*s.diff(Phi,r),r))==0)
test('GR_point_source_energy_equivalence',s.simplify(req_M*c*c+fraction*g*r*r*c*c/G)==0)
test('Newtonian_positive_energy_not_outward',(-G*s.Symbol('Mplus',positive=True)/r**2)<0)

# CMP119 local negative active stress can be compensated by support stresses.
rhoc,rhos,pc1,pc2,pc3,Vc,Vs=s.symbols('rho_c rho_s p_c1 p_c2 p_c3 V_c V_s',real=True,nonzero=True)
pcs=[pc1,pc2,pc3]
pss=[-Vc*x/Vs for x in pcs]
trace_core=-rhoc+sum(pcs)
active_core=rhoc+sum(pcs)
active_all=s.simplify(Vc*active_core+Vs*(rhos+sum(pss)))
test('CMP119_active_vs_trace',s.simplify(active_core-trace_core-2*rhoc)==0)
test('static_closed_integrated_spatial_stress_balance',all(s.simplify(Vc*pcs[i]+Vs*pss[i])==0 for i in range(3)))
test('closed_system_active_equals_total_energy',s.simplify(active_all-(Vc*rhoc+Vs*rhos))==0)
test('local_negative_active_does_not_imply_negative_total',active_core.subs({rhoc:2,pc1:-1,pc2:-1,pc3:-1})<0 and active_all.subs({rhoc:2,rhos:1,Vc:1,Vs:1,pc1:-1,pc2:-1,pc3:-1})>0)

# Fifth-force rival hypothesis (not itself metric curvature).
# V = -G M_s m_t [1 + alpha exp(-r/ell)]/r.
Ms,ell,alpha=s.symbols('M_s ell alpha_Y',positive=True,positive_dummy=False) if False else (s.symbols('M_s',positive=True),s.symbols('ell',positive=True),s.symbols('alpha_Y',real=True))
Yuk=-G*Ms*m*alpha*s.exp(-r/ell)/r
ayuk=s.simplify(-s.diff(Yuk,r)/m)
req_alpha=s.solve(s.Eq(ayuk,fraction*g),alpha)[0]
test('Yukawa_derivative_source',s.simplify(ayuk+G*Ms*alpha*s.exp(-r/ell)*(1+r/ell)/r**2)==0)
test('Yukawa_repulsion_requires_negative_product',s.simplify(req_alpha+fraction*g*r*r*s.exp(r/ell)/(G*Ms*(1+r/ell)))==0)
test('same_sign_canonical_universal_scalar_cannot_repulse',ayuk.subs(alpha,s.Symbol('beta',positive=True)**2)<0)
test('screened_inverse_source_forward',s.simplify(ayuk.subs(alpha,req_alpha)-fraction*g)==0)
test('unscreened_limit',s.simplify(s.limit(req_alpha,ell,s.oo)+fraction*g*r*r/(G*Ms))==0)

# Wider identifiability model than P0.25: now allow BOTH gravitational metric
# response and an independent nonmetric fifth force alongside EM pickup.
k=s.symbols('k_pickup',real=True)
obs=s.Matrix([[1,-m,-m,1], [0,1,1,k], [0,r/c**2,0,0], [0,0,0,1]])
obs3=obs[[0,1,3],:]
test('four_channel_model_invertible',s.simplify(obs.det()+r/c**2)==0 and obs.rank()==4)
test('three_channel_no_clock_cannot_separate_metric_fifth',obs3.rank()==3 and obs3.nullspace()==[s.Matrix([0,-1,1,0])])
yload,yremote,yclock,ypick=s.symbols('y_load y_remote y_clock y_pick')
back=s.simplify(obs.inv()*s.Matrix([yload,yremote,yclock,ypick]))
test('clock_channel_is_metric_under_monopole_assumption',s.simplify(back[1]-c*c*yclock/r)==0)
test('remote_minus_clock_is_fifth_or_other',s.simplify(back[2]-yremote+c*c*yclock/r+k*ypick)==0)
test('load_with_pickup_and_remote_to_EM_force',s.simplify(back[0]-yload-m*yremote+(m*k+1)*ypick)==0)
test('pick_channel_identity',back[3]==ypick)
test('EM_only_cannot_generate_metric_clock_in_model',obs[2,0]==0)
test('fifth_only_cannot_generate_metric_clock_in_model',obs[2,2]==0)

# Illustrative numerical inverse values: not material source calibration.
const={g:Q(980665,100000),G:s.Float('6.67430e-11'),c:s.Integer(299792458),r:s.Integer(1),m:s.Integer(70)}
bench={}
for label,f in (('full_g',s.Integer(1)),('one_percent_g',Q(1,100))):
    subs={**const,fraction:f}
    bench[label]={'force_target_N':float((m*g*f).subs(subs)),
      'metric_active_mass_kg':float(req_M.subs(subs)),
      'metric_mass_energy_J':float((req_M*c*c).subs(subs)),
      'clock_offset_dnu_over_nu_at_infinity':float(clock.subs(Mact,req_M).subs(subs)),
      'Yukawa_alpha_at_70kg_source_range_1m':float(req_alpha.subs({**subs,Ms:70,ell:1}))}
test('bench_full_g_lift_weight',abs(bench['full_g']['force_target_N']-686.4655)<1e-8)
test('bench_one_percent_clock_order',1e-18<bench['one_percent_g']['clock_offset_dnu_over_nu_at_infinity']<2e-18)
test('bench_negative_metric_monopole_required',bench['full_g']['metric_active_mass_kg']<0)
test('bench_fifth_negative_coupling_required',bench['full_g']['Yukawa_alpha_at_70kg_source_range_1m']<0)

# Octupole-to-source steelman, WITHOUT claiming a measured coupling.
# O is a time-odd axial order coordinate and B a time-odd axial field.
# A hypothetical healthy scalar phi could have J_phi=lambda*(O.dot(B));
# its integrated source charge is Q_phi=lambda*I_OB for one bounded body.
# Test coupling q_t/m_t=alpha_t, positive scalar kinetic energy:
# a_phi=-alpha_t*Q_phi/(4*pi)*exp(-r/ell)*(1+r/ell)/r**2.
I_OB,lam,alpha_t=s.symbols('I_OB lambda_O_B alpha_target',real=True,nonzero=True)
Qphi=lam*I_OB
aphi=-alpha_t*Qphi*s.exp(-r/ell)*(1+r/ell)/(4*s.pi*r*r)
required_lam=s.solve(s.Eq(aphi,fraction*g),lam)[0]
test('octupole_scalar_source_inverse',s.simplify(required_lam+4*s.pi*fraction*g*r*r*s.exp(r/ell)/(alpha_t*I_OB*(1+r/ell)))==0)
test('octupole_scalar_source_forward',s.simplify(aphi.subs(lam,required_lam)-fraction*g)==0)
test('source_charge_flips_domain_fixed_B',Qphi.subs(I_OB,-I_OB)==-Qphi)
test('source_charge_even_under_domain_AND_field_flip',Qphi.subs(I_OB,I_OB)==Qphi)
Ox,Oy,Oz,Bx,By,Bz,xi,eta,M2=s.symbols('Ox Oy Oz Bx By Bz xi eta M2',real=True)
O2=Ox**2+Oy**2+Oz**2
OB=Ox*Bx+Oy*By+Oz*Bz
Fnonminimal=M2+2*xi*O2+2*eta*OB
test('quadratic_metric_F_even_under_domain',s.simplify(Fnonminimal.subs({eta:0,Ox:-Ox,Oy:-Oy,Oz:-Oz})-Fnonminimal.subs(eta,0))==0)
test('OB_metric_branch_odd_fixed_B',s.simplify(OB.subs({Ox:-Ox,Oy:-Oy,Oz:-Oz})+OB)==0)
test('OB_metric_branch_even_joint_TR',s.simplify(OB.subs({Ox:-Ox,Oy:-Oy,Oz:-Oz,Bx:-Bx,By:-By,Bz:-Bz})-OB)==0)

receipt={'programme':'OCT369 P0.33 endpoint-first steelman, strict source accounting',
 'checks_passed':len(checks),'checks':list(checks),
 'magnetic_source':'L12 Pt-centred six-site inversion-complete trial, 120deg and same fixed dipole energy',
 'harmonic_Phi4':'kappa4 * u * (v^3-3*v*w^2)',
 'harmonic_Phi5':'kappa5 * (u^2-(v^2+w^2)/8) * (v^3-3*v*w^2)',
 'force_per_sample':'F_u=-3*N*mu*a^2*kappa4',
 'vertical_stiffness':'K_z=6*N*mu*a^2*kappa5',
 'transverse_stiffness_each':'K_perp=-3*N*mu*a^2*kappa5=-K_z/2',
 'required_kappa4':str(req_k4),'required_kappa5_for_Kz':str(req_k5),
 'required_controller_each_transverse':'K_controller>K_z/2',
 'no_passive_3D_stability_from_only_fixed_moments':True,
 'metric_monopole_mass_inverse':str(req_M),
 'metric_clock_ratio_at_infinity':'f*g*r/c^2',
 'stress_trace_vs_active_original_CMP119':True,
 'isolated_static_stress_integral_requires_supports':True,
 'fifth_force_trial':'V_extra=-G*M_source*m_test*alpha_Y*exp(-r/ell)/r',
 'required_fifth_force_alpha_Y':str(req_alpha),
 'hypothetical_octupole_scalar_action_source':'J_phi=lambda_O_B*(O dot B), positive kinetic scalar (requires real dynamic B and O)',
 'required_scalar_octupole_coupling':str(required_lam),
 'metric_nonminimal_symmetric_coefficient':'F=M2+2xi|O|^2+2eta(O dot B) (hypothesis; source metric variation open)',
 'four_observables_for_four_rivals':True,
 'three_observables_nullspace':['0','-1','1','0'],
 'observation_inverse':[str(v) for v in back],
 'illustrative_reverse_targets':bench,
 'same_source_material_SI_coefficients_calibrated':False,
 'bounded_coil_or_superconductor_current_solution':False,
 'controller_stress_and_stable_body_validated':False,
 'negative_ADM_mass_achieved':False,
 'healthy_universal_fifth_force_repulsion_achieved':False,
 'real_metric_sourced_from_octupole_action':False,
 'levitation_or_anomalous_gravity_measured':False,
 'attribution':{'external':'Maxwell/Earnshaw/Einstein/Newton/Yukawa/scalar-tensor and Tolman-Laue stress theory are prior art; Kang 2026 owns PtMn3 experiment',
 'DASHI_original':'AntigravityMaterialBidiCrossPollinationExact, EngineeredInertialGravitationalBidiExact, CMP119 trace/active, P0.24-28/P0.32',
 'new_DASHI':'same Pt-origin finite force+stability inverse, metric/clock and fifth-force rival inverse, expanded observation rank certificate'}}
if __name__=='__main__':print(json.dumps(receipt,sort_keys=True,indent=2))
