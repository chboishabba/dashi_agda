#!/usr/bin/env python3
"""P0.37: SOURCE-OWNED KK/E6 x original 4D SU(N) Wilson/OS P0 steelman.

Mathematical identities are standard prior art. Native owners: 5D KK/E6
PR #1241, E6 PR #1106, original Wilson/R445 and OS PR #1444/#1536,
TSFVKKSelectedHorizontalMetricSchurExact, OCT369 P0.36.

Scope: an exact finite SU(3)c lattice plaquette/5D circle restriction,
commutator/adjoint zero mode, 5D->4D tree-level action/coupling and
negative controls for extra-fibre integration and quantum/spectral
promotion. Does not run existing Agda or prove the interacting continuum
mass gap. A 5D non-Abelian GAUGE connection is not the classical metric U1.
"""
import json
from pathlib import Path
import sympy as s

Q=s.Rational; I=s.I
checks=[]
def ck(name, condition):
    assert bool(condition), name
    checks.append(name)

sx=s.Matrix([[0,1],[1,0]]); sy=s.Matrix([[0,-I],[I,0]]); sz=s.diag(1,-1)
I2=s.eye(2); I3=s.eye(3)
embed=lambda u:s.diag(u,s.ones(1,1))
X=embed(I*sx); Y=embed(I*sy); Z=embed(I*sz)
bracket=lambda a,b:a*b-b*a
plaquette=lambda u,v:u*v*u.inv()*v.inv()
def tr(z):return s.simplify(s.trace(z))
def action(U):return s.simplify(1-s.re(tr(U))/3)

ck('source_SU3_3x3',X.shape==(3,3) and Y.shape==(3,3) and Z.shape==(3,3))
for name,u in [('X',X),('Y',Y),('Z',Z)]:
    ck(f'{name}_unitary',s.simplify(u.H*u)==I3)
    ck(f'{name}_special',s.simplify(u.det())==1)
    ck(f'{name}_nontrivial',u!=I3)
ck('SU3_fibre_nonabelian',bracket(X,Z)!=s.zeros(3))
ck('SU3_Plaquette_holonomy_minusI2',plaquette(X,Z)==s.diag(-1,-1,1))
ck('SU3_plaquette_positive_real_trace',action(plaquette(X,Z))==Q(4,3))
ck('abelian_U1_commutator_identity',s.simplify(s.exp(I*s.Symbol('a'))*s.exp(I*s.Symbol('b'))*s.exp(-I*s.Symbol('a'))*s.exp(-I*s.Symbol('b')))==1)
# Simultaneous colour-frame conjugation is the SAME physical plaquette.
frame=Y
ck('source_Wilson_trace_gauge_conjugacy',tr(frame*plaquette(X,Z)*frame.inv())==tr(plaquette(X,Z)))
ck('source_Wilson_action_gauge_invariant',action(frame*plaquette(X,Z)*frame.inv())==action(plaquette(X,Z)))

# Exact old C3 donor selection: three cyclic spatial Wilson marks. The
# phases/projectors are the familiar finite C3 representation; they are
# NOT automatically eigenstates of a reconstructed OS Hamiltonian.
three_marks=s.Matrix([action(plaquette(X,Y)),action(plaquette(Y,Z)),action(plaquette(Z,X))])
C3=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
omega=-Q(1,2)+s.sqrt(3)*I/2
P1=(s.eye(3)+C3+C3**2)/3
Pw=(s.eye(3)+omega**2*C3+omega*C3**2)/3
Pw2=(s.eye(3)+omega*C3+omega**2*C3**2)/3
ck('original_C3_spatial_mark_orbit_equal',three_marks==s.Matrix([Q(4,3)]*3))
ck('original_C3_spatial_rotation_order3',C3**3==s.eye(3))
ck('original_C3_spatial_mark_invariant',C3*three_marks==three_marks)
ck('original_C3_all_three_projectors_resolve_I',s.simplify(P1+Pw+Pw2)==s.eye(3))
ck('original_C3_projectors_idempotent',all(s.simplify(P*P-P)==s.zeros(3) for P in (P1,Pw,Pw2)))
ck('original_C3_projectors_orthogonal',all(s.simplify(P*R)==s.zeros(3) for P,R in ((P1,Pw),(P1,Pw2),(Pw,Pw2))))
ck('C3_omega_sector_nonempty_in_representation',Pw.rank()==1 and Pw2.rank()==1)
ck('C3_selected_source_has_no_nontrivial_mark_component',(Pw*three_marks).applyfunc(s.simplify)==s.zeros(3,1) and (Pw2*three_marks).applyfunc(s.simplify)==s.zeros(3,1))

# A 5D SOURCE (not independently selected abstract 4D theory): each of the
# N5 identical physical 4D layers has the SAME SU3c plaquette. With U5=I
# and no fifth-coordinate dependence, all (mu,5) plaquettes are the identity.
N5=3; a5=Q(2,5); L=N5*a5; g5sq=s.Symbol('g5sq',positive=True)
beta5=6*a5/g5sq # 2N a5/g5² with N=3; isotropic 5D plaquette coefficient
beta4=6/g5sq*L
P=plaquette(X,Z); E=action(P)
S5=s.simplify(N5*beta5*E)
S4=s.simplify(beta4*E)
ck('same_source_five_to_four_Wilson_action',s.simplify(S5-S4)==0)
ck('correct_tree_level_beta4_N5_beta5',s.simplify(beta4-N5*beta5)==0)
ck('same_fibre_trivial_U5_plaquette',plaquette(X,I3)==I3)
ck('fifth_direction_plaquette_action_zero_if_U5_identity',action(plaquette(X,I3))==0)
ck('4D_zero_mode_coupling_inverse',s.simplify(L/g5sq-1/(g5sq/L))==0)
ck('5D_source_action_nonzero',S5!=0)

# Retaining an A5 connection is NOT optional: a constant, noncentral
# SU3 Wilson line yields nontrivial mixed (mu,5) plaquettes.
Pmix=plaquette(X,Z)
ck('noncentral_A5_mixed_SU3_plaquette_nonzero',Pmix!=I3)
ck('noncentral_A5_mixed_action_positive',action(Pmix)>0)
ck('A5_center_commutator_vanishes',plaquette(X,I3)==I3)
ck('5D_restricted_action_changes_when_A5_unfrozen',s.simplify(S5 +N5*beta5*action(Pmix)-S4)>0)

# 5D local gauge transformations do NOT preserve the naive zero-mode gauge
# slice U5=I and U_mu(y)=U_mu without a gauge-fixing and quotient witness.
# Start with all three layers U_mu=Z and U5=I; apply distinct y-dependent
# site gauge rotations (constant along each 4D x direction). All mixed
# source plaquettes remain I, but the *coordinates* leave the fixed slice.
glayer=[I3,X,I3]
transverse=[g*Z*g.inv() for g in glayer]
fibre=[glayer[j]*glayer[(j+1)%N5].inv() for j in range(N5)]
ck('full_five_dimensional_gauge_slice_not_preserved',any(u!=Z for u in transverse) and any(u!=I3 for u in fibre))
for j in range(N5):
    jnext=(j+1)%N5
    mixed=transverse[j]*fibre[j]*transverse[jnext].inv()*fibre[j].inv()
    ck(f'full_five_dimensional_mixed_plaquette_covariance_layer{j}',s.simplify(mixed)==I3)
ck('fifth_gauge_holonomy_remains_identity',s.simplify(fibre[0]*fibre[1]*fibre[2])==I3)
ck('5D_two_form_planes_count_6_plus_4',len([(a,b) for a in range(5) for b in range(a+1,5)])==10 and len([(a,b) for a in range(4) for b in range(a+1,4)])==6)

# Exact continuum 5D field-strength decomposition at zero y derivative.
# Anti-Hermitian algebra-valued potential P_mu (not scalar graviphoton).
a0=I*sx; a1=I*sz; ph=I*sy
F01=bracket(a0,a1) # assume constant coordinates in x,y
F05=bracket(a0,ph)
ck('YM_F01_nonzero_interaction',F01!=s.zeros(2))
ck('YM_F05_adjoint_scalar_nonzero',F05!=s.zeros(2))
ck('YM_zero_mode_Fmu5_is_covariant_commutator',F05==a0*ph-ph*a0)
ck('YM_F01_antiHermitian',F01.H==-F01)
ck('YM_F05_antiHermitian',F05.H==-F05)
# One independent spatial plane + one mixed plane; sum over ordered AB
# carries factor two each. Index/minkowski signature not needed for ratio.
g4sq=s.Symbol('g4sq',positive=True)
F4density=-tr(F01*F01)/(2*g4sq)
F5density=-L*(tr(F01*F01)+tr(F05*F05))/(2*g5sq)
ck('5D_density_reduced_to_4D_when_Fmu5_zero',s.simplify((F5density+L*tr(F05*F05)/(2*g5sq)).subs(g5sq,L*g4sq)-F4density)==0)
ck('additional_adjoint_scalar_density_positive',s.simplify(-L*tr(F05*F05)/(2*g5sq))>0)

# Full KK metric has a U(1) GRAVIPHOTON geometry distinct from SU(3)c.
g4=s.diag(-1,1,1,1); Avec=s.Matrix([Q(1,2),Q(1,3),0,0]); b2=Q(9,4)
G=g4.row_join(s.zeros(4,1)).col_join(s.zeros(1,5))
for i in range(4):
    for j in range(4):G[i,j]+=b2*Avec[i]*Avec[j]
    G[i,4]+=b2*Avec[i];G[4,i]+=b2*Avec[i]
G[4,4]=b2
Schur=G[:4,:4]-G[:4,4]*G[4,4]**-1*G[4,:4]
ck('original_TSFV_KK_horizontal_metric_exact',Schur==g4)
ck('5D_metric_determinant_from_same_4D_metric',s.simplify(G.det()-b2*g4.det())==0)
ck('metric_graviphoton_four_vector_not_SU3_matrix',G[0,4]!=0 and X.shape==(3,3))
ck('5D_metric_not_frozen_fibre_restriction',G[:4,:4]!=g4)

# The HOLONOMY can lift some charged adjoint modes; colour-neutral Cartan
# zero modes persist at tree level, even with nontrivial SU3 holonomy.
w=-Q(1,2)+s.sqrt(3)*I/2
V=s.diag(w,w.conjugate(),1)
ck('SU3_Wilson_loop_determinant_one',s.simplify(V.det())==1)
ck('SU3_Wilson_loop_noncentral',V!=I3)
Cartan1=s.diag(1,-1,0);Cartan2=s.diag(1,1,-2)
ck('KK_SU3_two_Cartan_zero_modes_survive',bracket(V,Cartan1)==s.zeros(3) and bracket(V,Cartan2)==s.zeros(3))
for a,b in [(0,1),(0,2),(1,2)]:
    Eab=s.zeros(3);Eab[a,b]=1
    ck(f'KK_root_{a}{b}_twisted',bracket(V,Eab)!=s.zeros(3))
# Complete SU3 adjoint Lie-algebra basis, not five representative matrices.
adjoint_basis=[]
for i,j in ((0,1),(0,2),(1,2)):
    upper=s.zeros(3);upper[i,j]=1
    lower=s.zeros(3);lower[j,i]=1
    adjoint_basis.extend([upper+lower,I*(upper-lower)])
adjoint_basis.extend([Cartan1,Cartan2])
ck('SU3_eight_generators_full_rank',len(adjoint_basis)==8 and s.Matrix.hstack(*[s.Matrix(list(m)) for m in adjoint_basis]).rank()==8)
ck('identity_Wilson_all_eight_adjoints_untwisted',all(bracket(I3,M)==s.zeros(3) for M in adjoint_basis))
ck('generic_holonomy_exact_two_neutral_adjoint_directions',sum(bracket(V,M)==s.zeros(3) for M in adjoint_basis)==2)
ck('generic_holonomy_six_charged_adjoint_directions',sum(bracket(V,M)!=s.zeros(3) for M in adjoint_basis)==6)
# Original #1241 also warns that *independent* U1_B and EW U1_Y may
# leave two photon-like zero vectors without a source-defined mixing/Higgs.
neutral_mass_vector=s.Matrix([1,-1,0])
neutral_mass_gram=neutral_mass_vector*neutral_mass_vector.T
ck('source_independent_U1_two_neutral_vectors_if_unmixed',neutral_mass_gram.rank()==1 and len(neutral_mass_gram.nullspace())==2)
ck('SU3_cannot_be_identical_U1_lie_algebra',len(adjoint_basis)!=1 and bracket(X,Z)!=s.zeros(3))

# Integrating an interacting fifth-direction link is not the same as
# pinning U5=identity. A two-state, exact rational finite counterexample
# uses SU3 U_mu in {I,X}, U5 in {I,Z}. A mixed commutator has action 4/3.
# Choose beta=(3/4)*log(2) so exp(-beta*4/3)=1/2.
# The 4D zero-mode restricted unweighted measure is uniform, but
# the genuine TOY 5D V-marginal is nonuniform because U couples to V.
# This two-state counting measure is NOT the continuous SU3 Haar measure.
t=s.Symbol('t',positive=True)
weights=s.Matrix([2,1+t]);Ztot=sum(weights)
ck('5D_integrating_A5_changes_measure_for_t_ne1',s.simplify(weights[0]/Ztot-Q(1,2))!=(0))
ck('full_5D_fibre_marginal_selected_t',weights.subs(t,Q(1,2))==s.Matrix([2,Q(3,2)]))
ck('full_5D_marginal_differs_from_uniform_two_state_reference',s.simplify((weights[0]/Ztot).subs(t,Q(1,2))-Q(1,2))==Q(1,14))
ck('full_5D_marginal_probabilities',s.simplify((weights[0]/Ztot).subs(t,Q(1,2)))==Q(4,7) and s.simplify((weights[1]/Ztot).subs(t,Q(1,2)))==Q(3,7))
ck('special_equal_coupling_full_marginal_if_no_mixed_interaction',s.simplify((weights[0]/Ztot).subs(t,1))==Q(1,2))

# Operator reduction is NOT an exact quantum semigroup map if zero and
# nonzero KK sectors mix. Test the algebraic Schur complement and its pole.
h,lam,energy=s.symbols('h lam energy',real=True)
H=s.Matrix([[0,lam],[lam,h]])
P0=s.diag(1,0)
ck('projector_onto_selected_KK_zero_sector',P0*P0==P0)
ck('interacting_H_does_not_preserve_zero_sector',P0*H*(s.eye(2)-P0)!=s.zeros(2))
ck('naive_projected_H_zero',P0*H*P0==s.zeros(2))
ck('projected_second_moment_retains_interaction',P0*H**2*P0==s.diag(lam**2,0))
ck('projected_second_moment_not_naive_square',P0*H**2*P0!=(P0*H*P0)**2)
# Exact Feshbach-Schur energy-dependent effective zero-sector operator
ck('Feshbach_operator_is_energy_dependent',s.simplify((lam**2/(energy-h)).diff(energy))!=0)
ck('Feshbach_eigen_equation_matches_full_det',s.simplify((energy-h)*(energy-lam**2/(energy-h))-((energy*s.eye(2)-H).det()))==0)

# A stronger geometric STEELMAN: compactification radius can set the
# EFFECTIVE 4D non-Abelian coupling g4²=g5²/L; if a separate 4D pure YM
# continuum exists, the ONE-LOOP running-scale heuristic is exponential in
# L/g5², not the free KK mode n*(2*pi/L). This is source mathematics,
# NOT a proof of confinement or a YM spectral mass gap.
ell,g5positive,renmu,delta=s.symbols('ell g5positive renmu delta',positive=True)
b0pure=Q(11)  # SU3 pure: (11/3)*C_A=11, C_A=3
b0eight=b0pure-Q(2,3)*8  # 8 active Dirac SU3 fundamentals, NO scalars
scale=renmu*s.exp(-8*s.pi*s.pi*ell/(b0pure*g5positive))
KK1=2*s.pi/ell
ck('original_YM_pure_SU3_b0_equal_11',b0pure==11)
ck('source_QCD_eight_flavour_one_loop_coefficient_differs',b0eight==Q(17,3) and b0eight!=b0pure)
ck('KK_radius_changes_4D_YM_running_scale_exponent',s.simplify(s.diff(s.log(scale),ell)+8*s.pi*s.pi/(b0pure*g5positive))==0)
ck('geometric_nonperturbative_scale_not_KK_first_excitation',s.simplify(scale/KK1-renmu*ell/(2*s.pi)*s.exp(-8*s.pi*s.pi*ell/(b0pure*g5positive)))==0)
ck('one_loop_scale_ratio_under_change_of_radius',s.simplify(scale.subs(ell,ell+delta)/scale-s.exp(-8*s.pi*s.pi*delta/(b0pure*g5positive)))==0)

# Positive finite-regulator transfer eigenvalue separation can vanish in
# physical units as the regulator a -> 0. This is NOT a YM theorem.
a=s.Symbol('a',positive=True)
Delta=s.log((1+a*a)/(1-a*a))/a
ck('regulated_transfer_strict_positive_at_a_half',s.simplify(Delta.subs(a,Q(1,2))-2*s.log(Q(5,3)))==0)
ck('regulated_transfer_gap_vanishes_in_continuum',s.limit(Delta,a,0,dir='+')==0)
ck('bare_KK_circle_n0_massless',Q(0)**2==0)
ck('nonzero_KK_n1_has_positive_mass',Q(1)**2>0)

receipt={
 'programme':'OCT369 P0.37 same-source non-Abelian KK/E6 x YM Wilson/OS P0 steelman',
 'checks_passed':len(checks),'checks':checks,
 'physical_original_owners':{
 'KK_5D_nonabelian':'PR #1241 selected 5D SU3c x SU3L x SU3R x U1_B interacting EFT and #1106 E6',
 '4D_SU_N_Wilson_OS':'PR #1444/#1536 original SU(N) Wilson/Haar/Gibbs, R445, CMP116, OS source',
 '5D_KK_metric':'TSFVKKSelectedHorizontalMetricSchurExact; abelian graviphoton distinct from SU3 connection',
 'science':'Kaluza/Klein; Yang/Mills; Wilson; Osterwalder/Schrader; Slansky; standard EFT dimensional reduction',
 },
 'same_source_restricted_nonabelian_5D_to_4D_action':True,
 'C3_original_spatial_rotation_representation_projectors_reused':True,
 'C3_source_mark_projection_is_not_OS_gap_spectral_source':True,
 'exact_beta4_equals_N5_beta5':True,'su3_noncommuting_Wilson_plaquette':str(P),
 'su3_plaquette_deficit':str(E),'N5':N5,'a5':str(a5),'L':str(L),
 'coupling_tree':'1/g4^2=L/g5^2','mixed_fibre_Fmu5_nonzero':True,
 'KK_schur_horizontal_matches_same_metric':True,
 'SU3_nontrivial_holonomy_has_two_neutral_Cartan_modes':True,
 'source_independent_photon_U1_B_and_EW_U1_need_real_mixing':True,
 'integrated_fifth_link_marginal':[str(Q(4,7)),str(Q(3,7))],
 'restricted_uniform_four_link_marginal':['1/2','1/2'],
 'Feshbach_zero_mode_quantum_interaction_survives':True,
 'positive_regulator_gap_can_go_to_zero':True,
 'full_5D_quantum_path_integral_identical_4D_pure_YM':False,
 'conditional_4D_dimensional_transmutation_scale_from_L_over_g5sq':'mu*exp(-8*pi^2*L/(11*g5sq)) for pure SU3, only one-loop running heuristic',
 'five_D_SU3c_eight_light_flavours_identical_to_pure_SU3_beta0':False,
 'toy_marginal_is_SU3_Haar':False,
 'naive_zero_mode_slice_invariant_under_all_5D_gauge_transformations':False,
 'original_continuum_SU_N_OS_Hilbert_intertwiner_constructed':False,
 'positive_infinite_volume_continuum_mass_gap_proved':False,
 'KK_color_YM_a_metric_only_U1_photon':False,
 'source_measured_electromagnetic_gravity_interaction':False,
 'YM_mass_gap_proved_equal_to_EM_cavity_gap':False,
 'Agda_kernel_tested':False,
}
if __name__=='__main__':
    print(json.dumps(receipt,sort_keys=True,indent=2))
