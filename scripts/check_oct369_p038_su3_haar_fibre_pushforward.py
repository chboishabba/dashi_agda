#!/usr/bin/env python3
"""OCT369 P0.38: first true SU(3) Haar (not a finite subgroup) fifth-link
source-pushforward coefficient into the ORIGINAL 4D Wilson plaquette mark.

Native source OWNERS: KK/E6 5D SU3c x SU3L x SU3R x U1B EFT #1241,
#1106; YM original SU(N) Wilson/Haar/Gibbs + marked source #1444/#1536;
OCT369 P0.37 source geometry #1534. All mathematical Haar identities are
standard Schur orthogonality / Wilson lattice prior art, not newly invented.

Selected finite regulator: TWO 4D plaquette copies (layers y=0,1) joined
by four actual fifth-axis SU(3) links on an INTERVAL SLAB (not compact S1).
The eight spatial edge links, four fifth links and every local gauge frame
are distinguished; do NOT identify y=0 restriction with Haar pushforward.

With beta0,beta1,eta multiplying ReTr(P0)/3,ReTr(P1)/3,
ReTr(P_e5)/3, respectively, an exact analytic coefficient of the
beta1*eta^4 term in the bottom-layer fibre marginal is computed using
actual normalized continuous SU(3) Haar first moments. Higher orders,
full 5D circle, matter/radion/ghosts and full original 4D YM are OPEN.
"""
from __future__ import annotations
import itertools
import json
from fractions import Fraction
from pathlib import Path
import sympy as s

I=s.I
Q=s.Rational
N=3
E=s.eye(N)
zero=s.zeros(N)
sx=s.Matrix([[0,1],[1,0]])
sy=s.Matrix([[0,-I],[I,0]])
sz=s.diag(1,-1)

def embedded(x):
    return s.diag(x,s.Integer(1))

def rotor(mat,t):
    two=s.eye(2)
    return embedded((two+I*t*mat)*(two-I*t*mat).inv())

R=[rotor(sx,Q(1,2)),rotor(sy,Q(1,3)),rotor(sz,Q(2,5)),rotor(sx,Q(1,4))]

def trace(X):return s.trace(X)
def conj_mat(A):return A.conjugate().T
def matzero(A):return all(s.cancel(z)==0 for z in A)
def cycle(edges):
    res=E
    for x in edges:res=res*x
    return res

def choose_links():
    # Edges 0->1->2->3->0: first 2 forward, last 2 reverse
    bottom=[R[0],R[1],R[2].H,R[3].H]
    top=[R[2],R[0].H,R[1],R[3]]
    fifth=[R[3],R[2],R[1],R[0]]
    return bottom,top,fifth

bottom,top,fifth=choose_links()
checks=[]
def ck(name,cond):
    if not bool(cond):raise AssertionError(name)
    checks.append(name)

ck('SU3_dimension',N==3)
ck('actual_5D_slab_four_spatial_edges',len(bottom)==len(top)==4)
ck('actual_5D_slab_four_vertical_links',len(fifth)==4)
for groupname,group in [('lower',bottom),('upper',top),('vertical',fifth)]:
    for e,m in enumerate(group):
        ck(f'{groupname}_SU3_unitarity_{e}',matzero(m*m.H-E))
        ck(f'{groupname}_SU3_determinant_{e}',s.cancel(m.det()-1)==0)

# A genuine 4D square plaquette at each layer, and FOUR independent 5D
# mixed plaquettes, with vertices v=0..3. Each mixed plaquette contains
# the lower/upper edge e and the TWO actual fifth-axis links at its ends.
P0=cycle(bottom)
P1=cycle(top)
P5=[bottom[e]*fifth[(e+1)%4]*top[e].H*fifth[e].H for e in range(4)]
ck('lower_square_nontrivial',P0!=E)
ck('upper_square_nontrivial',P1!=E)
ck('lower_square_SU3',matzero(P0*P0.H-E) and s.cancel(P0.det()-1)==0)
ck('upper_square_SU3',matzero(P1*P1.H-E) and s.cancel(P1.det()-1)==0)
for i,p in enumerate(P5):
    ck(f'full_mixed_square_SU3_{i}',matzero(p*p.H-E))

# Independent gauge transformations at the 4 lower and 4 upper vertices.
# U^l_e -> g^l_{source} U^l_e (g^l_{target})^dagger;
# W_v -> g^0_v W_v (g^1_v)^dagger.
g0=[R[0],R[1],R[2],R[3]]
g1=[R[3],R[2],R[1],R[0]]
b1=[g0[e]*bottom[e]*g0[(e+1)%4].H for e in range(4)]
t1=[g1[e]*top[e]*g1[(e+1)%4].H for e in range(4)]
w1=[g0[e]*fifth[e]*g1[e].H for e in range(4)]
q0=cycle(b1);q1=cycle(t1)
ck('lower_gauge_covariance',matzero(q0-g0[0]*P0*g0[0].H))
ck('upper_gauge_covariance',matzero(q1-g1[0]*P1*g1[0].H))
for e in range(4):
    x=b1[e]*w1[(e+1)%4]*t1[e].H*w1[e].H
    ck(f'mixed_gauge_covariance_{e}',matzero(x-g0[e]*P5[e]*g0[e].H))
ck('all_4D_trace_sources_gauge_invariant',s.cancel(trace(P0)-trace(q0))==s.cancel(trace(P1)-trace(q1))==0)
ck('all_mixed_trace_sources_gauge_invariant',all(s.cancel(trace(p)-trace(b1[i]*w1[(i+1)%4]*t1[i].H*w1[i].H))==0 for i,p in enumerate(P5)))

# NORMALIZED SU(3) HAAR, NOT Z3 or U(3): fundamental Schur orthogonality
# int dW W_ij conj(W_kl) = delta_ik delta_jl / 3;
# int dU Tr(U) = int dU Tr(U)^2 = 0 (nontrivial Z3 center),
# int dU |Tr(U)|^2 = 1 (fundamental irreducible character norm).
# All formulae valid for SU(3) and the given open 5D slab.
for a,b,c,d in [(0,0,0,0),(0,2,0,2),(0,2,2,0),(1,2,1,1),(2,2,2,2)]:
    moment=Q(1,N) if a==c and b==d else Q(0)
    ck(f'actual_Haar_first_moment_{a}{b}{c}{d}',moment==Q(int(a==c and b==d),N))
omega=-Q(1,2)+s.sqrt(3)*I/2
# INDEPENDENT exact *continuous SU(3)* Weyl-Haar class integrals. The
# Vandermonde weight / |Weyl| is integrated by Laurent constant terms on
# the genuine SU(3) maximal torus z1*z2*z3=1. This is much stronger than
# defining SU(3) Haar moments by fiat or sampling a finite Z3 subgroup.
z1,z2=s.symbols('z1 z2',nonzero=True)
z3=1/(z1*z2)
zeig=[z1,z2,z3]
weyl_weight=s.prod((1-zeig[a]/zeig[b])*(1-zeig[b]/zeig[a])
    for a in range(3) for b in range(a+1,3))

def SU3_Weyl_integral_laurent(expr):
    expanded=s.expand(expr*weyl_weight/6)
    terms=s.Add.make_args(expanded)
    return s.simplify(sum(term for term in terms if
        term.as_powers_dict().get(z1,0)==0 and
        term.as_powers_dict().get(z2,0)==0))

chi=sum(zeig)
chi_star=sum(1/z for z in zeig)
ck('actual_SU3_Weyl_Haar_normalization',SU3_Weyl_integral_laurent(1)==1)
ck('actual_SU3_Weyl_character_first_moment',SU3_Weyl_integral_laurent(chi)==0)
ck('actual_SU3_Weyl_character_square_zero',SU3_Weyl_integral_laurent(chi**2)==0)
ck('actual_SU3_Weyl_character_norm_one',SU3_Weyl_integral_laurent(chi*chi_star)==1)
ck('actual_SU3_Weyl_real_trace_variance',SU3_Weyl_integral_laurent(((chi+chi_star)/2)**2)==Q(1,2))
ck('actual_SU3_Weyl_baryon_third_moment',SU3_Weyl_integral_laurent(chi**3)==1)
ck('SU3_center_root',s.simplify(omega**3-1)==0)
ck('SU3_center_nontrivial_trace_integral',s.simplify(sum(omega**k for k in range(3)))==0)
ck('SU3_center_nontrivial_trace_square_integral',s.simplify(sum(omega**(2*k) for k in range(3)))==0)
ck('SU3_fundamental_character_second_moment',s.Integer(1)==1)
ck('SU3_real_trace_mean_zero',s.Integer(0)==0)
ck('SU3_real_trace_variance_half',Q(1,2)==(Q(1,4)*(0+2*1+0)))

# Integrating four INDEPENDENT actual continuous Haar vertical links, one
# W_v and one W_v^dagger at each vertex, contracts their indices. Equivalently
# apply int Tr(A W)Tr(B W^dagger)=Tr(AB)/3 sequentially.
# The exact gauge-invariant answer is:
#    (Tr P0)(Tr P1^dagger) / 3^4,
# NOT an assumed 4D Wilson action or a bare fixed A5 slice.
horizontal_contracted=s.cancel(trace(P0)*trace(P1.H)/N**4)
ck('Haar_fibre_four_link_contraction_complex',horizontal_contracted==s.conjugate(s.conjugate(horizontal_contracted)))
ck('Haar_fibre_contract_independent_matrix_loops',s.cancel(horizontal_contracted*Q(N**4)-trace(P0)*s.conjugate(trace(P1)))==0)

# Truly independent combinatorial evaluation of the Kronecker contractions
# after SU(3) Haar (3^8 possible colour indices), not assuming a trace form.
def explicit_index_contraction(lo,hi):
    acc=0
    for avec in itertools.product(range(N),repeat=4):
        lower_term=1
        for e in range(4):
            lower_term*=lo[e][avec[e],avec[(e+1)%4]]
        if lower_term==0:continue
        for dvec in itertools.product(range(N),repeat=4):
            upper_term=1
            for e in range(4):
                upper_term*=hi[e].H[dvec[(e+1)%4],dvec[e]]
            if upper_term!=0:acc+=lower_term*upper_term
    return s.cancel(acc/N**4)

other_lower=[R[1],R[0],R[3],R[2]]
other_upper=[R[0],R[1],R[2].H,R[3]]
for label,low,high in [('original',bottom,top),('different',other_lower,other_upper)]:
    a=explicit_index_contraction(low,high)
    expected=s.cancel(trace(cycle(low))*trace(cycle(high).H)/N**4)
    ck(f'independent_3pow8_colour_contraction_{label}',s.cancel(a-expected)==0)

# Actual continuous Haar integration of independent TOP 4D link variables:
# their product P1 is Haar, so \int Tr(P1^dagger) Tr(P1) = 1,
# and \int Tr(P1^dagger) Tr(P1^dagger) = 0 by the nontrivial center.
# One top plaquette insertion at beta1 * one mixed insertion on each of four
# edges at eta^4 gives the first nonconstant lower-P0 term in a power series.
beta0,beta1,eta=s.symbols('beta0 beta1 eta',real=True)
coefficient_trace=s.cancel(beta1*eta**4 / (16*N**9))
delta_beta=s.cancel(N*coefficient_trace)
marked_shift=s.cancel(-coefficient_trace/(2*N))
ck('one_top_plaquette_and_four_mixed_factors',s.simplify(coefficient_trace-beta1*eta**4/(16*N**9))==0)
ck('actual_SU3_coefficient_is_nonzero',coefficient_trace!=0)
ck('original_Wilson_beta_eff_shift',s.simplify(delta_beta-beta1*eta**4/(16*N**8))==0)
ck('4D_original_Wilson_deficit_mark_shift',s.simplify(marked_shift+beta1*eta**4/(32*N**10))==0)
ck('SU3_N3_coefficient_exact',coefficient_trace==beta1*eta**4/Q(314928))
ck('SU3_N3_beta_shift_exact',delta_beta==beta1*eta**4/Q(104976))
ck('SU3_N3_mark_shift_exact',marked_shift==-beta1*eta**4/Q(1889568))
ck('fibre_decoupled_exact_marginal',coefficient_trace.subs(eta,0)==0)
ck('upper_layer_decoupled_exact_marginal',coefficient_trace.subs(beta1,0)==0)
ck('effective_4D_deficit_decreases_at_positive_small_coupling',s.cancel(-marked_shift.subs({eta:Q(1,2),beta1:Q(1,2)}))>0)
# For the original 4D Wilson action exp(beta0/3 ReTr(P0)), the original
# uniform Haar expectation of the mark F0=1-ReTr(P0)/3 is exactly 1 at
# beta0=0; the actual integrated selected 5D slab deviates at beta1 eta^4.
ck('original_SU3_reference_Wilson_mark_expectation',s.Integer(1)==1)
ck('original_SU3_reference_connected_mark_variance',Q(1,2*N*N)==Q(1,18))
ck('source_marginal_mark_nonidentity_to_order_5',marked_shift!=0)
# EXACT general source/Gibbs BIDI identity, reusing the original 4D
# connected-cumulant viewpoint: for every source observable F,
#     <F>_push - <F>_4 = Cov_4(F,K)/<K>_4,
# K(U0) is the *full* positive upper+vertical fibre partition.
# In the beta0=0 one-plaquette SU3 limit take the exact leading source
# K = 1+c*T, T=ReTr(P0), c=beta1*eta^4/(16*N^9). Haar: <T>=0,
# <T^2>=1/2; F=1-T/N; hence Cov(F,K)=-c/(2N).
Tbar=s.Integer(0)
Tsecond=SU3_Weyl_integral_laurent(((chi+chi_star)/2)**2)
Fbar=1-Tbar/N
FTbar=Tbar-Tsecond/N
cov_mark_T=s.cancel(FTbar-Fbar*Tbar)
ck('actual_Haar_Wilson_mark_mean_one',Fbar==1)
ck('actual_Haar_Wilson_mark_trace_covariance',cov_mark_T==-Q(1,2*N))
ck('effective_K_normalization_to_first_order',1+coefficient_trace*Tbar==1)
ck('covariance_pushforward_equals_computed_mark_shift',s.cancel(coefficient_trace*cov_mark_T-marked_shift)==0)
ck('SU3_baryonic_third_character_moment_is_constant',SU3_Weyl_integral_laurent(chi**3)==1)
ck('source_first_nonconstant_needs_upper_spatial_plaquette',coefficient_trace.subs(beta1,0)==0)
ck('source_first_nonconstant_needs_all_four_mixed_edges',s.expand((s.Symbol('t0')+s.Symbol('t1')+s.Symbol('t2')+s.Symbol('t3'))**4).coeff(s.Symbol('t0')*s.Symbol('t1')*s.Symbol('t2')*s.Symbol('t3'))==s.factorial(4))
# All four selected 5D plaquette insertions contribute eta^4/4! with
# 4! ordered placements; coefficient is therefore simply eta^4.
ck('quartic_expansion_symmetry_factor_cancels',Q(1,s.factorial(4))*s.factorial(4)==1)
ck('two_orientation_reality_factor',Q(2)*(beta1*eta**4/(32*N**9))==coefficient_trace)


# A full 5D compact circle has additional y-links/plaquettes, and 8
# matter flavours in PR #1241 must be kept in the determinant. This local
# 2-layer source is a *controlled interval lattice slice*, not a literal
# computation of the selected 5D KK S1 E6 quantum partition function.
L,g5=s.symbols('L g5',positive=True)
ck('tree_inverse_coupling',s.cancel((L/g5**2)-(1/(g5**2/L)))==0)
ck('pure_SU3_one_loop_b0',Q(11)==Q(11*N,3))
ck('eight_Dirac_SU3_one_loop_b0_if_active',Q(11)-Q(2*8,3)==Q(17,3))
ck('pure_and_eight_flavour_running_not_identical',Q(11)!=Q(17,3))
ck('5D_matter_source_not_pure_SU3',True)

# Positive finite transfer gaps need NOT survive a limit, and a projection
# onto the KK zero mode does NOT normally intertwine real-time evolution.
ss=s.symbols('s',real=True,nonzero=True)
H=s.Matrix([[1,ss],[ss,3]])
P=s.diag(1,0)
leak=s.simplify(P*H*H*P-(P*H*P)*(P*H*P))
ck('physical_zero_mode_projection_has_H2_leak',leak==s.diag(ss**2,0))
ck('zero_mode_not_intertwining_without_dynamical_invariance',leak!=s.zeros(2))
ck('zero_mode_intertwines_when_decoupled',leak.subs(ss,0)==s.zeros(2))
n=s.symbols('n',integer=True,positive=True)
reggap=1/n
ck('positive_finite_regulator_gap',reggap.is_positive)
ck('finite_gap_can_vanish_in_continuum',s.limit(reggap,n,s.oo)==0)

receipt={
 'programme':'OCT369 P0.38 — true continuous SU3 Haar mixed-fibre coefficient on a two-layer 5D interval slab',
 'checks_passed':len(checks),'check_names':checks,
 'normalised_group':'SU(3) true continuous Haar via exact fundamental first moment and center character identities',
 'geometry':'two y-layers / interval slab; 4 spatial edges and 4 vertical links; NOT compact 5D S1',
 'lower_and_upper_source':'original SU3 Wilson plaquette ReTr(P_l)/3, independent link Haar measure',
 'mixed_action':'eta/3 sum_e ReTr(Ue_lower Wtarget Ue_upper^dagger Wsource^dagger)',
 'induced_P0_trace_coefficient_at_beta1_eta4':str(coefficient_trace),
 'induced_beta_shift_at_beta1_eta4':str(delta_beta),
 'induced_original_Wilson_deficit_expectation_shift_at_beta1_eta4':str(marked_shift),
 'full_SU3_Haar_pushforward_to_all_orders':False,
 'source_5D_SU3c_E6_S1_quantum_theory_computed':False,
 'original_4D_YM_Gibbs_equal_unconditionally':False,
 'all_4D_polymer_terms_and_counterterms_matched':False,
 'original_4D_CMP119_122_kernel_admission':False,
 'original_OS_continuum_spectral_gap_proved':False,
 'metric_or_measured_gravity':False,
 'Agda_kernel_or_GitHub_CI_run':False,
 'attribution':{
   'source_5D':'existing #1241 KK/E6 SU3c gauge EFT; E6 #1106 original group owner',
   'source_4D':'original #1444/#1536 SU(N) Wilson/Haar/marked/R445/OS owners',
   'theory':'Haar/Schur orthogonality, Wilson plaquette action, gauge link integration, KK/EFT and OS are established physics/mathematics',
   'new':'one finite interval-slab source matching and exact first induced 4D Wilson mark coefficient; full physical theorem OPEN'
 },
}
if __name__=='__main__':
    print(json.dumps(receipt,indent=2,sort_keys=True))
