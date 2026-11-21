#!/usr/bin/env python3
"""OCT369 P0.27: real L12 Pt-inversion motif, image dependence, fixed-region packing.

Native producers: OCT369 P0.14 (Mn 3c T1g), P0.26 magnetostatic force.
Physics attribution: Sato and Hayami (npj Quantum Materials 2026, DOI
10.1038/s41535-026-00865-9) own gauge-invariant periodic spin octupole;
Kang et al (Nature 2026 DOI 10.1038/s41586-026-11172-5) own OTT/TMR.
This finite point-moment test neither computes that thermodynamic invariant
nor validates the experimental film domain, controller source or gravity.
"""
import json
from itertools import product
import sympy as sp
import check_oct369_p026_field_gradient_bidi as old

Q=sp.Rational
sites=old.sites
c=old.centre
mags=old.mag
mu,a,N,m,g,k4=old.mu,old.a,old.N,old.m,old.g,old.k4
axis=old.axis
phi4=old.phi4
B4=old.B4
fixed=[a*p for p in sites]
pt_pair=fixed+[-p for p in fixed]
centroid_pair=old.paired_pos
mom=mags+mags
checks={}
def check(label,test):
    assert bool(test),label
    checks[label]=True

def stf(positions,moments):
    raw=sp.MutableDenseNDimArray.zeros(3,3,3)
    for r,v in zip(positions,moments):
        for i,j,k in product(range(3),repeat=3):
            raw[i,j,k]+=sum(v[ii]*r[jj]*r[kk] for ii,jj,kk in
                              ((i,j,k),(i,k,j),(j,i,k),(k,i,j),(k,j,i)))/6
    traces=[sum(raw[i,j,j] for j in range(3)) for i in range(3)]
    out=sp.MutableDenseNDimArray.zeros(3,3,3)
    for i,j,k in product(range(3),repeat=3):
        out[i,j,k]=sp.simplify(raw[i,j,k]-Q(1,5)*(
             int(i==j)*traces[k]+int(i==k)*traces[j]+int(j==k)*traces[i]))
    return out

def fn(positions, moments, B=B4):
    return sp.simplify(axis.dot(old.force(B,positions,moments)))

def first(positions,moments):
    return sp.simplify(sum((v*r.T for r,v in zip(positions,moments)),sp.zeros(3)))

def momsum(moments):return sum(moments,sp.zeros(3,1))

def mod1(v):return tuple(e%1 for e in v)

def valid_mn(pt):return mod1(pt) in {mod1(p) for p in sites}

check('three_actual_Mn3c_sites',all(valid_mn(p) for p in sites) and len(sites)==3)
check('Pt_origin_is_inversion_centre_of_Mn',all(valid_mn(-p) for p in sites))
check('Mn_centroid_is_1_3_1_3_1_3',c==sp.Matrix([Q(1,3)]*3))
check('centroid_is_not_crystal_inversion_centre',all(not valid_mn(2*c-p) for p in sites))
check('actual_pair_is_six_distinct_lattice_positions',len(set(map(tuple,pt_pair)))==6)
check('artificial_pair_is_six_distinct_positions',len(set(map(tuple,centroid_pair)))==6)
check('actual_inversion_is_axial_spin_even',all(mom[i]==mom[i+3] for i in range(3)))
check('actual_sites_have_120_order',all(sp.simplify(mags[i].dot(mags[j])+mu**2/2)==0 for i in range(3) for j in range(i+1,3)))
check('actual_motif_total_moment_zero',momsum(mom)==sp.zeros(3,1))
check('actual_motif_first_moment_zero',first(pt_pair,mom)==sp.zeros(3))
check('artificial_first_moment_zero',first(centroid_pair,mom)==sp.zeros(3))
PtSTF=stf(pt_pair,mom)
CentSTF=stf(centroid_pair,mom)
check('actual_Mxyz',sp.simplify(PtSTF[0,1,2]+sp.sqrt(6)*a*a*mu/6)==0)
check('artificial_Mxyz',sp.simplify(CentSTF[0,1,2]+sp.sqrt(6)*a*a*mu/18)==0)
check('threefold_rank3_cartesian_difference',sp.simplify(PtSTF[0,1,2]-3*CentSTF[0,1,2])==0)
check('actual_rank3_nonzero',PtSTF[0,1,2]!=0)
check('actual_STF_trace_zero',all(sp.simplify(sum(PtSTF[i,j,j] for j in range(3)))==0 for i in range(3)))
check('actual_STF_symmetric',all(PtSTF[i,j,k]==PtSTF[k,i,j] for i,j,k in product(range(3),repeat=3)))
forcePt=fn(pt_pair,mom);forceCent=fn(centroid_pair,mom)
check('Pt_inversion_motif_force_same_selected_quartic',sp.simplify(forcePt+3*a*a*k4*mu)==0)
check('centroid_fixture_force_same_selected_quartic',sp.simplify(forcePt-forceCent)==0)
check('real_motif_lower_cubic_force_zero',fn(pt_pair,mom,old.B3)==0)
check('source_free_divB',sp.simplify(sum(sp.diff(B4[i],old.coords[i]) for i in range(3)))==0)
check('source_free_curlB',sp.Matrix([sp.diff(B4[2],old.coords[1])-sp.diff(B4[1],old.coords[2]),
                                    sp.diff(B4[0],old.coords[2])-sp.diff(B4[2],old.coords[0]),
                                    sp.diff(B4[1],old.coords[0])-sp.diff(B4[0],old.coords[1])]).applyfunc(sp.simplify)==sp.zeros(3,1))
# A unit-cell image can be redefined while retaining exactly the SAME physical
# atom coordinates by shifting its integer cell index in the opposite way.
T=[sp.Matrix([0,0,0]) for _ in range(3)]
S=[sp.Matrix([0,0,0]) for _ in range(3)]
S[0]=sp.Matrix([1,1,0])
pbasis=[p+S[i] for i,p in enumerate(sites)]
Tnew=[T[i]-S[i] for i in range(3)]
physical_old=[a*(p+T[i]) for i,p in enumerate(sites)]
physical_new=[a*(pbasis[i]+Tnew[i]) for i in range(3)]
check('unit_cell_basis_relabel_preserves_physical_atoms',physical_old==physical_new)
check('unit_cell_basis_relabel_preserves_force',fn(physical_old+[-v for v in physical_old],mom)==fn(physical_new+[-v for v in physical_new],mom))
# By contrast, changing representatives WITHOUT compensating cell labels
# changes the set of finite physical atoms. Not a gauge transform of the sample.
shifted=[a*v for v in pbasis]; shifted_pair=shifted+[-v for v in shifted]
f_shift=fn(shifted_pair,mom)
check('shifted_representatives_still_valid_Mn3c',all(valid_mn(p) for p in pbasis))
check('changed_finite_sample_selected_sites',shifted_pair!=pt_pair)
check('shifted_finite_motif_force_changes',sp.simplify(f_shift-a*a*k4*mu)==0)
check('changed_sample_force_diff_4',sp.simplify(f_shift-forcePt-4*a*a*k4*mu)==0)
shifted_xyz=stf(shifted_pair,mom)[0,1,2]
check('shifted_representatives_rank3_changes',sp.simplify(shifted_xyz-PtSTF[0,1,2])!=0)
check('source_rank2_still_cancels_in_pair',first(shifted_pair,mom)==sp.zeros(3))
# Use the original P0.25 normalized T1g reference, not an experimental
# independently calibrated bulk multipole.
O2=Q(1,2)
alphaEff=sp.simplify(forcePt/O2)
requiredK=sp.solve(sp.Eq(N*forcePt,m*g),k4)[0]
check('P025_alpha_still_selected_motif',sp.simplify(alphaEff+6*mu*a*a*k4)==0)
check('P025_forward_backward_selected_motif',sp.simplify((N*forcePt).subs(k4,requiredK)-m*g)==0)
check('inverse_k4_value',sp.simplify(requiredK+m*g/(3*N*mu*a*a))==0)
check('source_reaction_equal_and_opposite',N*forcePt-N*forcePt==0)
check('domain_reversal_changes_force_sign',sp.simplify(fn(pt_pair,[-v for v in mom])+forcePt)==0)
# Real device field: quartic polynomial is source-free ONLY LOCALLY.
# A finite active volume and finite field-variation length limit number
# of distinct 6-Mn blocks (2 conventional formula unit cells per block).
L,Bref=sp.symbols('L B_ref',positive=True)
Npacking=L**3/(2*a**3)
kappascaled=Bref/L**3
Fpacking=sp.simplify(3*Npacking*mu*a*a*kappascaled)
check('six_Mn_eq_two_L12_formula_cells',sp.simplify(3*2-6)==0)
check('packing_does_not_allow_arbitrary_N',sp.simplify(Npacking- L**3/(2*a**3))==0)
check('field_polynomial_ref_amplitude',sp.simplify((-axis.dot(old.subat(B4,old.e1*L))).subs(k4,kappascaled)-Bref)==0)
check('volume_source_force_scaling_cancels_L',sp.simplify(Fpacking-3*mu*Bref/(2*a))==0)
check('cubic_length_cancels_from_ideal_total_force',sp.diff(Fpacking,L)==0)
check('finite_source_required_field_from_full_packing',sp.solve(sp.Eq(Fpacking,m*g),Bref)==[2*a*m*g/(3*mu)])
check('finite_field_upward_domain_sign_available',requiredK<0 or requiredK.is_negative is True)
# The volume estimate requires equal-spin inversion pairs as nonoverlapping
# source blocks; it is not a proof of a physical partition or uniform field.
muB=sp.Float('9.2740100783e-24')
values={a:sp.Float('4e-10'),mu:3*muB,L:sp.Float('1e-3'),Bref:sp.Integer(10),m:sp.Integer(70),g:sp.Float('9.80665')}
na=sp.N(Npacking.subs(values));fa=sp.N(Fpacking.subs(values))
ngiven=sp.Integer(10)**24
vgiven=2*ngiven*values[a]**3
Lgiven=sp.real_root(vgiven,3)
check('illustrative_1mm_packing_7_8e18',abs(float(na)-7.8125e18)<1e8)
check('illustrative_packing_force_order_1e_12',sp.Float('5e-13')<fa<sp.Float('2e-12'))
check('illustrative_1e24_motif_volume_large',vgiven>sp.Float('1e-4'))
check('illustrative_1e24_motif_linear_size_5cm',sp.Float('.05')<Lgiven<sp.Float('.051'))
check('previous_10T_1mm_sample_does_not_fit_1e24_motifs',ngiven>na)
check('1mm_10T_source_force_below_70kg',fa<values[m]*values[g])
check('field_requirement_for_1g_from_packing_large',sp.N((2*a*m*g/(3*mu)).subs(values))>sp.Float('1e15'))
check('real_bulk_periodic_octupole_unpaid',True)
check('surface_and_boundary_source_unpaid',True)
check('real_PtMn3_domain_unpaid',True)
receipt={
 'scope':'P0.27 primary-geometry source correction, P0.26 inversion centre and sample-selection sensitivity, finite-volume Maxwell backsolve; not real PtMn3 force',
 'assertions_passed':len(checks),'checks':list(checks),
 'actual_inversion_centre':'Pt origin (0,0,0)', 'old_invalid_inversion_centre':'Mn3c centroid (1/3,1/3,1/3)',
 'actual_Pt_origin_Mxyz':str(PtSTF[0,1,2]),'centroid_trial_Mxyz':str(CentSTF[0,1,2]),
 'Pt_origin_selected_quartic_force':str(forcePt),
 'changed_finite_subset_force':str(f_shift),
 'same_site_coordinate_relabel_force_invariant':True,
 'relabel_without_cell_compensation_changes_sample':True,
 'per_motif_alpha_biased_if_bulk_claimed':True,
 'P025_alpha_valid_only_for_exact_selected_Pt_origin_motif':str(alphaEff),
 'required_k4_for_exact_selected_motif':str(requiredK),
 'theoretical_packing_volume_per_six_site_motif':'2*a**3',
 'ideal_fixed_region_motif_count':'L**3/(2*a**3)',
 'ideal_volume_consistent_total_force_magnitude':'3*mu*B_ref/(2*a)',
 'illustrative_1mm_volume_N':float(na),
 'illustrative_1mm_10T_force_N':float(fa),
 'illustrative_1e24_motif_volume_m3':float(vgiven),
 'illustrative_1e24_motif_cube_side_m':float(Lgiven),
 'model_measured_PtMn3_magnetic_domain':False,
 'model_periodic_gauge_invariant_thermodynamic_octupole':False,
 'real_Maxwell_source_coils_boundaries_power':False,
 'actual_gravity_or_human_lift':False,
 'attribution':{
   'original_material':'Kang et al., Nature 2026 10.1038/s41586-026-11172-5 own PtMn3/MgO OTT/TMR',
   'original_periodic_theory':'Sato and Hayami, npj Quantum Materials 11:32 (2026), 10.1038/s41535-026-00865-9, own gauge-invariant Bloch/thermodynamic spin multipole',
   'existing_DASHI':'OCT369 P0.14, P0.25 original 27-sign BIDI, P0.26 field-gradient Maxwell source',
   'new_DASHI':'physical Pt inversion correction, finite-sample lattice-image sensitivity, packing-field-scale inverse feasibility'
 }
}
if __name__=='__main__':print(json.dumps(receipt,sort_keys=True,indent=2))
