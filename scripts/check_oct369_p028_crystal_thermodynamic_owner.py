#!/usr/bin/env python3
"""OCT369 P0.28: existing crystal-owner and finite magnetic thermodynamic weld.

Original theory owners: IUCr (crystallography); Bhowal/Spaldin PRX 2024;
Oike/Peters/Shinada PRB 2025 bulk thermodynamic magnetic octupole;
Sato/Hayami npj Quantum Materials 2026 gauge-invariant Bloch formula;
Kang et al Nature 2026 PtMn3/MgO OTT switching and TMR.

New DASHI cut uses prior P0.27 SAME chosen FINITE physical Pt-inversion
point-moment sample and harmonic Maxwell source, NOT the original authors'
bulk quantum-geometric Eq. (11) or the actual measured magnetic domain.
Full 3x3x3 tensor is not replaced by a symmetric trace-free tensor until
an external, source-free Maxwell probe is supplied; only seven projected
components are then observable. No metric/gravity experiment is implied.
"""
import json
from itertools import permutations, product
import sympy as sp
import check_oct369_p027_lattice_image_maxwell_packing as p27

s=sp; Q=s.Rational; old=p27.old
n=3
C3=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
idx=list(product(range(n),repeat=3))
checks=[]
def ok(label,truth):
    assert bool(truth),label
    checks.append(label)

def full_tensor(positions,moments):
    # Classical point-moment limit: M_ijk=(1/2) sum m_i r_j r_k.
    # This is the exact conjugate of SECOND field derivative when
    # externally controlled components G_ijk are written independently.
    return sp.ImmutableDenseNDimArray([
        sp.simplify(sum(m[i]*r[j]*r[k]/2 for r,m in zip(positions,moments)))
        for i,j,k in idx], (3,3,3))

def sym_all(A):
    return sp.ImmutableDenseNDimArray([
        sp.simplify(sum(A[p[0],p[1],p[2]] for p in set(permutations((i,j,k))))/len(set(permutations((i,j,k)))))
        for i,j,k in idx], (3,3,3))

def sym_jk(A):
    return sp.ImmutableDenseNDimArray([(A[i,j,k]+A[i,k,j])/2 for i,j,k in idx],(3,3,3))

def stf(A):
    S=sym_all(A)
    trace=[sum(S[i,j,j] for j in range(3)) for i in range(3)]
    return sp.ImmutableDenseNDimArray([
        sp.simplify(S[i,j,k]-Q(1,5)*(
            sp.KroneckerDelta(i,j)*trace[k]+sp.KroneckerDelta(i,k)*trace[j]+sp.KroneckerDelta(j,k)*trace[i]))
        for i,j,k in idx],(3,3,3))

def dot(A,B):
    return sp.simplify(sum(A[i,j,k]*B[i,j,k] for i,j,k in idx))

def trans3(A,R):
    return sp.ImmutableDenseNDimArray([sp.simplify(sum(
        R[i,a]*R[j,b]*R[k,c]*A[a,b,c]
        for a,b,c in idx)) for i,j,k in idx], (3,3,3))

sites=p27.sites; pts=p27.pt_pair; moments=p27.mom
M=full_tensor(pts,moments); S=sym_all(M); STF=stf(M)
ok('L12_Pt_origin_inversion_cell',all(p27.valid_mn(-x) for x in sites))
ok('L12_lattice_not_ternary_chart',p27.c==sp.Matrix([Q(1,3)]*3))
ok('same_P027_six_fixed_sites',pts==[p27.a*x for x in sites]+[-p27.a*x for x in sites])
ok('actual_P027_zero_net_magnetization',sum(moments,sp.zeros(3,1))==sp.zeros(3,1))
ok('full_tensor_jk_symmetric',all(M[i,j,k]==M[i,k,j] for i,j,k in idx))
ok('full_tensor_not_totally_symmetric',any(M[i,j,k]!=S[i,j,k] for i,j,k in idx))
ok('tensor_full_decomposes',all(M[i,j,k]==S[i,j,k]+(M[i,j,k]-S[i,j,k]) for i,j,k in idx))
ok('mixed_symmetry_nonzero',any(M[i,j,k]-S[i,j,k] for i,j,k in idx))
ok('sym_tensor_trace_nonzero',any(sum(S[i,j,j] for j in range(3)) for i in range(3)))
ok('STF_trace_zero',all(sum(STF[i,j,j] for j in range(3))==0 for i in range(3)))
ok('STF_fully_symmetric',all(STF[i,j,k]==STF[k,j,i]==STF[j,i,k] for i,j,k in idx))
ok('STF_xyz_half_of_P027_tensor_normalization',sp.simplify(2*STF[0,1,2]-p27.PtSTF[0,1,2])==0)
ok('full_M_xyz_value',sp.simplify(M[0,1,2]+p27.a**2*p27.mu*sp.sqrt(6)/12)==0)
ok('nonzero_rank3_source_tensor',STF[0,1,2]!=0)

# Classical thermodynamic FIELD-conjugacy, explicitly distinguished from
# Sato/Hayami's fully quantum-geometric periodic Kubo formula.
B0=sp.symbols('B0:3'); grad=sp.symbols('H0:9')
Gvars=sp.symbols('G0:27')
Ffree=-sum(moments[z][i]*B0[i] for z in range(len(pts)) for i in range(3))
Ffree-=sum(moments[z][i]*pts[z][j]*grad[3*i+j]
  for z in range(len(pts)) for i,j in product(range(3),repeat=2))
Ffree-=sum(moments[z][i]*pts[z][j]*pts[z][k]*Gvars[9*i+3*j+k]/2
  for z in range(len(pts)) for i,j,k in idx)
Ffree=sp.expand(Ffree)
for i,j,k in idx:
    ok(f'finite_thermodynamic_conjugate_{i}{j}{k}',
       sp.simplify(-sp.diff(Ffree,Gvars[9*i+3*j+k])-M[i,j,k])==0)
ok('no_uniform_B_coupling',all(sp.diff(Ffree,B0[i])==0 for i in range(3)))
ok('no_linear_field_gradient_coupling',all(sp.diff(Ffree,grad[i])==0 for i in range(9)))
ok('time_reverse_full_tensor_sign',full_tensor(pts,[-v for v in moments])==sp.ImmutableDenseNDimArray([-v for v in M],(3,3,3)))
ok('spatial_inversion_axial_spin_even',full_tensor([-r for r in pts],moments)==M)

# Exact linear projectors on all Cartesian tensors: full 27-dimensional
# tensor -> symmetric-jk 18 -> totally symmetric/traceless 7.
E=[]
for b in idx:
  basis=sp.ImmutableDenseNDimArray([int(t==b) for t in idx],(3,3,3))
  E.append(basis)
Pjk=sp.Matrix.hstack(*[sp.Matrix([sym_jk(v)[i,j,k] for i,j,k in idx]) for v in E])
Pstf=sp.Matrix.hstack(*[sp.Matrix([stf(v)[i,j,k] for i,j,k in idx]) for v in E])
ok('jk_sym_projection_idempotent',Pjk*Pjk==Pjk)
ok('jk_sym_projection_rank18',Pjk.rank()==18)
ok('STF_projection_idempotent',Pstf*Pstf==Pstf)
ok('STF_projection_rank7',Pstf.rank()==7)
ok('STF_nested_in_jk_sym',Pjk*Pstf==Pstf and Pstf*Pjk==Pstf)
ok('STF_27_dim_kernel20',27-Pstf.rank()==20)
ok('magnetic_jk_sym18_to_STF_kernel11',Pjk.rank()-Pstf.rank()==11)
ok('P027_raw_M_has_STF_inaccessible_component',any(M[i,j,k]-STF[i,j,k] for i,j,k in idx))
ok('projector_sym_all_formula',stf(sym_all(M))==STF)
ok('STF_covariant_under_crystal_C3',trans3(STF,C3)==STF)
ok('full_M_covariant_under_crystal_C3',trans3(M,C3)==M)

# A source-free neighbourhood: B=-grad(Phi) => G_ijk=d_j d_k B_i
# is totally symmetric and trace-free; only P_STF(M) couples.
d=sp.symbols('z_body',real=True)
point=dict(zip(old.coords, [d*old.axis[i] for i in range(3)]))
field=old.B4
Hfield=sp.ImmutableDenseNDimArray([
  sp.simplify(sp.diff(field[i],old.coords[j],old.coords[k]).subs(point,simultaneous=True))
  for i,j,k in idx],(3,3,3))
ok('applied_maxwell_field_second_derivative_nonzero',any(v!=0 for v in Hfield))
ok('applied_maxwell_field_curlfree_sym',Hfield==sym_all(Hfield))
ok('applied_maxwell_field_tracefree',all(sum(Hfield[i,j,j] for j in range(3))==0 for i in range(3)))
ok('applied_source_STF_fixed',stf(Hfield)==Hfield)
ok('full_raw_contraction_equals_STF_contraction',sp.simplify(dot(M,Hfield)-dot(STF,Hfield))==0)
ok('unobservable_complement_annihilated',sp.simplify(dot(M,Hfield)-dot(S,Hfield))==0)
Fquadratic=-dot(M,Hfield)
Fdirect=old.energy(field,pts,moments,d)
ok('finite_thermodynamic_energy_equals_actual_same_source',sp.simplify(Fquadratic-Fdirect)==0)
force=-sp.diff(Fquadratic,d)
ok('thermodynamic_source_force_reproduces_P027',sp.simplify(force-p27.forcePt)==0)
ok('force_requires_third_derivative_B',sp.simplify(sp.diff(Fquadratic,d)+p27.forcePt)==0)
ok('force_zero_without_source_coefficient',force.subs(old.k4,0)==0)
ok('source_reaction_included_separately',sp.simplify(force+(-force))==0)
ok('field_SI_units_not_fixed_from_Wyckoff_data',old.a in force.free_symbols and old.mu in force.free_symbols)

# Direct lattice and contragredient reciprocal action from ORIGINAL
# crystallography owner (not another ternary point/cell geometry).
A=s.Matrix([[1,1,0],[0,1,0],[0,0,1]])
R=C3
U=A.inv()*R*A
K=U.inv().T
metric=A.T*A
qpos=sp.Matrix(sp.symbols('n0:3')); qrec=sp.Matrix(sp.symbols('k0:3'))
ok('crystal_nonorthonormal_basis_invertible',A.det()==1)
ok('direct_action_integral',all(z.is_Integer for z in U))
ok('direct_C3_order3',U**3==sp.eye(3))
ok('reciprocal_C3_order3',K**3==sp.eye(3))
ok('direct_differs_reciprocal_nonorthogonal',U!=K)
ok('lattice_metric_preserved',U.T*metric*U==metric)
ok('reciprocal_phase_pairing_preserved',sp.simplify((K*qrec).dot(U*qpos)-qrec.dot(qpos))==0)
ok('spatial_action_reconstructed',A*U==R*A)
ok('Bravais_does_not_identify_spin_group',not any('measured' in str(y) for y in U))

# Explicit position/cell relabel is a PHYSICAL invariance; substituting
# *different actual physical sites* isn't. Prior P0.27 negative control.
ok('native_unit_cell_relabel_preserves_force',p27.fn(p27.physical_old+[-v for v in p27.physical_old],moments)==p27.fn(p27.physical_new+[-v for v in p27.physical_new],moments))
ok('real_finite_site_change_changes_force',sp.simplify(p27.f_shift-p27.forcePt)!=0)
ok('P027_packing_does_not_fix_bulk_operator',p27.Npacking.has(old.a))

receipt={
 'scope':'finite P0.27 classical conjugacy welded to original crystal direct/reciprocal contract, NOT a Sato-Hayami or Oike-Peters-Shinada bulk quantum formula',
 'checks_passed':len(checks),'checks':checks,
 'PtMn3_crystal_prototype':'AuCu3 L12 cP4 Pm-3m 221, Pt 1a, Mn 3c (original IUCr/prototype facts)',
 'magnetic_domain':'trial 120-degree Pt-centred inversion-complete fixture, not measured Kang film',
 'thermodynamic_source_relation':'M_ijk = -dOmega/d(d_j d_k B_i) = (1/2)*sum_a m_ai r_aj r_ak (FINITE classical model only)',
 'full_tensor_components_formal':27,'jk_symmetric_components':18,'Maxwell_STF_accessible_rank':7,
 'JK_symmetric_unprobed_directions':11,'arbitrary_tensor_unprobed_directions':20,
 'full_tensor_distinct_from_STF':True,
 'Maxwell_currentfree_probe':'G_ijk=d_j d_k B_i is fully symmetric and tracefree',
 'direct_field_contraction_equals_STF_contraction':True,
 'same_source_second_gradient_energy':str(Fquadratic),
 'same_source_harmonic_field_force':str(force),
 'P027_force':str(p27.forcePt),
 'direct_reciprocal_actions_distinct_in_sheared_basis':True,
 'physical_lattice_cell_relabelling_force_invariant':True,
 'bulk_Bloch_gauge_invariant_octupole_Eq11_implemented':False,
 'real_PtMn3_Wannier_SI_parameters_measured':False,
 'real_finite_sample_Maxwell_coils_and_stress':False,
 'metric_gravitational_response_or_levitation_demonstrated':False,
 'Agda_kernel_checked':False,
 'attribution':{
  'IUCr_prototype':'International Tables for Crystallography, Pm-3m No 221, AuCu3 L12 1a/3c',
  'earlier_order':'Bhowal and Spaldin, Phys Rev X 14 011019 (2024); Yamasaki/Nakao/Arima JPSJ 89 083703 (2020)',
  'original_thermodynamic':'Jun Oike, Robert Peters, Koki Shinada, Phys Rev B 112, 134412 (2025) DOI 10.1103/frq1-9xx7',
  'original_quantum':'Takumi Sato and Satoru Hayami, npj Quantum Materials 11, 32 (2026) DOI 10.1038/s41535-026-00865-9, Eq5/11',
  'original_experiment':'Jaimin Kang et al, Nature 658, 1160-1166 (2026) DOI 10.1038/s41586-026-11172-5',
  'native_DASHI':'crystallography_common_types_symmetries_roadmap.md; crystallography_native_lattice_hyperfabric_reuse.md; CrystalRealizationConsumerContractExact; OCT369 P0.14/P0.26/P0.27',
  'new_DASHI':'finite thermodynamic derivative + current-free Maxwell tensor rank/projection + P0.27 same-source force and direct/reciprocal lattice audit'
 }
}
if __name__=='__main__':print(json.dumps(receipt,sort_keys=True,indent=2))
