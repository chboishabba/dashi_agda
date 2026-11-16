#!/usr/bin/env python3
"""KSW668 original moving a=t AdS5: sourced radial ladder vs optional Weil chart.

r is the radius in the ordinary brane 3-space. Extra bulk direction z
provides the KK-normal operator, NOT the ell=0,2,4 radial FV spectra.
J=(1/r)d_r intertwines L_d and L_{d+2}; J² yields d=3,7,11.
The three-channel shift is nilpotent and not a physical C3 rotation.
The actual original TT source S0/S2/S4 is not generically ladder-related.

A CHOSEN, not physically derived, quadratic form Q(j)=j²/3 on Z/3Z
produces finite Weil matrices S=-i*DFT_3/sqrt(3), T=diag(1,omega,omega).
They satisfy exact SL2Z relations, but S does NOT commute with the
original radial dimension matrix or the sourced physical operator.
Prior-art owners: Base369, TTMultipoleAngularRationalExact,
TriadicEisensteinTransformationTheorem, PenumbralVectorValuedForm,
c3-braid-b3-modular-monster-ads3-gravity-maxcut.md.
"""
import json
import sympy as sp

r,d=sp.symbols('r d',positive=True)

def L(dim,f):return sp.diff(f,r,2)+(dim-1)*sp.diff(f,r)/r
def J(f):return sp.diff(f,r)/r
def Jpower(f,k):
    for _ in range(k):f=J(f)
    return f

def original_radial_ladder():
    f=sp.Function('f')(r)
    for k in (1,2,4):
        assert sp.simplify(L(d+2*k,Jpower(f,k))-Jpower(L(d,f),k))==0
    for dim in (3,7):
        assert sp.simplify(L(dim+4,Jpower(f,2))-Jpower(L(dim,f),2))==0
    fields=[sp.Function('u%d'%q)(r) for q in range(3)]
    lhs=[0,L(7,Jpower(fields[0],2)),L(11,Jpower(fields[1],2))]
    rhs=[0,Jpower(L(3,fields[0]),2),Jpower(L(7,fields[1]),2)]
    assert all(sp.simplify(x-y)==0 for x,y in zip(lhs,rhs))
    assert Jpower(sp.Integer(1),2)==0  # noninjective, not unitary C3
    # Exact original TT modal radial source profiles: source f=r^10
    # disproves a GENERIC source q0 -> q1 differential ladder.
    f=r**10;f1=sp.diff(f,r);f2=sp.diff(f,r,2)
    f3=sp.diff(f,r,3);f4=sp.diff(f,r,4)
    s0=sp.Rational(2,5)*(f4+4*f3/r)
    s2=sp.Rational(4,7)*(f4+f3/r-6*f2/r**2+6*f1/r**3)
    residual=sp.factor(Jpower(s0,2)-s2/r**2)
    assert residual!=0
    return {
        'exact_ladder':'L_(d+2) J=J L_d, J=(1/r)d_r',
        'actual_dimension_pairs':[[3,7],[7,11]],
        'all_3_channel_interior_shift_commutes':True,
        'three_channel_shift_N_cubed_zero':True,
        'noninvertible_J_squared':True,
        'generic_source_not_ladder_related':True,
        'source_counterexample_polynomial_r10':str(residual),
        'finite_FV_boundary_intertwiner_proved':False,
        'original_sourced_Weyl_receiver_symmetry_proved':False}

def optional_weil_Z3():
    w=(-1+sp.sqrt(3)*sp.I)/2
    U=sp.Matrix([[w**(j*k) for k in range(3)] for j in range(3)])/sp.sqrt(3)
    S=-sp.I*U;T=sp.diag(1,w,w)
    P=sp.Matrix([[1,0,0],[0,0,1],[0,1,0]])
    zero=sp.zeros(3)
    clean=lambda a:a.applyfunc(sp.simplify)
    assert clean(U**2-P)==zero
    assert clean(S**2+P)==zero
    assert clean((S*T)**3-S**2)==zero
    assert clean(S**4-sp.eye(3))==zero
    assert clean(T**3-sp.eye(3))==zero
    assert clean(S.conjugate().T*S-sp.eye(3))==zero
    assert clean(T.conjugate().T*T-sp.eye(3))==zero
    A=sp.diag(3,7,11)
    assert clean(S*A-A*S)!=zero
    assert clean(T*A-A*T)==zero
    q=[sp.Rational(j*j,3)%1 for j in range(3)]
    assert q==[0,sp.Rational(1,3),sp.Rational(1,3)]
    return {
        'chosen_finite_quadratic_module':'Z/3Z, Q(j)=j²/3 (mod 1)',
        'Q_values':list(map(str,q)),
        'normalized_modular_S':'-i * DFT3/sqrt(3)',
        'modular_T':'diag(1,omega,omega)',
        'S_squared':'-charge-conjugation; swaps q=1 and q=2',
        'S4_I_ST_cubed_equals_S_squared_T3_I_verified':True,
        'modular_S_commutes_with_original_radial_generator':False,
        'chosen_Q_is_physical_AdS5_charge':False,
        'actual_vector_valued_modular_source_form_derived':False}

def audit():
    return {
      'same_original_physical_object':'moving a=t AdS5; radial r in 3-space; bulk z is extra normal coordinate',
      'Base369_unsigned_q':[0,1,2],
      'physical_even_ell':[0,2,4],
      'effective_spatial_radial_d':[3,7,11],
      'radial_ladder':original_radial_ladder(),
      'finite_modular_chart':optional_weil_Z3(),
      'Monster':{
        'minimum_nontrivial_complex_rep_dimension':196883,
        'whole_Monster_nontrivial_3channel_linear_rep_possible':False,
        'restricted_C3_subgroup_chart_possible':True,
        'graded_VOA_and_physical_operator_weld':False},
      'Kaluza_Klein':{
        'spatial_r_radial_spectra_are_KK_mass_spectra':False,
        'true_KK_requires_bulk_z_normal_eigenproblem':True,
        'moving_wall_static_KK_truncation_established':False},
      'physical_F8_E4_E5_convergence':False}
if __name__=='__main__':print(json.dumps(audit(),indent=2))
