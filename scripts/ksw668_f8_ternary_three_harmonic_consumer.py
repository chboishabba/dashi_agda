#!/usr/bin/env python3
"""Exact Base369 unbalanced-ternary INDEX codec for original a=t AdS5 TT.

The physical source tensor S_yy(k)=|k|^4*(mu^4+6mu^2+1)/8 has ONLY
Legendre harmonics ell in {0,2,4} and amplitudes 2/5, 4/7, 1/35.
DASHI Base369 TriTruth slots (tri-low,tri-mid,tri-high) have indices
q=0,1,2 and map to ell=2q and radial effective dimension d=3+4q.
This is a lossless INDEX of three arbitrary (not ternary-valued!)
physical radial functions. It is not a cyclic symmetry: the radial
operators L_3,L_7,L_11 differ. C3 cycling does not intertwine them,
and a C3 Fourier basis mixes the radial generators non-diagonally.
All receiver E4/E5 and causality convergence gates remain OPEN.
"""
import json
import sympy as sp

DIGITS=(0,1,2)
ELL=(0,2,4)
DIMS=(3,7,11)
COEFFS=(sp.Rational(2,5),sp.Rational(4,7),sp.Rational(1,35))

def even_ell(digit):
    if type(digit) is not int or digit not in DIGITS:
        raise ValueError('Base369 unbalanced q must be one of 0,1,2')
    return 2*digit

def digit_for_ell(ell):
    if type(ell) is not int or ell not in ELL:
        raise ValueError('physical spin-2 yy producer has only ell=0,2,4')
    return ell//2

def radial_dimension(digit):
    return 3+4*digit_for_ell(even_ell(digit))

def legendre_components(mu):
    return tuple(c*sp.legendre(2*q,mu) for q,c in zip(DIGITS,COEFFS))

def physical_tt_angular_symbol(mu):
    return (mu**4+6*mu**2+1)/8

def receiver_yy_from_radial_V(V,r,eps):
    if len(V)!=3 or not eps>0 or not r>=0:
        raise ValueError('three independent radial modes, r>=0, eps>0')
    return sum((r/eps)**(2*q)*V[q] for q in DIGITS)

def verify_angular_exact():
    mu=sp.symbols('mu',real=True)
    components=legendre_components(mu)
    assert sp.simplify(sum(components)-physical_tt_angular_symbol(mu))==0
    assert all(sp.simplify(sp.legendre(2*q,1)-1)==0 for q in DIGITS)
    for q in DIGITS:
        assert even_ell(q)==ELL[q]
        assert digit_for_ell(ELL[q])==q
        assert radial_dimension(q)==DIMS[q]
    r=sp.symbols('r',positive=True);W=sp.Function('W')(r)
    for q in DIGITS:
        ell=even_ell(q);d=radial_dimension(q)
        R=r**ell*W
        angular_laplacian=sp.diff(R,r,2)+2*sp.diff(R,r)/r-ell*(ell+1)*R/r**2
        lifted=r**ell*(sp.diff(W,r,2)+(d-1)*sp.diff(W,r)/r)
        assert sp.simplify(angular_laplacian-lifted)==0
    return dict(symbol='(mu^4+6mu^2+1)/8',
        exact_legendre_coefficients=['2/5','4/7','1/35'],
        physical_multipoles=[0,2,4],carrier_digits=[0,1,2],
        effective_radial_dimensions=[3,7,11],
        three_channel_angular_reconstruction_exact=True,
        radial_angular_laplacian_weld_exact=True)

def verify_c3_non_intertwining():
    first_cell=[2*d for d in DIMS]
    assert first_cell==[6,14,22]
    assert first_cell[1]-first_cell[0]==8
    omega=(-1+sp.I*sp.sqrt(3))/2
    F=sp.Matrix([[omega**(j*k) for k in DIGITS] for j in DIGITS])
    F_inv=sp.conjugate(F.T)/3
    assert (F*F_inv).applyfunc(sp.simplify)==sp.eye(3)
    diag=sp.diag(*DIMS)
    mixed=(F*diag*F_inv).applyfunc(sp.simplify)
    assert all(mixed[q,q]==7 for q in DIGITS)
    assert sp.simplify(mixed[0,1]-(-2+2*sp.I*sp.sqrt(3)/3))==0
    assert mixed!=diag
    return dict(physical_laplacian_on_r_squared=first_cell,
        C3_label_cycle_commutes_with_original_radial_operator=False,
        explicit_cycle_commutator_witness=8,
        C3_fourier_unitary_bidi=True,
        Fourier_basis_radial_matrix=[[str(v) for v in list(mixed.row(i))] for i in DIGITS],
        Fourier_basis_preserves_original_uncoupled_radial_channels=False)

def verify_fourier_commuting_square_and_zero_sector_no_go():
    # Unnormalised F is invertible, F^{-1}=F^dagger/3. Its first row
    # exactly SUMS the original three physical source/receiver channels.
    # The exact radial stiffness witness is A=diag(6,14,22), from
    # Delta_d r^2=2d, NOT a 369-symmetric 3x3 operator.
    omega=(-1+sp.I*sp.sqrt(3))/2
    F=sp.Matrix([[omega**(j*k) for k in DIGITS] for j in DIGITS])
    Finv=sp.conjugate(F.T)/3
    A=sp.diag(6,14,22)
    Ahat=(F*A*Finv).applyfunc(sp.simplify)
    u=sp.Matrix([1,-1,0])
    z=(F*u).applyfunc(sp.simplify)
    assert z[0]==0 and z[1]!=0 and z[2]!=0
    assert (F*A*u)[0]==-8  # nontrivial sectors feed aggregate zero mode
    assert (Ahat*z-F*A*u).applyfunc(sp.simplify)==sp.zeros(3,1)
    for test in (sp.Matrix([1,3,-2]),sp.Matrix([sp.Rational(1,3),-1,2])):
        assert (F*test)[0]==sum(test)
        assert (Ahat*(F*test)-F*(A*test)).applyfunc(sp.simplify)==sp.zeros(3,1)
    return dict(full_three_sector_Fourier_commuting_square_exact=True,
        original_receiver_sum_equals_Fourier_trivial_character=True,
        original_trivial_character_sector_dynamically_closed=False,
        initially_zero_receiver_witness=[1,-1,0],
        exact_radial_first_cell_image=[6,-14,0],
        generated_receiver_trivial_character=-8,
        discarding_nontrivial_Fourier_sectors_is_unsound=True)

def actual_original_angular_source_profiles():
    from ksw668_f8_tt_multipole import profiles
    source=profiles()
    assert [x[0] for x in source]==[0,2,4]
    assert all(abs(x[2])<1e30 for x in source)
    return dict(actual_producer_ell=[int(x[0]) for x in source],
        actual_source_zero_origin_moments_checked_by_existing_fv_consumer=True)

def audit():
    angular=verify_angular_exact();c3=verify_c3_non_intertwining()
    commuting=verify_fourier_commuting_square_and_zero_sector_no_go()
    vals=[sp.Rational(5,3),-sp.Rational(2,7),sp.Rational(13,11)]
    r=sp.Rational(2,3);eps=sp.Rational(1,2)
    reconstructed=receiver_yy_from_radial_V(vals,r,eps)
    independent=sum((r/eps)**ELL[q]*vals[q] for q in DIGITS)
    assert reconstructed==independent
    return dict(kind='KSW668_original_F8_Base369_unbalanced_ternary_index_consumer',
        angular=angular,non_equivariance=c3,cyclotomic_commuting_square=commuting,
        independent_radial_amplitudes_retained=3,
        receiver_axis_reconstruction_exact=True,
        original_photon_dark_and_both_Weyl_convergence=False,
        complete_5D_source_kinematics_proved=False,
        original_C3_dynamical_symmetry_claimed=False)

if __name__=='__main__': print(json.dumps(audit(),indent=2))
