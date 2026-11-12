"""Adversarial SG / PNP gate tests: finite identities versus physical claims.

Uses the existing native geometry, solver Bernoulli and current orientation.
Synthetic examples are NOT original Rhea kinetics and NOT Agda receipts.
"""
import numpy as np
import pytest
from reactive_pnp_369 import (
    BONDS, Model, bernoulli, native_flux, poisson, vector_rhs,
    closed_pnp_entropy_factorization,
)


def no_reaction_model(z, diffusion=None):
    z=np.asarray(z,dtype=float)
    n=z.size
    return Model(
        z=z, D=(np.ones(n) if diffusion is None else np.asarray(diffusion,dtype=float)),
        reactants=np.empty((0,n),dtype=int),
        products=np.empty((0,n),dtype=int),
        kf=np.empty(0), kb=np.empty(0),
        standard_mu=np.zeros(n),
        h=1., RT=1., F=1., epsilon=1.,
    )


@pytest.mark.parametrize("drop",[-12.,-3.,-0.4,-1e-10,0.,1e-10,0.4,3.,12.])
def test_exact_sg_bernoulli_orientation_difference_numerically(drop):
    # B(-x)-B(x)=x, including the analytically extended B(0)=1.
    assert np.isclose(bernoulli(-drop)-bernoulli(drop),drop,
                      atol=1e-14,rtol=1e-9)
    assert np.isfinite(bernoulli(drop))
    assert bernoulli(0.) == 1.


def test_native_sg_current_orientation_is_not_user_incoming_flux():
    # Python native_flux is outward a->b:
    # J_ab=(D/h)[B(x)c_a - B(-x)c_b].
    # The user's displayed formula is inward and has the OPPOSITE sign.
    m=no_reaction_model([1.])
    c=np.ones((27,1))
    a,b=BONDS[0]
    c[a,0]=1.4
    c[b,0]=0.7
    phi=np.zeros(27)
    phi[b]=0.3
    actual=native_flux(c,phi,m)[0,0]
    x=phi[b]-phi[a]
    inward=(m.D[0]/m.h)*(bernoulli(-x)*c[b,0]-bernoulli(x)*c[a,0])
    assert np.isclose(actual,-inward,rtol=1e-14,atol=1e-14)
    assert actual != 0.


def test_local_cell_mass_is_not_constant_when_global_species_mass_is():
    m=no_reaction_model([0.])
    c=np.ones((27,1))
    c[0,0]=2.
    rhs=vector_rhs(c,m,phi=np.zeros(27))
    assert rhs[0,0]<0
    assert np.any(rhs[:,0]>0)
    assert abs(float(rhs.sum()))<1e-12
    assert np.max(abs(rhs))>0


def test_zero_drop_is_removable_singularity_even_for_neutral_species():
    m=no_reaction_model([0.])
    c=np.ones((27,1))
    a,b=BONDS[0]
    c[a,0]=3.
    c[b,0]=2.
    phi=np.linspace(-1,1,27)  # zero * phi always zero
    flux=native_flux(c,phi,m)[0,0]
    assert flux == (m.D[0]/m.h)*(c[a,0]-c[b,0])
    assert np.all(np.isfinite(native_flux(c,phi,m)))


def test_source_stoichiometry_does_not_imply_chemical_dissipation():
    # Hypothetical A <-> B, S=(-1,+1) has exact atom left-kernel (1,1).
    # Without detailed balance, the standard ideal free energy may RISE.
    ca,cb=1.,1.2
    forward=2.*ca
    backward=1.*cb
    unconstrained_power=(forward-backward)*np.log(cb/ca)
    assert unconstrained_power>0
    with pytest.raises(ValueError,match="detailed balance"):
        Model(
            z=np.zeros(2),D=np.zeros(2),
            reactants=np.array([[1,0]]), products=np.array([[0,1]]),
            kf=np.array([2.]), kb=np.array([1.]),
            standard_mu=np.zeros(2),
        )


def test_equilibrium_has_zero_dissipation_so_strict_decrease_is_false():
    m=Model(z=np.zeros(2),D=np.zeros(2),
            reactants=np.array([[1,0]]), products=np.array([[0,1]]),
            kf=np.array([1.]),kb=np.array([1.]),
            standard_mu=np.zeros(2))
    c=np.ones((27,2))
    phi=np.zeros(27)
    receipts=closed_pnp_entropy_factorization(c,phi,m)
    assert receipts["bond_terms"]==54
    assert receipts["reaction_terms"]==27
    assert abs(receipts["transport_power"])<1e-12
    assert abs(receipts["reaction_power"])<1e-12


def test_true_solver_detailed_balance_supports_both_entropy_signs():
    m=Model(
        z=np.array([1.,-1.]),D=np.array([0.8,1.1]),
        reactants=np.empty((0,2),dtype=int),
        products=np.empty((0,2),dtype=int),
        kf=np.empty(0),kb=np.empty(0),
        standard_mu=np.zeros(2))
    c=np.ones((27,2))
    c[:,0]=np.linspace(.7,1.8,27)
    c[:,1]=np.linspace(1.6,.75,27)
    phi=poisson(c,m)
    receipt=closed_pnp_entropy_factorization(c,phi,m)
    assert receipt["bond_terms"]==54
    assert receipt["transport_power"]<0
    assert abs(receipt["reaction_power"])<1e-12
    assert not receipt["agda_kernel_checked"]
