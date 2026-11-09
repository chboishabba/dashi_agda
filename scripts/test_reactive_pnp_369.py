# Synthetic numerical regression, not BH4 measurements or Agda acceptance.
"""Non-biological regression tests for the 3x3x3 reactive-PNP reference solver."""
import numpy as np
import pytest
from reactive_pnp_369 import (BONDS, INDEX, Model, implicit_step, native_flux,
                               poisson, synthetic_demo, vector_rhs)


def model():
    return Model(z=np.array([1,-1,0]), D=np.array([0.12,0.1,0.08]),
                 reactants=np.array([[1,1,0]]), products=np.array([[0,0,1]]),
                 kf=np.array([0.04]), kb=np.array([0.04]),
                 standard_mu=np.zeros(3))


def test_geometry_exact():
    assert len(BONDS)==54
    assert len(set(BONDS))==54
    assert all(sum(abs(a-b) for a,b in zip(pa,pb))==1
               for ia,ib in BONDS
               for pa,pb in [(list(INDEX)[ia],list(INDEX)[ib])])


def test_thermodynamic_synthetic_step():
    d=synthetic_demo()
    assert d['charge_defect']<1e-10
    assert d['free_energy_after']<=d['free_energy_before']
    assert d['minimum_concentration']>0


def test_homogeneous_equilibrium():
    m=model(); c=np.ones((27,3))
    # A=B=C=1; zero net ionic charge and reaction rate.
    phi=poisson(c,m)
    assert np.max(np.abs(phi))<1e-12
    assert np.max(np.abs(native_flux(c,phi,m)))<1e-12
    assert np.max(np.abs(vector_rhs(c,m,phi)))<1e-12
    final,r=implicit_step(c,0.1,m)
    assert np.max(np.abs(final-c))<1e-9
    assert r['numerical_residual_max']<1e-9


def test_two_sequential_transient_steps():
    m=model(); c=np.ones((27,3)); c[:,2]=0.5
    c[INDEX[(-1,0,0)],0]+=0.3
    c[INDEX[(1,0,0)],1]+=0.2
    e=[]
    for _ in range(2):
        c,receipt=implicit_step(c,0.02,m)
        e.append(receipt['free_energy_after'])
        assert receipt['numerical_residual_max']<1e-8
        assert receipt['charge_defect']<1e-8
    assert e[1]<=e[0]


def test_invalid_charge_or_detailed_balance_fails():
    for products,kf in [(np.array([[0,1,1]]),np.array([0.04])),
                        (np.array([[0,0,1]]),np.array([0.08]))]:
        with pytest.raises(ValueError):
            Model(z=np.array([1,-1,0]), D=np.ones(3),
                  reactants=np.array([[1,1,0]]),products=products,
                  kf=kf,kb=np.array([0.04]),standard_mu=np.zeros(3))


def test_no_negative_input_or_zero_timestep():
    m=model();c=np.ones((27,3));c[0,0]=0
    with pytest.raises(ValueError):implicit_step(c,0.1,m)
    c[0,0]=1
    with pytest.raises(ValueError):implicit_step(c,0,m)

def test_synthetic_29_species_12_reaction_instantaneous_dissipation():
    """Geometry/size stress, NOT the acquired 29x12 Rhea chemistry."""
    from reactive_pnp_369 import dissipation_diagnostics
    rng=np.random.default_rng(369)
    z=np.array(([1,-1,0]*10)[:29])
    A=np.zeros((12,29),dtype=int)
    B=np.zeros((12,29),dtype=int)
    for r in range(12):
        A[r,r]=1
        B[r,r+3]=1  # same valence, intentionally SYNTHETIC
    m=Model(z=z,D=np.full(29,0.1),reactants=A,products=B,
            kf=np.full(12,0.02),kb=np.full(12,0.02),standard_mu=np.zeros(29))
    for _ in range(20):
        c=rng.uniform(0.3,1.8,(27,29))
        phi=poisson(c,m)
        rates=dissipation_diagnostics(c,phi,m)
        assert rates['transport_power']<=1e-9
        assert rates['reaction_power']<=1e-9
        change=vector_rhs(c,m,phi)
        assert abs(np.sum(change@m.z))<1e-10
    invalid=B.copy()
    invalid[0,3]=0
    invalid[0,4]=1
    with pytest.raises(ValueError):
        Model(z=z,D=np.full(29,0.1),reactants=A,products=invalid,
              kf=np.full(12,0.02),kb=np.full(12,0.02),standard_mu=np.zeros(29))


def test_sg_per_edge_electrochemical_dissipation_sign():
    """Per-edge sign test on original 54 bonds; synthetic 29-species states."""
    rng=np.random.default_rng(1454)
    z=np.array(([1,-1,0]*10)[:29]); A=np.zeros((12,29),int); B=np.zeros((12,29),int)
    for j in range(12): A[j,j]=1;B[j,j+3]=1
    m=Model(z=z,D=rng.uniform(0.01,0.3,29),reactants=A,products=B,
            kf=np.full(12,0.04),kb=np.full(12,0.04),standard_mu=np.zeros(29))
    for _ in range(12):
        c=rng.uniform(0.1,2.5,size=(27,29));ph=poisson(c,m)
        J=native_flux(c,ph,m)
        for e,(a,b) in enumerate(BONDS):
            dmu=m.RT*np.log(c[b]/c[a])+m.z*m.F*(ph[b]-ph[a])
            assert np.max(J[e]*dmu)<1e-9
