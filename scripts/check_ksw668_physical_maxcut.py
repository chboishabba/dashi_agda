#!/usr/bin/env python3
"""Exact KSW 668 A-E physics benchmarks. Models, not measurements or kernel proofs.

A original-form ideal Elsasser Fourier triad; B Maxwell/Poynting with boundary;
C NIST masses + 2026 measured N14 thermal cross section; D Lorentz and Bell;
E isotope-source identifiability. Values/signatures are source-indexed in docs.
"""
import json
from decimal import Decimal, getcontext
from fractions import Fraction as Q
from pathlib import Path
import unittest
import sympy as s

getcontext().prec = 40
I = s.I
p = s.Matrix([1, 0, 0])
q = s.Matrix([0, 1, 0])
k = p + q
ZERO = s.zeros(3, 1)


def spectral_state(sign):
    """Instantaneous, conjugate-paired and divergence-free z+/z- Fourier state."""
    assert sign in (-1, 1)
    plus = {tuple(q): s.Matrix([1, 0, 0]),
            tuple(k): s.Matrix([sign * I, -sign * I, 0])}
    minus = {tuple(p): s.Matrix([0, 1, 0])}
    for state in (plus, minus):
        for wave, value in list(state.items()):
            state[tuple(-c for c in wave)] = s.conjugate(value)
    return plus, minus


def mode(state, wave):
    return state.get(tuple(wave), ZERO)


def magnetic(state, wave):
    return (mode(state[0], wave) - mode(state[1], wave)) / 2


def mag2(v):
    return s.simplify((s.conjugate(v).T * v)[0])


def selected_transfer(state):
    plus, minus = state
    transport = mode(minus, p)
    target_q = mode(plus, q)
    target_k = mode(plus, k)
    projector = s.eye(3) - (k * k.T) / (k.T * k)[0]
    forcing = -I * projector * ((transport.T * q)[0] * target_q)
    return s.simplify(s.re((s.conjugate(target_k).T * forcing)[0]))


def maxwell_slab(j):
    """E=(0,x-t+1-j*t,0), B=(0,0,x-t), J=(0,j,0);
    normalized eps=mu=c=1, periodic unit transverse area x in [0,L].
    Fields require boundary sources, not finite-energy all-space data.
    """
    x, t, L = s.symbols("x t L", real=True)
    ey, bz = x - t + 1 - j * t, x - t
    energy = (ey ** 2 + bz ** 2) / 2
    flux = ey * bz
    work = j * ey
    total = s.integrate(energy, (x, 0, L))
    left, right = flux.subs(x, 0), flux.subs(x, L)
    return dict(x=x, t=t, L=L, ey=ey, bz=bz, energy=energy,
                flux=flux, work=work, left=left, right=right,
                local=s.expand(s.diff(energy, t) + s.diff(flux, x) + work),
                integrated=s.simplify(s.diff(total, t) + right - left
                                      + s.integrate(work, (x, 0, L))))


# NIST atomic-mass tables; electrons balance on both sides. Values are
# evaluated atomic masses, not mathematical constants known exactly.
MASSES = {
    "He4": Decimal("4.00260325413"),
    "C12": Decimal("12"),
    "C14": Decimal("14.0032419884"),
    "N14": Decimal("14.00307400443"),
    "H1": Decimal("1.00782503223"),
    "n": Decimal("1.00866491595"),
}
U_MEV = Decimal("931.49410242")
SIGMA_B = Decimal("1.828")
SIGMA_ERROR_B = Decimal("0.053")


def q_values():
    return ((3 * MASSES["He4"] - MASSES["C12"]) * U_MEV,
            (MASSES["N14"] + MASSES["n"] - MASSES["C14"]
             - MASSES["H1"]) * U_MEV)


def neutral_atom_two_body_kinematics():
    # Effective neutral-atom rest masses with conserved electron count:
    # N14 atom + n -> C14 atom + H1 atom. This is a four-vector kinematic
    # benchmark, NOT a fully corrected nuclear-ion/electron final state.
    u = s.Rational("931.49410242")
    W = (s.Rational("14.00307400443")+s.Rational("1.00866491595"))*u
    mc = s.Rational("14.0032419884")*u
    mp = s.Rational("1.00782503223")*u
    EC = (W**2+mc**2-mp**2)/(2*W)
    EP = (W**2+mp**2-mc**2)/(2*W)
    p2 = s.factor(EC**2-mc**2)
    return W, mc, mp, EC, EP, p2


def neutron_rate(flux_cm2_s, target_N14_atoms):
    scale = Decimal(str(flux_cm2_s)) * Decimal(str(target_N14_atoms)) * Decimal("1e-24")
    return scale * SIGMA_B, scale * SIGMA_ERROR_B


def bell_local_after_bob(U):
    ket = s.Matrix([1, 0, 0, 1]) / s.sqrt(2)
    rho = ket * ket.H
    transform = s.kronecker_product(s.eye(2), U)
    new = transform * rho * transform.H
    return s.Matrix([[s.simplify(sum(new[2*a+b, 2*c+b] for b in range(2)))
                      for c in range(2)] for a in range(2)])


def isotope_final(initial, uptake, nuclear, clearance):
    return initial + uptake + nuclear - clearance


class KSWPhysicalBenchmarks(unittest.TestCase):
    def test_a_same_magnetic_strength(self):
        a, b = spectral_state(1), spectral_state(-1)
        for w in (p, q, k, -p, -q, -k):
            self.assertEqual(mag2(magnetic(a, w)), mag2(magnetic(b, w)))
        self.assertEqual(mag2(magnetic(a, k)), s.Rational(1, 2))
        self.assertEqual(mag2(magnetic(a, q)), s.Rational(1, 4))

    def test_a_reality_divergence(self):
        for sign in (-1, 1):
            for species in spectral_state(sign):
                for w, v in species.items():
                    self.assertEqual(s.Matrix(w).T * v, s.zeros(1, 1))
                    self.assertEqual(mode(species, tuple(-z for z in w)), s.conjugate(v))

    def test_a_signed_selected_original_transfer(self):
        self.assertEqual(selected_transfer(spectral_state(1)), -1)
        self.assertEqual(selected_transfer(spectral_state(-1)), 1)

    def test_a_resonance(self):
        self.assertEqual(p + q, k)

    def test_b_faraday(self):
        for j in (-1, 1):
            z = maxwell_slab(s.Integer(j))
            self.assertEqual(s.diff(z["bz"], z["t"]), -s.diff(z["ey"], z["x"]))

    def test_b_ampere(self):
        for j in (-1, 1):
            z = maxwell_slab(s.Integer(j))
            self.assertEqual(-s.diff(z["bz"], z["x"]), j + s.diff(z["ey"], z["t"]))

    def test_b_local_poynting(self):
        for j in (-1, 1):
            self.assertEqual(maxwell_slab(s.Integer(j))["local"], 0)

    def test_b_actual_boundary_flux(self):
        for j in (-1, 1):
            z = maxwell_slab(s.Integer(j))
            self.assertEqual(z["integrated"], 0)
            self.assertEqual((z["right"]-z["left"]).subs({z["t"]:0,z["L"]:1}), 2)

    def test_b_initial_fields_equal_and_opposite_work(self):
        pos, neg = maxwell_slab(s.Integer(1)), maxwell_slab(s.Integer(-1))
        for key in ("ey", "bz", "energy", "flux"):
            self.assertEqual(s.simplify(pos[key].subs(pos["t"], 0)
                                        -neg[key].subs(neg["t"], 0)), 0)
        self.assertEqual(pos["work"].subs({pos["x"]:0,pos["t"]:0}), 1)
        self.assertEqual(neg["work"].subs({neg["x"]:0,neg["t"]:0}), -1)

    def test_c_nist_mass_q(self):
        alpha, np = q_values()
        self.assertTrue(Decimal("7.274") < alpha < Decimal("7.276"))
        self.assertTrue(Decimal("0.625") < np < Decimal("0.628"))

    def test_c_exact_effective_fourmomentum_cm_kinematics(self):
        W, mc, mp, EC, EP, p2 = neutral_atom_two_body_kinematics()
        self.assertEqual(s.simplify(EC+EP-W),0)
        self.assertEqual(s.simplify(EP**2-mp**2-p2),0)
        self.assertGreater(p2,0)
        self.assertEqual(s.simplify((EC-mc)+(EP-mp)),W-mc-mp)

    def test_c_neutron_rate_uncertainty_and_flux_dependence(self):
        self.assertEqual(neutron_rate("1e6", "1e20"),
                         (Decimal("182.8"), Decimal("5.3")))
        self.assertEqual(neutron_rate(0, "1e20"), (0, 0))

    def test_d_bell_amplitude_damping_cptp(self):
        # A nonunitary local CPTP map on Bob, not just reversible unitaries.
        for g in (s.Integer(0),s.Rational(1,4),s.Rational(1,2),s.Integer(1)):
            k0 = s.diag(1,s.sqrt(1-g))
            k1 = s.Matrix([[0,s.sqrt(g)],[0,0]])
            self.assertEqual(s.simplify(k0.H*k0+k1.H*k1),s.eye(2))
            self.assertEqual(
                s.simplify(bell_local_after_bob(k0)+bell_local_after_bob(k1)),
                s.eye(2)/2)

    def test_d_flat_lorentz_causality(self):
        x, t, c = Q(10), Q(0), Q(1)
        self.assertLess((c*t)**2 - x*x, 0)

    def test_d_bell_local_operations(self):
        for U in (s.eye(2), s.Matrix([[0,1],[1,0]]),s.diag(1,-1),
                  s.Matrix([[1,1],[1,-1]])/s.sqrt(2)):
            self.assertEqual(bell_local_after_bob(U), s.eye(2)/2)

    def test_e_identical_observation_two_sources(self):
        self.assertEqual(isotope_final(Q(10),Q(5),Q(0),Q(0)),
                         isotope_final(Q(10),Q(2),Q(3),Q(0)))

    def test_e_paired_tracer_identifies_residual(self):
        initial, uptake, clearance, final = Q(10),Q(2),Q(0),Q(15)
        nuclear = final - initial - uptake + clearance
        self.assertEqual(nuclear,3)
        self.assertEqual(isotope_final(initial,uptake,nuclear,clearance),final)


if __name__ == "__main__":
    result = unittest.TextTestRunner(verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(KSWPhysicalBenchmarks))
    if result.wasSuccessful():
        alpha, np = q_values()
        receipt = {
            "date":"2026-11-14", "authority":"exact analytic/model test only, no Agda kernel or experiment",
            "tests_passed":result.testsRun,
            "A":{"p":[1,0,0],"q":[0,1,0],"k":[1,1,0],
                 "b_k_squared":"1/2","b_q_squared":"1/4","transfer_plus_k":["-1","+1"]},
            "B":{"equations":"Maxwell + Poynting exact polynomial local/slab",
                 "surface_flux_at_t0_L1":"2","current":["-1","+1"]},
            "C":{"triple_alpha_Q_MeV":str(alpha),"N14_n_p_C14_Q_MeV":str(np),
                 "sigma_thermal_barn":"1.828 +/- 0.053",
                 "rate_at_hypothetical_flux_1e6_and_N_1e20_per_s":"182.8 +/- 5.3",
                 "two_body_CM_neutral_atom_kinematics":"energy and mass shells exactly satisfy 4-momentum, not nuclear-ion reaction data"},
            "D":{"flat_spacelike_event":"x=10,t=0,c=1",
                 "bell_reduced_alice":"I/2 under Bob I,X,Z,H and CPTP amplitude damping"},
            "E":{"observations":"total=15 from (uptake,nuclear)=(5,0) or (2,3)",
                 "paired_residual":"3 given measured initial, uptake, clearance and final"},
            "unpaid":"physical same-object Agda triad inhabitant; general PDE boundary theorem; nuclear rate environment; KK global solution; biological isotope measurement"
        }
        print("RECEIPT",json.dumps(receipt,indent=2))
    raise SystemExit(not result.wasSuccessful())
