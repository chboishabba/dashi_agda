"""Synthetic tests of free-energy remainder; not original BH4 physiology."""
import unittest
import numpy as np
from reactive_pnp_369 import Model, INDEX, implicit_step
from bh4_closed_pnp_free_energy_remainder import remainder_receipt


def synthetic_model():
    return Model(
        z=np.array([1, -1, 0]), D=np.array([.12, .1, .08]),
        reactants=np.array([[1, 1, 0]]), products=np.array([[0, 0, 1]]),
        kf=np.array([.04]), kb=np.array([.04]),
        standard_mu=np.zeros(3),
    )


def initial_state():
    c = np.ones((27, 3))
    c[:, 0] = c[:, 1] = 1.2
    c[:, 2] = .4
    c[INDEX[(-1,0,0)], 0] += .4
    c[INDEX[(1,0,0)], 1] += .3
    return c


class GroundedFreeEnergyRemainderTests(unittest.TestCase):
    def test_arbitrary_positive_pair_exact_reconstruction(self):
        m = synthetic_model()
        c0 = initial_state()
        c1 = .85*c0 + .15*np.roll(c0, 1, axis=0)
        receipt = remainder_receipt(c0, c1, .08, m)
        self.assertAlmostEqual(receipt["identity_defect"], 0., places=9)
        self.assertGreaterEqual(receipt["chemical_bregman_gap"], -1e-12)
        self.assertGreaterEqual(receipt["electrostatic_bregman_gap"], -1e-12)

    def test_implicit_root_energy_dissipation(self):
        m = synthetic_model()
        c0 = initial_state()
        c1, root = implicit_step(c0, .08, m)
        receipt = remainder_receipt(c0, c1, .08, m)
        self.assertAlmostEqual(receipt["identity_defect"], 0., places=9)
        self.assertLessEqual(receipt["energy_change"], 1e-9)
        self.assertLessEqual(receipt["transport_power"], 1e-9)
        self.assertLessEqual(receipt["reaction_power"], 1e-9)
        self.assertLessEqual(receipt["implicit_residual_max"], 1e-8)
        self.assertFalse(receipt["root_existence_proven"])

    def test_nonroot_has_visible_residual_work(self):
        m = synthetic_model()
        c0 = initial_state()
        c1 = c0.copy()
        receipt = remainder_receipt(c0, c1, .08, m)
        self.assertAlmostEqual(receipt["identity_defect"], 0., places=9)
        self.assertGreater(receipt["implicit_residual_max"], 0.)
        self.assertAlmostEqual(receipt["chemical_bregman_gap"], 0., places=11)
        self.assertAlmostEqual(receipt["electrostatic_bregman_gap"], 0., places=11)

    def test_reject_bad_chart(self):
        m = synthetic_model()
        c0 = initial_state()
        c1 = c0.copy()
        c1[0,0] = 0.
        with self.assertRaises(ValueError):
            remainder_receipt(c0, c1, .08, m)
        with self.assertRaises(ValueError):
            remainder_receipt(c0, c0, -1., m)


if __name__ == "__main__":
    unittest.main()
