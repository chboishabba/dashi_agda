#!/usr/bin/env python3
"""KSW 668 finite discriminators: exact rational controls, not physical validation."""
from fractions import Fraction as Q
import unittest


def flow_pair(forward):
    return forward, -forward


def poynting_local_solution(current, time):
    """Unit-normalized local Maxwell solution: uniform E_x=1-J*t, B_y=2.

    curl(E)=curl(B)=0, dB/dt=0, dE/dt=-J; rho=0.
    This is a local uniform-field model with externally specified uniform J.
    It is not a finite-energy global solution or a measured plasma device.
    """
    e = Q(1) - current * time
    b = Q(2)
    field_energy = (e * e + b * b) / 2
    energy_derivative = e * (-current)
    flux_divergence = Q(0)
    work_to_matter = current * e
    return field_energy, energy_derivative, flux_divergence, work_to_matter


NUCLIDES = {
    "hydrogen1": (1, 0), "helium4": (2, 2),
    "carbon12": (6, 6), "carbon14": (6, 8),
    "nitrogen14": (7, 7), "neutron": (0, 1), "proton": (1, 0),
}


def nuclear_ledger(sources, products):
    def totals(side):
        return tuple(sum(NUCLIDES[s][i] for s in side) for i in (0, 1))
    return totals(sources), totals(products)


class KSW668ExactControls(unittest.TestCase):
    def test_a_conserved_pair_both_signs(self):
        self.assertEqual(sum(flow_pair(Q(3))), 0)
        self.assertEqual(sum(flow_pair(Q(-3))), 0)

    def test_a_same_strength_order_opposite_direction(self):
        stronger, weaker = Q(2), Q(1)
        self.assertGreater(stronger, weaker)
        self.assertEqual((stronger, weaker), (Q(2), Q(1)))
        self.assertGreater(flow_pair(Q(1))[0], 0)
        self.assertLess(flow_pair(Q(-1))[0], 0)

    def test_b_maxwell_ampere_and_faraday_local(self):
        h = Q(1, 8)
        for j in (Q(1), Q(-1)):
            for t in (Q(-1, 4), Q(0), Q(1, 4)):
                e_plus, e_minus = 1 - j * (t + h), 1 - j * (t - h)
                d_e = (e_plus - e_minus) / (2 * h)
                self.assertEqual(d_e, -j)  # curl B = 0, dE/dt = -J
                self.assertEqual(
                    poynting_local_solution(j, t + h)[0]
                    - poynting_local_solution(j, t - h)[0],
                    -2 * h * j * (1 - j * t),
                )

    def test_b_poynting_local_identity_all_samples(self):
        for j in (Q(1), Q(-1)):
            for t in (Q(-1, 4), Q(0), Q(1, 4)):
                _, du, div_s, je = poynting_local_solution(j, t)
                self.assertEqual(du + div_s + je, 0)

    def test_b_same_fields_opposite_work_sign(self):
        pos = poynting_local_solution(Q(1), Q(0))
        neg = poynting_local_solution(Q(-1), Q(0))
        self.assertEqual(pos[0], neg[0])
        self.assertEqual(pos[0], Q(5, 2))
        self.assertEqual(pos[-1], Q(1))
        self.assertEqual(neg[-1], Q(-1))

    def test_c_triple_alpha_charge_neutrons(self):
        self.assertEqual(*nuclear_ledger(["helium4"] * 3, ["carbon12"]))

    def test_c_n14_neutron_to_c14_proton(self):
        self.assertEqual(*nuclear_ledger(["nitrogen14", "neutron"], ["carbon14", "proton"]))

    def test_c_six_protons_not_carbon12(self):
        self.assertNotEqual(*nuclear_ledger(["hydrogen1"] * 6, ["carbon12"]))

    def test_d_constant_local_marginal_is_not_bit_channel(self):
        local = {"choice0": "baseline", "choice1": "baseline"}
        self.assertEqual(local["choice0"], local["choice1"])
        self.assertNotEqual(local["choice1"], "pulse")

    def test_e_observation_not_unique_cause(self):
        worlds = {"redistribution": "sameMeasuredTrace", "nuclear": "sameMeasuredTrace"}
        self.assertEqual(worlds["redistribution"], worlds["nuclear"])
        self.assertNotEqual("redistribution", "nuclear")

    def test_scope_no_empirical_rates_or_geometry(self):
        outputs = set(NUCLIDES)
        self.assertNotIn("cross_section", outputs)
        self.assertNotIn("spacetime_metric", outputs)
        self.assertNotIn("isotope_measurements", outputs)


if __name__ == "__main__":
    unittest.main(verbosity=2)
