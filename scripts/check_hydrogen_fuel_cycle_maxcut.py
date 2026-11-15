#!/usr/bin/env python3
"""Independent arithmetic regression for the *conditional* DASHI fuel-cycle model.

Attribution: conventional reaction stoichiometry/energy laws belong to their
scientific sources. User-directed test design; ChatGPT-generated implementation,
2026-11-09. Tests do not imply an actual McLaren/XFuel apparatus has been
independently tested, a 2026 patent has been granted, or Agda has typechecked.
No network, pytest or CI infrastructure required.
"""
from dataclasses import dataclass
from fractions import Fraction
import unittest

ATOMS = {
    "H2O": (0, 2, 1),
    "H2": (0, 2, 0),
    "O2": (0, 0, 2),
    "CO2": (1, 0, 2),
    "CH4": (1, 4, 0),
}
REACTIONS = (
    ({"H2O": 2}, {"H2": 2, "O2": 1}),
    ({"CO2": 1, "H2": 4}, {"CH4": 1, "H2O": 2}),
    ({"CH4": 1, "O2": 2}, {"CO2": 1, "H2O": 2}),
)

def elements(molecules):
    return tuple(sum(n * ATOMS[s][k] for s, n in molecules.items())
                 for k in range(3))

def chemical_step(stock, reaction):
    reactants, products = reaction
    if any(stock.get(s, 0) < n for s, n in reactants.items()):
        raise ValueError("insufficient reagent")
    result = dict(stock)
    for s, n in reactants.items():
        result[s] -= n
    for s, n in products.items():
        result[s] = result.get(s, 0) + n
    return result

def engine_diesel(baseline_fuel, baseline_eff, assisted_eff, h2, synth):
    return Fraction(baseline_fuel) * baseline_eff / assisted_eff - h2 - synth

def guaranteed_saving(baseline_low, assisted_high, electrical_high):
    return assisted_high + electrical_high < baseline_low

@dataclass(frozen=True)
class CarbonStep:
    before: int
    makeup: int
    after: int
    emitted: int
    def validate(self):
        assert self.before + self.makeup == self.after + self.emitted

class ConditionalModelTests(unittest.TestCase):
    def test_three_reaction_atomic_conservation(self):
        for ins, outs in REACTIONS:
            self.assertEqual(elements(ins), elements(outs))

    def test_guarded_reaction_path(self):
        stock = {"H2O": 4, "H2": 0, "O2": 0, "CO2": 1, "CH4": 0}
        initial = elements(stock)
        stock = chemical_step(stock, REACTIONS[0])
        stock = chemical_step(stock, REACTIONS[0])
        stock = chemical_step(stock, REACTIONS[1])
        stock = chemical_step(stock, REACTIONS[2])
        self.assertEqual(elements(stock), initial)

    def test_insufficient_feed_refused(self):
        with self.assertRaises(ValueError):
            chemical_step({"H2O": 1}, REACTIONS[0])

    def test_kwh_conversion(self):
        self.assertEqual(1 * 3600000, 3600000)
        self.assertEqual(15 * 3600000, 54000000)

    def test_engine_no_substitution_threshold(self):
        self.assertEqual(
            engine_diesel(100, Fraction(35, 100), Fraction(50, 100), 0, 0),
            70
        )

    def test_h2_sabatier_allocated_once(self):
        produced, direct, methanated, stored, vented = 20, 10, 2, 2, 0
        self.assertEqual(produced, direct + 4 * methanated + stored + vented)

    def test_substitution_alone_cannot_save_with_loss(self):
        initial = Fraction(100)
        electricity = Fraction(15)
        h2_energy = Fraction(105, 10)
        assisted = engine_diesel(100, Fraction(35, 100),
                                 Fraction(35, 100), h2_energy, 0)
        self.assertEqual(assisted, Fraction(895, 10))
        self.assertGreater(assisted + electricity, initial)

    def test_interval_guarantee(self):
        self.assertTrue(guaranteed_saving(99, 83, 15))
        for baseline in range(99, 102):
            for assisted in range(80, 84):
                for electricity in range(13, 16):
                    self.assertLess(assisted + electricity, baseline)
        self.assertFalse(guaranteed_saving(99, 85, 15))

    def test_carbon_path_balances(self):
        steps = [CarbonStep(100, 0, 80, 20),
                 CarbonStep(80, 0, 64, 16),
                 CarbonStep(64, 0, 51, 13)]
        for s in steps:
            s.validate()
        self.assertEqual(steps[0].before + sum(s.makeup for s in steps),
                         steps[-1].after + sum(s.emitted for s in steps))

    def test_cyclic_carbon_requires_makeup(self):
        s = CarbonStep(100, 20, 100, 20)
        s.validate()
        self.assertEqual(s.makeup, s.emitted)

    def test_kwh_is_energy_not_power(self):
        # 15 kWh cannot be inferred from 15 volts without current and time.
        voltage, current, hours = Fraction(15), Fraction(10), Fraction(2)
        energy_kwh = voltage * current * hours / 1000
        self.assertEqual(energy_kwh, Fraction(3, 10))


class PhysicalSteelmanIdentificationTests(unittest.TestCase):
    """Synthetic falsification tests; NOT observed device results."""

    def test_same_diesel_and_output_different_mechanism(self):
        # Candidate A: F=70, H=0, eta=1/2 gives W=35.
        # Candidate B: F=70, H=10, eta=7/16 also gives W=35.
        self.assertEqual(Fraction(1, 2) * 70, Fraction(35))
        self.assertEqual(Fraction(7, 16) * (70 + 10), Fraction(35))
        self.assertNotEqual(Fraction(1, 2), Fraction(7, 16))
        # Diesel and output alone cannot identify combustion mechanism.

    def test_30_percent_claim_with_external_hydrogen(self):
        diesel = engine_diesel(
            100, Fraction(35, 100), Fraction(70, 161),
            Fraction(21, 2), 0
        )
        self.assertEqual(diesel, Fraction(70))
        self.assertEqual(diesel + Fraction(15), Fraction(85))
        self.assertEqual(Fraction(21, 2) / Fraction(15), Fraction(7, 10))

    def test_genuinely_tiny_hydrogen_requires_high_efficiency(self):
        # F1 = 70; H = 1; W = 35: eta = 35/71 ~= 49.3%.
        eta = Fraction(35, 71)
        self.assertEqual(eta * (70 + 1), 35)
        self.assertGreater(eta, Fraction(49, 100))

    def test_hydrogen_oxygen_interaction_contrast(self):
        # Synthetic factorial data, matched output assumed.
        no_gases, hydrogen_only, oxygen_only, combined = 100, 92, 94, 80
        extra_synergy = hydrogen_only + oxygen_only - no_gases - combined
        self.assertEqual(extra_synergy, 6)
        self.assertNotEqual(extra_synergy, 0)
        # These numbers do NOT imply a real causal interaction.

    def test_heat_assisted_input_boundary(self):
        # H=12 output is NOT constrained by electricity-only input of 10:
        # there is 5 energy units of imported heat and 3 rejected units.
        electricity, imported_heat, hydrogen, rejects = 10, 5, 12, 3
        self.assertEqual(electricity + imported_heat, hydrogen + rejects)
        self.assertGreater(hydrogen, electricity)
        self.assertLess(hydrogen, electricity + imported_heat)

    def test_similar_diesel_saving_not_same_net_input(self):
        # Independently metered auxiliaries affect net performance.
        fossil0, fossil1 = 100, 70
        self.assertTrue(fossil1 + 15 < fossil0)
        self.assertFalse(fossil1 + 35 < fossil0)

if __name__ == "__main__":
    unittest.main(verbosity=2)
