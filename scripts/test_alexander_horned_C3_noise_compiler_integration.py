#!/usr/bin/env python3
"""Cross-check the exact noise law on the REAL horn-word compiler.

Unlike the synthetic identity-product audit, this expands the existing
Hatcher commutator words and uses the repository's 2I labels and gate
noise implementation. A conservative bound avoids brittle fixed-seed
pointwise expectations. No hardware or geometric-flatness claim.
"""
import math
import unittest

import alexander_horned_c3_finite_SU2_gauge_simulator as gauge
import alexander_horned_c3_independent_noise_envelope as envelope


class ExistingHornCompilerNoiseChecks(unittest.TestCase):
    def test_real_recursive_horn_word_mean(self):
        sigma=4.0
        trials=500
        result=gauge.simulate(depth=3,trials=trials,shots=25,
                              sigma=sigma,seed=20261025)
        # Bounded independent per-trial halftraces; bound on the sample
        # mean, not the angle-noise distribution or deterministic words.
        radius=math.sqrt(2*math.log(2000)/trials)
        for row in result["rows"]:
            d=row["depth"]
            self.assertEqual(row["loop_gates"],3*4**d)
            self.assertEqual(row["ideal_halftrace"],-1)
            expected=envelope.expected_halftrace(d,sigma)
            self.assertLess(abs(row["noisy_halftrace"]-expected),radius)
            # Readout includes independent Bernoulli shot noise.
            self.assertLess(abs(row["observed_halftrace"]-expected),radius)

    def test_signal_budget_monotone(self):
        for d in range(6):
            self.assertAlmostEqual(
                envelope.max_sigma_degrees(d+1,0.9),
                envelope.max_sigma_degrees(d,0.9)/2,places=12)
            self.assertGreater(
                envelope.expected_halftrace(d+1,1.5),
                envelope.expected_halftrace(d,1.5))


if __name__=="__main__":
    unittest.main(verbosity=2)
