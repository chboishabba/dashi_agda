#!/usr/bin/env python3
"""Source-chart Burnside regression; does NOT authenticate original Monster words."""
import sys
import unittest
from pathlib import Path
from collections import Counter

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import monster3b_mixed8_linear_orbit_burnside as b


class Mixed8LinearOrbits(unittest.TestCase):
    def test_source_d4_relations_and_80(self):
        self.assertEqual(len(b.X), 80)
        self.assertEqual(len(b.Y), 8)
        for x in b.X:
            self.assertEqual(b.rotate(b.rotate(b.rotate(b.rotate(x)))), x)
            self.assertEqual(b.reflect(b.reflect(x)), x)
            self.assertEqual(b.reflect(b.rotate(b.reflect(x))),
                             b.rotate(b.rotate(b.rotate(x))))

    def test_d4_orbits_and_local_hom_counts(self):
        orbs = b.source_orbits()
        self.assertEqual(Counter(len(o) for _, o in orbs), {4: 8, 8: 6})
        homsizes = []
        for rep, orbit in orbs:
            choices = [(y, b.local_map(rep, y)) for y in b.Y]
            maps = [(y, m) for y, m in choices if m is not None]
            for y, mapping in maps:
                self.assertEqual(set(mapping), set(orbit))
            homsizes.append(len(maps))
        self.assertEqual(sorted(homsizes), [2]*8 + [8]*6)

    def test_source_linear_centralizer_and_target_action(self):
        auts = list(b.source_linear_automorphisms())
        self.assertEqual(len(auts), 48)
        self.assertEqual(len({mat for mat, _ in auts}), 48)
        for signs in ((1, 1), (1, 2), (2, 1), (2, 2)):
            self.assertEqual(len(set(b.target_automorphism(y, signs)
                                     for y in b.Y)), 8)
            for y in b.Y:
                self.assertEqual(b.target_automorphism(b.rotate(y), signs),
                                 b.rotate(b.target_automorphism(y, signs)))
                self.assertEqual(b.target_automorphism(b.reflect(y), signs),
                                 b.reflect(b.target_automorphism(y, signs)))

    def test_exact_burnside_and_nonpromotion(self):
        res = b.compute()
        self.assertEqual(res["balanced_maps"], 20_971_520)
        hist = {int(k): v for k, v in res["fixed_count_histogram"].items()}
        self.assertEqual(hist, {0: 174, 512: 16, 20_971_520: 2})
        self.assertEqual(res["fixed_point_sum"],
                         2*20_971_520 + 16*512)
        self.assertEqual(res["fixed_point_sum"] // 192, 218_496)
        self.assertEqual(res["orbits_source_linear_and_target_equivariant"],
                         218_496)
        self.assertFalse(res["authentic_monster_word_or_full_Heisenberg_intertwiner"])
        self.assertFalse(res["actual_suzuki_78_family_source_selected"])
        self.assertFalse(res["agda_kernel_checked"])


if __name__ == "__main__":
    unittest.main()
