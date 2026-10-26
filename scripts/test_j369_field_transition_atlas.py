#!/usr/bin/env python3
import importlib.util
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).with_name('j369_field_transition_atlas.py')
spec = importlib.util.spec_from_file_location('atlas', SCRIPT)
atlas = importlib.util.module_from_spec(spec)
spec.loader.exec_module(atlas)


class J369FieldTransitionAtlasTest(unittest.TestCase):
    def test_prime_power_and_bracket_196830(self):
        self.assertEqual(atlas.prime_power(196831), (196831, 1))
        self.assertEqual(atlas.bracket_prime_powers(196830), (196817, 196831))

    def test_ticket_numeric_candidates(self):
        self.assertEqual(atlas.frobenius_orbit_count(2, 2), 3)
        self.assertEqual(atlas.frobenius_orbit_count(3, 2), 6)
        self.assertEqual(atlas.frobenius_orbit_count(2, 4), 6)
        self.assertEqual(atlas.frobenius_orbit_count(4, 2), 10)
        self.assertEqual(atlas.frobenius_orbit_count(5, 2), 15)
        self.assertEqual(atlas.frobenius_orbit_count(3, 4), 24)
        self.assertEqual(atlas.frobenius_orbit_count(4, 3), 24)
        self.assertEqual(atlas.prime_power(81), (3, 4))
        self.assertEqual(atlas.prime_power(243), (3, 5))
        self.assertEqual(atlas.prime_power(729), (3, 6))
        self.assertEqual(atlas.prime_power(811), (811, 1))
        c81 = atlas.numeric_candidates(81)
        self.assertTrue(any(t == 'T5' and m.get('subfield_sizes') == [3, 9, 81] for _, t, _, m in c81))
        c24 = atlas.numeric_candidates(24)
        self.assertTrue(any(t == 'T5' and m.get('subfield_sizes') == [3, 9, 81] for _, t, _, m in c24))

    def test_mass18_legacy_slice_is_exactly_1330_nodes_and_edges(self):
        states = atlas.legacy_states_exact_mass(18)
        self.assertEqual(len(states), 1330)
        state_set = set(states)
        edges = [(s, atlas.legacy_first_enabled_step(s)) for s in states]
        self.assertEqual(len(edges), 1330)
        self.assertTrue(all(t in state_set for _, t in edges))

    def test_legacy_transition_semantics_match_agda_priority(self):
        self.assertEqual(atlas.legacy_first_enabled_step((1, 1, 0, 0)), (0, 1, 1, 0))
        self.assertEqual(atlas.legacy_first_enabled_step((0, 1, 1, 0)), (0, 1, 0, 1))
        self.assertEqual(atlas.legacy_first_enabled_step((0, 1, 0, 1)), (1, 1, 0, 0))
        self.assertEqual(atlas.legacy_first_enabled_step((0, 1, 0, 0)), (1, 0, 0, 0))

    def test_generated_table_covers_authoritative_carriers(self):
        rows = atlas.field_bracket_rows(atlas.CARRIERS)
        self.assertEqual([r['n'] for r in rows], list(atlas.CARRIERS))
        row80 = next(r for r in rows if r['n'] == 80)
        self.assertEqual((row80['below'], row80['above'], row80['multiplicative_upper']), (79, 81, 81))
        row196830 = next(r for r in rows if r['n'] == 196830)
        self.assertEqual((row196830['below'], row196830['above'], row196830['multiplicative_upper']), (196817, 196831, 196831))

    def test_full_generation_has_numeric_firewall_and_svg_outputs(self):
        with tempfile.TemporaryDirectory() as td:
            out = Path(td)
            manifest = atlas.generate(out, 18, 37)
            self.assertEqual(manifest['legacy_nodes'], 1330)
            self.assertEqual(manifest['legacy_edges'], 1330)
            self.assertEqual(manifest['grid_rows'], 36)
            self.assertEqual(manifest['grid_displacement_vector_count'], 233)
            self.assertFalse(manifest['recognition_claimed'])
            self.assertFalse(manifest['t5_subfield_object_shape_inferred'])
            for name in (
                'fieldBracketTable.csv', 'fieldCandidates.csv', 'atlasManifest.json',
                'fieldRelationGraph.svg', 'legacyMass18TransitionGraph.svg',
                'legacyMass18EdgeDensity.svg', 'legacyMass18Transitions.csv',
                'OggSSPFiniteFieldBracketGenerated.agda'):
                self.assertTrue((out / name).exists(), name)


if __name__ == '__main__':
    unittest.main()
