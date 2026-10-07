#!/usr/bin/env python3
import importlib.util
import unittest
from pathlib import Path

SCRIPT = Path(__file__).with_name('j369_kernel_field_recognition.py')
spec = importlib.util.spec_from_file_location('recognition', SCRIPT)
recognition = importlib.util.module_from_spec(spec)
spec.loader.exec_module(recognition)


class J369KernelFieldRecognitionTest(unittest.TestCase):
    def test_selected_irreducible_presentations(self):
        for d in (4, 5, 6):
            model = recognition.model_for_degree(d)
            self.assertTrue(recognition.is_irreducible(model.modulus))
            self.assertEqual(model.order, 3 ** d)

    def test_every_nonzero_element_has_inverse(self):
        for d in (4, 5, 6):
            model = recognition.model_for_degree(d)
            one = model.one
            for x in model.elements:
                if x != model.zero:
                    self.assertEqual(model.mul(x, model.inv(x)), one)

    def test_negation_matches_scalar_minus_one(self):
        for d in (4, 5, 6):
            model = recognition.model_for_degree(d)
            minus_one = model.from_int(2)
            for x in model.elements:
                self.assertEqual(model.neg(x), model.mul(minus_one, x))

    def test_frobenius_and_negation_profiles(self):
        expected_frobenius = {
            4: {1: 3, 2: 3, 4: 18},
            5: {1: 3, 5: 48},
            6: {1: 3, 2: 3, 3: 8, 6: 116},
        }
        expected_negation_nonzero = {
            4: {2: 40},
            5: {2: 121},
            6: {2: 364},
        }
        for d in (4, 5, 6):
            model = recognition.model_for_degree(d)
            self.assertEqual(recognition.orbit_profile(model.elements, model.frobenius), expected_frobenius[d])
            nonzero = [x for x in model.elements if x != model.zero]
            self.assertEqual(recognition.orbit_profile(nonzero, model.neg), expected_negation_nonzero[d])

    def test_k4_puncture_has_exactly_80_elements_and_cyclic_field_group(self):
        model = recognition.model_for_degree(4)
        nonzero = [x for x in model.elements if x != model.zero]
        self.assertEqual(len(nonzero), 80)
        generator = recognition.find_primitive_element(model)
        self.assertEqual(recognition.multiplicative_order(model, generator), 80)

    def test_k4_gf9_subfield_is_explicit_linear_k2_image(self):
        model = recognition.model_for_degree(4)
        fixed = {x for x in model.elements if model.pow(x, 9) == x}
        image = set(recognition.k4_gf9_linear_image())
        self.assertEqual(len(fixed), 9)
        self.assertEqual(image, fixed)
        prefix = {(a, b, 0, 0) for a in range(3) for b in range(3)}
        self.assertNotEqual(prefix, fixed)
        for x in image:
            for y in image:
                self.assertIn(model.add(x, y), image)
                self.assertIn(model.mul(x, y), image)

    def test_existing_heisenberg_translations_are_kernel_f3_addition(self):
        self.assertTrue(recognition.heisenberg_additive_intertwiner_verified())

    def test_additive_negation_structure_does_not_select_unique_multiplication(self):
        for d in (4, 5, 6):
            model = recognition.model_for_degree(d)
            self.assertTrue(recognition.coordinate_swap_preserves_addition_negation(model))
            witness = recognition.multiplication_noncanonicity_witness(model)
            a = tuple(witness['left']); b = tuple(witness['right'])
            self.assertNotEqual(model.mul(a, b), recognition.conjugated_multiply(model, a, b))

    def test_row_major_legacy_embeddings_do_not_produce_twelve_vectors(self):
        scan = recognition.scan_row_major_displacements(total_mass=18, min_cols=2, max_cols=200)
        self.assertEqual(scan['node_count'], 1330)
        self.assertEqual(scan['matching_12_vector_columns'], [])
        self.assertEqual(scan['minimum_vector_count'], 196)
        self.assertEqual(scan['minimum_vector_columns'], [173, 189])

    def test_full_signed_weave_frontier_is_narrowed_to_projection(self):
        frontier = recognition.full_signed_weave_frontier()
        self.assertEqual(frontier['lane_count'], 15)
        self.assertTrue(frontier['pointed_lane_to_full_valuation_paid'])
        self.assertTrue(frontier['canonical_total_program_counter_machine_paid'])
        self.assertFalse(frontier['machine_to_rich_signed_state_projection_paid'])
        self.assertFalse(frontier['canonical_total_step_over_summary_state_alone_found'])
        self.assertFalse(frontier['full_rich_signed_transition_graph_claimed'])


if __name__ == '__main__':
    unittest.main()
