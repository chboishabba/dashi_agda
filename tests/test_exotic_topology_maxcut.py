"""Focused reproducible regression checks for source-bound exotic topology.

No assertion in these tests claims Agda kernel or geometric topology authority.
"""
from pathlib import Path
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
SCRIPTS=ROOT/'scripts' if (ROOT/'scripts').exists() else ROOT
sys.path.insert(0,str(SCRIPTS))

import exotic_topology_exact_models as models
import exotic_topology_surface_exhaustions as exhaustions
import exotic_topology_warsaw_contour as warsaw
import exotic_topology_cw_donor_reuse as cw
import exotic_topology_binary_ternary_pants as codec
import exotic_topology_pl_surface_gluings as pl
import exotic_topology_pl_frontier_lineage as lineage
import exotic_topology_pl_complement_components as complement
import exotic_topology_cantor_cylinder_orientation as orientation
import exotic_topology_braid_crosspr_discriminator as braid
import exotic_topology_cantor_measure_obstruction as measure
# Native scripts are owned upstream by horned-sphere PR #1244.
import alexander_horned_c3_explicit_open_cover as original_cover
import alexander_horned_c3_pierced_shell_product as original_shell

class ExoticMaxCutTests(unittest.TestCase):
    def test_whitney_real_parametric_image_caution(self):
        r=models.whitney()
        self.assertEqual(r['implicit_residual'],'0')
        self.assertFalse(r['negative_axis_in_real_parametric_image'])

    def test_ida_klein_seam(self):
        r=models.ida_seam()
        self.assertEqual(r['seam_residuals'],['0','0','0'])
        self.assertFalse(r['global_immersion_verified'])

    def test_simons_no_false_minimality(self):
        self.assertFalse(models.simons_cone()['minimality_proved'])

    def test_finite_surface_stages(self):
        for family,data in exhaustions.audit().items():
            self.assertEqual(data['checked_depths'],13)
            self.assertFalse(data['full_surface_constructed'])
        self.assertEqual(exhaustions.audit()['cantor_tree']['last_boundary_count'],4096)

    def test_warsaw_does_not_pretend_to_compute_homotopy(self):
        r=warsaw.audit()
        self.assertFalse(r['weak_homotopy_groups_computed'])
        self.assertFalse(r['homotopy_type_computed'])

    def test_cw_chain_torsion_rejects_rational_only_equivalence(self):
        point=cw.single_vertex('point',0,0,[],(1,0,0)).verify()
        rp2=cw.single_vertex('RP2',1,1,[[2]],(1,0,0),(2,)).verify()
        self.assertEqual(point['betti'],rp2['betti'])
        self.assertNotEqual(point['h1_torsion'],rp2['h1_torsion'])

    def test_cw_bad_boundary_detected(self):
        bad=cw.CW2('invalid boundary',2,1,1,((-1,),(1,)),((1,),),(1,0,0))
        with self.assertRaises(AssertionError): bad.verify()

    def test_cantor_binary_ternary_bijection_is_not_measure_parity(self):
        r=codec.verify(7)
        self.assertEqual(r['levels'][7]['n_cylinders'],2187)
        self.assertFalse(r['uniform_ternary_measure_preserved'])
        self.assertEqual(r['weights'],{'3':'1/2','6':'1/4','9':'1/4'})
        self.assertIsNone(codec.decode('1'))


    def test_actual_finite_pl_surface_vertex_links(self):
        result = pl.audit(4)
        self.assertIn('FINITE PL GEOMETRY ONLY', result['status'])
        self.assertEqual([x['boundaries'] for x in result['families']['cantor']], [1,2,4,8,16])
        self.assertEqual([x['genus'] for x in result['families']['loch']], [0,1,2,3,4])
        self.assertEqual([x['genus'] for x in result['families']['jacob']], [0,2,4,6,8])
        self.assertTrue(all(x['vertex_links_verified'] for family in result['families'].values() for x in family))

    def test_wrongly_oriented_shared_edge_rejected(self):
        with self.assertRaises(AssertionError):
            pl.inspect(pl.Mesh([(0,1,2),(0,1,3)], 'same-orientation-shared-edge'))


    def test_exact_geometric_frontier_lineage(self):
        result = lineage.audit(4)
        self.assertTrue(result['status'].startswith('PASS'))
        for depth, stage in enumerate(result['families']['cantor']):
            self.assertEqual(len(stage['frontier_keys']), 2 ** depth)
            self.assertEqual(
                set(stage['frontier_keys']),
                {tuple(int(x) for x in format(k, '0%db' % depth)) if depth
                 else () for k in range(2 ** depth)})
        self.assertEqual(result['families']['loch'][-1]['genus'], 4)
        self.assertEqual(result['families']['jacob'][-1]['genus'], 8)

    def test_wrong_lineage_even_with_correct_frontier_count(self):
        # Same numerical count but an old branch did not split:
        # the label (1,) persists while (0,) is over-refined.
        old = {(0,), (1,)}
        bad = {(0, 0), (0, 1), (0, 0, 0), (1,)}
        self.assertEqual(len(bad), 2 * len(old))
        self.assertNotEqual(bad, {p + (b,) for p in old for b in (0, 1)})


    def test_real_wrong_lineage_while_geometric_manifold_still_valid(self):
        # Construct an ACTUAL all-valid triangulated mesh with four
        # boundaries but the wrong ancestry: split the left child
        # repeatedly, leaving the right child unsplit.
        pants = pl.sphere_with_holes(3)
        wrong = lineage.mark_initial(pl.disk(), [()])
        wrong = lineage.attach(wrong, pants, (), ((0,), (1,)))
        wrong = lineage.attach(wrong, pants, (0,), ((0, 0), (0, 1)))
        wrong = lineage.attach(wrong, pants, (0, 0),
                               ((0, 0, 0), (0, 0, 1)))
        self.assertEqual(wrong.verify((0, 4))['boundaries'], 4)
        self.assertEqual(len(wrong.frontier), 4)
        self.assertNotEqual(
            set(wrong.frontier),
            {(0, 0), (0, 1), (1, 0), (1, 1)})
        self.assertIn((1,), wrong.frontier)


    def test_reuse_1239_real_b3_vs_endpoints_and_modular_sign(self):
        receipt = braid.audit()
        self.assertTrue(receipt['B3_braid_relation'])
        self.assertTrue(receipt['endpoint_projection_full_twist_identity'])
        self.assertEqual(receipt['SL2Z_full_twist'], '-I')
        self.assertEqual(receipt['SL2Z_double_full_twist'], 'I')
        self.assertEqual(receipt['B3_double_full_twist_exponent_sum'], 12)
        self.assertFalse(receipt['ambient_link_or_isotopy_claim'])

    def test_no_measure_preserving_binary_uniform_ternary_cantor_homeomorphism(self):
        receipt = measure.audit()
        self.assertTrue(receipt['topological_homeomorphism_possible'])
        self.assertFalse(receipt['measure_preserving_homeomorphism_possible'])
        self.assertFalse(receipt['kernel_verified'])


    def test_reuse_current_horned_parent_explicit_cover_without_pi1_promotion(self):
        receipt = original_cover.exact_certificate()
        self.assertTrue(receipt['inner_strictly_inside_outer'])
        self.assertTrue(receipt['tube_meets_both_spherical_cuts_in_single_disk'])
        self.assertEqual(receipt['pair_intersections'],
                         'U_i intersect U_j = C for i != j')
        self.assertFalse(receipt['central_pi1_verified'])
        self.assertFalse(receipt['wild_embedding_verified'])

    def test_reuse_current_horned_parent_shell_stereographic_chart(self):
        receipt = original_shell.audit()
        self.assertEqual(receipt['exact_rational_samples'], 867)
        self.assertEqual(receipt['domain'], '(15/4,17/4) x open unit disk')
        self.assertFalse(receipt['global_topology_machine_proof'])


    def test_real_complement_components_follow_old_boundary_at_every_stage(self):
        result = complement.audit(max_depth=3)
        self.assertTrue(result['finite_pl_inclusion_and_complement_components'])
        self.assertFalse(result['richards_infinite_end_space_proved'])
        self.assertFalse(result['kernel_verified'])
        self.assertEqual(
            [r['components'] for r in result['families']['cantor']],
            [1, 2, 4])
        self.assertEqual(
            [r['new_boundaries'] for r in result['families']['cantor']],
            [2, 4, 8])
        self.assertEqual(
            [r['components'] for r in result['families']['loch']],
            [1, 1, 1])
        self.assertEqual(
            [r['components'] for r in result['families']['jacob']],
            [2, 2, 2])
        self.assertTrue(all(r['geometric_child_incidence_verified']
                            and r['same_object_old_inclusion']
                            for rs in result['families'].values() for r in rs))

    def test_complement_bridge_rejects_wrong_old_vertex_inclusion(self):
        old, piece = complement.initial('cantor')
        new, actual_map = lineage.attach(old, piece, (), ((0,), (1,)),
                                         with_transport=True)
        # An actual connected pants attachment exists, but claiming a
        # constant vertex map erases the embedded old simplices.
        bogus_map = {v: 0 for v in actual_map}
        with self.assertRaises(AssertionError):
            complement.verify_complement_components(
                old, new, bogus_map, 'cantor')

    def test_complement_bridge_rejects_wrong_geometric_lineage(self):
        old, piece = complement.initial('cantor')
        new, actual_map = lineage.attach(old, piece, (), ((0,), (1,)),
                                         with_transport=True)
        # Swapping or falsifying a child's literal boundary label
        # changes the consumer's expected parent/child incidence even
        # if the surface and all Euler data stay unchanged.
        original = new.frontier.pop((0,))
        new.frontier[(7,)] = original
        new.verify((0, 2))
        with self.assertRaises(AssertionError):
            complement.verify_complement_components(
                old, new, actual_map, 'cantor')


    def test_cantor_chronological_child_refines_actual_prefix_event(self):
        receipt = orientation.audit(max_depth=9)
        self.assertEqual(receipt['exact_prefix_child_cases'], 2046)
        self.assertTrue(receipt['append_children_are_chronological_refinements'])
        self.assertTrue(receipt['reverse_word_conjugates_append_to_prepend'])
        self.assertFalse(receipt['richards_end_space_homeomorphism_proved'])

    def test_original_prepended_mass_child_not_chronological_refinement(self):
        receipt = orientation.audit(max_depth=3)
        self.assertTrue(receipt['source_original_prepend_is_mass_consistent'])
        self.assertFalse(receipt['old_prepend_is_chronological_refinement'])
        self.assertTrue(receipt['original_source_unchanged'])
        self.assertFalse(receipt['agda_kernel_verified'])

if __name__ == '__main__': unittest.main()
