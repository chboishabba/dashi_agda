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
import exotic_topology_pl_stable_stars as stable
import exotic_topology_power_36_tight_nonpromotion as power
import exotic_topology_genus_zero_sphere_caps as cap
import exotic_topology_balanced_ternary_pl as balanced
import exotic_topology_cantor_cylinder_orientation as orientation
import exotic_topology_braid_crosspr_discriminator as braid
import exotic_topology_cantor_measure_obstruction as measure
# Native scripts are owned upstream by horned-sphere PR #1244.
import alexander_horned_c3_explicit_open_cover as original_cover
import alexander_horned_c3_pierced_shell_product as original_shell
import alexander_horned_c3_equivariant_basing_paths as original_basing
import alexander_horned_c3_same_cover_discriminator as original_cover_bidi
import alexander_horned_c3_clopen_spatial_realization as original_clopen

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


    def test_parent_1244_equivariant_central_basing_paths_source(self):
        result = original_basing.certify()
        self.assertEqual(result['status'], 'PASS')
        self.assertEqual(result['rational_checks'], 303)
        self.assertFalse(result['source_satellite_pi1_equivalence'])
        self.assertFalse(result['lean_kernel_checked'])

    def test_parent_1244_same_cover_tame_wild_collision(self):
        result = original_cover_bidi.audit()
        self.assertEqual(result['status'], 'PASS')
        self.assertTrue(result['good_open_cover'])
        self.assertEqual(result['same_cut_tame_wild_collision'],
                         'indistinguishable to this checker')
        self.assertEqual(result['symbolic_shell_identities'], 5)
        self.assertFalse(result['geometric_satellite_pi1_verified'])
        self.assertFalse(result['infinite_wild_embedding_machine_certified'])


    def test_real_two_pants_balanced_ternary_frontiers_and_complements(self):
        proof = balanced.audit(depth=3)
        self.assertEqual(
            [item["boundary_count"] for item in proof["stages"]],
            [1, 3, 9, 27])
        self.assertEqual(
            [item["new_attached_components"] for item in proof["stages"][:3]],
            [1, 3, 9])
        self.assertTrue(all(item["vertex_links_verified"] for item in proof["stages"]))
        self.assertEqual(proof["physical_pants_per_old_frontier"], 2)
        self.assertEqual(proof["one_to_three_cobordism_euler"], -2)
        self.assertFalse(proof["topological_infinite_end_space_homeomorphism_proved"])
        self.assertFalse(proof["agda_or_lean_kernel_verified"])

    def test_balanced_zero_is_a_distinct_third_ending(self):
        m = balanced.audit(depth=1)
        self.assertEqual(m["stages"][-1]["boundary_count"], 3)
        self.assertNotEqual(balanced.CODE[-1], balanced.CODE[0])
        self.assertNotEqual(balanced.CODE[0], balanced.CODE[1])
        self.assertEqual(balanced.DIGIT369, {-1:3, 0:6, 1:9})
        self.assertIsNone(balanced.decode_complete_binary_word((1,)))

    def test_reused_369_prefix_code_is_the_same_balanced_code(self):
        for t, digit in ((-1, "3"), (0, "6"), (1, "9")):
            self.assertEqual(
                balanced.CODE[t],
                tuple(int(x) for x in codec.CODE[digit]))
        for n in range(5):
            from itertools import product
            for word in product(balanced.BRANCHES, repeat=n):
                encoded = balanced.encode_balanced_word(word)
                self.assertEqual(
                    balanced.decode_complete_binary_word(encoded),
                    word)
                self.assertEqual("".join(map(str, encoded)),
                                 codec.encode(tuple(str(balanced.DIGIT369[t])
                                                    for t in word)))

    def test_one_pants_does_not_suffice_for_three_outgoing_boundaries(self):
        stage = lineage.mark_initial(pl.disk(), [()])
        pants = pl.sphere_with_holes(3)
        one = lineage.attach(stage, pants, (), ((-1,), ("aux",)))
        self.assertEqual(one.verify((0, 2))["boundaries"], 2)
        self.assertNotIn((0,), one.frontier)
        self.assertNotIn((1,), one.frontier)
        self.assertNotEqual(set(one.frontier), {(-1,), (0,), (1,)})

    def test_parent_latest_tame_cantor_endpoint_clopen_not_ambient_open(self):
        receipt = original_clopen.audit(max_depth=4)
        self.assertEqual(receipt['status'], 'PASS')
        self.assertEqual(receipt['checked_binary_prefixes'], 31)
        self.assertEqual(receipt['sector_prefix_combinations'], 93)
        self.assertTrue(receipt['clopen_on_endpoint_image'])
        self.assertFalse(receipt['clopen_in_ambient_R3'])
        self.assertFalse(receipt['Hatcher_wild_exterior_pi1_proved'])
        self.assertFalse(receipt['linked_horn_ambient_embedding_proved'])


    def test_native_balanced_27_cube_same_set_not_same_graph(self):
        result = balanced.depth_three_cube_sibling_nonpromotion()
        self.assertEqual(result["same_underlying_label_count"], 27)
        self.assertEqual(result["native_cube_grid_edges"], 54)
        self.assertEqual(result["optional_parent_sibling_pairs"], 27)
        self.assertEqual(result["shared_pairs"], 18)
        self.assertEqual(result["sibling_non_grid_pairs"], 9)
        self.assertEqual(result["grid_non_sibling_pairs"], 36)
        self.assertFalse(result["cube_graph_equivalence_claim"])
        self.assertFalse(result["surface_homeomorphism_claim"])


    def test_every_old_pl_vertex_becomes_interior_and_star_stabilises(self):
        result = stable.audit(two_step_windows=2)
        self.assertTrue(result["status"].startswith("PASS"))
        self.assertTrue(result["same_object_triangle_transport"])
        self.assertFalse(result["infinite_pl_colimit_proved"])
        self.assertFalse(result["richards_end_space_homeomorphism_proved"])
        self.assertFalse(result["kernel_verified"])
        for family in ("cantor", "loch", "jacob", "balanced_ternary"):
            self.assertEqual(len(result["families"][family]), 2)
            self.assertTrue(all(
                witness["all_old_vertices_interior_after_one_stage"] and
                witness["all_old_vertex_stars_stable_after_two_stages"]
                for witness in result["families"][family]
            ))

    def test_old_pl_star_validation_rejects_incorrect_embedding(self):
        old, piece = stable.initial("cantor")
        mid, _, old_to_mid = stable.transition(old, piece, "cantor")
        later, _, mid_to_later = stable.transition(mid, piece, "cantor")
        wrong = {v: 0 for v in old_to_mid}
        with self.assertRaises(AssertionError):
            stable.verify_stable_old_stars(
                old, mid, later, wrong, mid_to_later)


    def test_power_2025_existence_not_this_handled_pl_triangulation(self):
        result = power.audit()
        self.assertEqual(
            [s["maxwell_3V_minus_E"] for s in result["families"]["loch"]],
            [6, 0, -6])
        self.assertEqual(
            [s["maxwell_3V_minus_E"] for s in result["families"]["jacob"]],
            [6, -6, -18])
        self.assertTrue(
            result["source_theorem_is_existence_not_all_triangulations"])
        self.assertFalse(result["actual_selected_triangs_36_tight_verified"])
        for name in ("loch", "jacob"):
            self.assertTrue(all(
                s["violates_full_graph_36_sparsity_if_below_6"]
                for s in result["families"][name][1:]))

    def test_global_maxwell_six_does_not_certify_subgraph_sparsity(self):
        result = power.audit()
        for name in ("cantor","balanced_ternary"):
            self.assertTrue(all(
                s["maxwell_3V_minus_E"] == 6
                for s in result["families"][name]))
        self.assertTrue(result[
            "full_graph_maxwell_eq_6_does_not_prove_sparse_subgraphs"])
        self.assertFalse(result["actual_selected_triangs_36_tight_verified"])


    def test_euler_maxwell_all_genus_selected_pl_stage_identity(self):
        result = power.audit()
        self.assertTrue(result["euler_maxwell_identity_verified_on_source_meshes"])
        for name, stages in result["families"].items():
            for stage in stages:
                self.assertTrue(stage["all_boundary_loops_triangular"])
                self.assertTrue(stage["euler_maxwell_genus_identity"])
                self.assertEqual(
                    stage["maxwell_3V_minus_E"],
                    6 - 6*stage["genus"])
                self.assertEqual(
                    stage["boundary_total_edge_length"],
                    3*(1 if name == "loch" else
                       2 if name == "jacob" else
                       (2**stage["depth"] if name == "cantor"
                        else 3**stage["depth"])))


    def test_positive_depth_cantor_and_trit_have_same_graph_spherical_caps(self):
        result = cap.audit(depth=2)
        self.assertTrue(result["same_graph_spherical_caps_verified"])
        self.assertTrue(result["classical_planar_edge_bound_required_for_36_tight"])
        self.assertFalse(result["lean_agda_kernel_verified"])
        for family, expected in (("cantor", [1,2,4]),
                                 ("balanced_ternary", [1,3,9])):
            stages = result["families"][family]
            self.assertEqual([x["boundary_count"] for x in stages], expected)
            self.assertEqual([x["maxwell"] for x in stages], [6,6,6])
            self.assertTrue(all(
                x["planarity_witness"] == "same-graph explicit simplicial 2-sphere cap"
                for x in stages[1:]))

    def test_single_triangle_disk_cannot_be_capped_as_duplicate_simplex(self):
        with self.assertRaises(AssertionError):
            cap.cap_boundary_triangles(pl.disk())
        self.assertEqual(cap.audit(depth=1)["families"]["cantor"][0][
            "planarity_witness"], "K3 planar by direct three-vertex embedding")

    def test_positive_genus_handle_cannot_be_spherical_capped(self):
        # The same cap operation must reject positive-genus source stages:
        # filling the triangular boundary does not remove handles.
        handle, piece = complement.initial("loch")
        handled, _ = complement.transition(handle, piece, "loch")
        with self.assertRaises(AssertionError):
            cap.cap_boundary_triangles(handled.mesh)

if __name__ == '__main__': unittest.main()
