#!/usr/bin/env python3
"""Numerical/combinatorial verification for the IIT / 369 max-cut.

This file is deliberately *not* a source/build checker. It never inspects Agda
text, imports, filenames, or theorem names. Formal completeness belongs to the
Agda aggregate and the Agda compiler.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

from iit4_finite_reference import (
    IIT4_2023,
    IIT4_2026,
    deterministic_model,
    directional_partitions,
    feedforward_three_cell_step,
    recurrent_three_cell_step,
    system_phi,
)
from iit4_structure_reference import big_phi, nonempty_relation_candidates, relation_phi_from_overlap
from iit_369_algebra_scan import algebra_summary
from iit_boolean_gate_minimal_sufficiency import scan as boolean_minimality_scan
from iit_hyperfabric_fixture_scan import fixture_summary
from iit_matched_fabric_gate_sweep import sweep_summary
from iit_pointed27_gluing_scan import gluing_summary
from iit_ternary_affine_minimal_sufficiency import scan as ternary_affine_scan
from iit_xor_369_stress_scan import stress_summary
from iit_xor_grid_calibration import calibration_summary
from iit_lattice_prime_power_audit import audit as prime_power_lattice_audit
from iit_j_coarse_fine_5cube_audit import audit as five_cube_fibre_audit
from iit_jfine_selected_punctured79_audit import audit as selected_punctured79_audit
from iit_projective_f9_pointed80_audit import audit as projective_pointed80_audit
from iit_pgl2_f9_720_audit import audit as pgl2_f9_audit
from iit_f81_f9_norm_inversion_audit import audit as f81_norm_inversion_audit
from iit_f81_f9_quadratic_tower_audit import audit as f81_same_tower_audit
from iit_jfine_four_one_four_s3_zeta_audit import audit as jfine_s3_audit
from iit_jfine_d4_s3_mixed_character_audit import audit as jfine_d4_s3_mixed_audit
from iit_jfine_heisenberg_four_pair_audit import audit as heisenberg_four_pair_audit
from iit_jfine_d4_symplectic_obstruction_audit import audit as d4_symplectic_audit
from iit_jfine_d4_heisenberg_h6_model_weld import audit as d4_h6_weld_audit
from iit_jfine_d4_single_line_orientation_bypass import audit as d4_line_bypass_audit
from iit_jfine_d4_oriented_c4_monster_necessary_bridge import audit as d4_c4_steelman_audit
from iit_jfine_h4_central_phase_fourier_intertwiner import audit as h4_fourier_weld_audit


def _xor2(a: int, b: int) -> int:
    return a ^ b


def _or2(a: int, b: int) -> int:
    return int(bool(a) or bool(b))


def _tri_xor(a: int, b: int) -> int:
    return (a + b) % 3


def _phi_values(model, version: str) -> list[float]:
    return sorted({round(system_phi(model, state, formalism=version)["phi_s"], 12) for state in model.states})


def verify_numeric_results() -> dict:
    assert len(directional_partitions(3)) == 54

    xor_model = deterministic_model(2, 3, recurrent_three_cell_step(_xor2))
    or_model = deterministic_model(2, 3, recurrent_three_cell_step(_or2))
    tri_model = deterministic_model(3, 3, recurrent_three_cell_step(_tri_xor))
    ff_model = deterministic_model(2, 3, feedforward_three_cell_step(_xor2))

    core = {
        "directional_partitions_3_units": len(directional_partitions(3)),
        "recurrent_xor_2023": _phi_values(xor_model, IIT4_2023),
        "recurrent_xor_2026": _phi_values(xor_model, IIT4_2026),
        "recurrent_or_2023": _phi_values(or_model, IIT4_2023),
        "recurrent_or_2026": _phi_values(or_model, IIT4_2026),
        "recurrent_trixor_2023": _phi_values(tri_model, IIT4_2023),
        "recurrent_trixor_2026": _phi_values(tri_model, IIT4_2026),
        "feedforward_xor_2023": _phi_values(ff_model, IIT4_2023),
    }
    assert core["recurrent_xor_2023"] == [2.0]
    assert core["recurrent_xor_2026"] == [0.0]
    assert core["recurrent_or_2023"] == [0.0, round(math.log2(4 / 3), 12), 2.0]
    assert core["recurrent_or_2026"] == [0.0]
    assert core["recurrent_trixor_2023"] == [round(math.log2(9), 12)]
    assert core["recurrent_trixor_2026"] == [0.0]
    assert core["feedforward_xor_2023"] == [0.0]

    boolean_minimality = boolean_minimality_scan()
    assert boolean_minimality["bipermutative_class"] == ["XOR", "XNOR"]
    assert boolean_minimality["essential_two_input_positive_all_states"] == ["XOR", "XNOR"]

    ternary_minimality = ternary_affine_scan()
    assert ternary_minimality["essential_two_input_count"] == 12
    assert ternary_minimality["bipermutative_count"] == 12
    assert ternary_minimality["positive_all_states_count"] == 12
    assert ternary_minimality["symmetric_affine_count"] == 6
    assert ternary_minimality["antisymmetric_affine_count"] == 6
    assert ternary_minimality["essential_all_state_phi_s"] == [round(math.log2(9), 12)]

    grid = calibration_summary()["recurrent_xor_grid_2x2"]
    assert grid["states_tested"] == 16
    assert grid["iit_4_0_2023"]["distinct_phi_s"] == [0.0, 0.5]
    assert grid["iit_4_0_2023"]["zero_phi_states"] == 12
    assert grid["iit_4_0_2026"]["distinct_phi_s"] == [0.0]

    matched = sweep_summary()
    fixed = matched["fixed_recurrent_fabric_vary_gate"]
    assert fixed["binary_xor"]["iit_4_0_2023"]["distinct_phi_s"] == [2.0]
    assert fixed["binary_or"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0, round(math.log2(4 / 3), 12), 2.0]
    assert fixed["binary_and"]["iit_4_0_2023"]["zero_phi_states"] == 6
    assert fixed["ternary_trixor"]["iit_4_0_2023"]["distinct_phi_s"] == [round(math.log2(9), 12)]
    topology = matched["fixed_binary_xor_vary_fabric"]
    assert topology["feedforward"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0]
    assert topology["recurrent_three_cell"]["iit_4_0_2023"]["distinct_phi_s"] == [2.0]
    assert topology["grid_2x2"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0, 0.5]

    algebra = algebra_summary()
    expected6 = round(math.log2(36), 12)
    expected9 = round(math.log2(81), 12)
    z6 = algebra["z6_cyclic"]
    s3 = algebra["s3_permutation"]
    z9 = algebra["z9_cyclic"]
    f3sq = algebra["f3_squared"]
    assert z6["iit_4_0_2023"]["distinct_phi_s"] == [expected6]
    assert s3["iit_4_0_2023"]["distinct_phi_s"] == [expected6]
    assert z9["iit_4_0_2023"]["distinct_phi_s"] == [expected9]
    assert f3sq["iit_4_0_2023"]["distinct_phi_s"] == [expected9]
    same_6_profile = z6["iit_4_0_2023"]["distinct_phi_s"] == s3["iit_4_0_2023"]["distinct_phi_s"]
    same_9_profile = z9["iit_4_0_2023"]["distinct_phi_s"] == f3sq["iit_4_0_2023"]["distinct_phi_s"]
    assert same_6_profile and same_9_profile

    fixtures = fixture_summary()["fixtures"]
    assert fixtures["open_xor_path"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0]
    assert fixtures["closed_xor_cycle"]["iit_4_0_2023"]["distinct_phi_s"] == [2.0]
    assert fixtures["xor_grid_2x2"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0, 0.5]
    assert fixtures["closed_trixor_cycle"]["iit_4_0_2023"]["distinct_phi_s"] == [round(math.log2(9), 12)]

    pointed = gluing_summary()
    assert pointed["carrier_size"] == 27
    assert pointed["strata"] == {"0_faces": 1, "1_face": 6, "2_faces": 12, "3_faces": 8}
    assert pointed["non_origin_count"] == 26
    assert pointed["total_point_face_incidences"] == 54
    assert pointed["face_count"] == 6
    assert pointed["each_face_size"] == 9
    assert pointed["pairwise_face_overlaps"] == 12
    assert pointed["each_edge_overlap_size"] == 3
    assert pointed["corner_face_triples"] == 8
    assert pointed["each_corner_triple_intersection_size"] == 1
    assert pointed["three_selected_cubie_choices"] == 19683

    relation_candidates = len(nonempty_relation_candidates(("d1", "d2", "d3")))
    relation_overlap_phi = relation_phi_from_overlap(0.12, 3, 2)
    composed_big_phi = big_phi([0.1, 0.2, 0.3], [0.05, 0.15])
    assert relation_candidates == 7
    assert abs(relation_overlap_phi - 0.08) < 1e-12
    assert abs(composed_big_phi - 0.8) < 1e-12

    stress = stress_summary()
    assert stress["binary_recurrent_xor"]["iit_4_0_2023"]["distinct_phi_s"] == [2.0]
    assert stress["binary_xor_grid_2x2"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0, 0.5]
    assert stress["ternary_recurrent_trixor"]["iit_4_0_2023"]["distinct_phi_s"] == [round(math.log2(9), 12)]
    assert stress["z6_recurrent_addition"]["iit_4_0_2023"]["distinct_phi_s"] == [expected6]
    assert stress["s3_recurrent_composition"]["iit_4_0_2023"]["distinct_phi_s"] == [expected6]
    assert stress["z9_recurrent_addition"]["iit_4_0_2023"]["distinct_phi_s"] == [expected9]
    assert stress["f3_squared_recurrent_addition"]["iit_4_0_2023"]["distinct_phi_s"] == [expected9]

    # Existing larger-grid scaling is checked independently of IIT-phi.
    lattice = prime_power_lattice_audit()
    assert len(lattice["rows"]) == 26
    def lattice_case(p, dim, n):
        return next(row for row in lattice["rows"]
                    if row["p"] == p and row["dim"] == dim and row["n"] == n)
    assert lattice_case(2, 2, 10)["rank"] == 90
    assert lattice_case(2, 3, 5)["rank"] == 125
    assert lattice_case(3, 2, 3)["rank"] == 9
    assert lattice_case(3, 3, 3)["rank"] == 18
    assert all(c["all_basis_vectors"] for c in
               lattice["prime_power_operator_certificates"])
    assert lattice["binary_2D_n3_F4_equals_F_on_delta"]
    assert lattice["binary_2D_n10_F128_delta_is_nonzero"]

    five_cube = five_cube_fibre_audit()
    assert five_cube["sites"] == 125
    assert five_cube["rank"] == 120
    assert five_cube["lost_kernel_dimensions"] == 5
    assert five_cube["retained_core_dimensions"] == 120
    assert five_cube["diagonal_coarse_profile_dimensions"] == 5
    assert five_cube["tested_basis_vectors"] == 125
    assert five_cube["eighty_step_equals_identity_minus_section_projection"]
    assert five_cube["coarse_fine_exact_reopening"]
    assert five_cube["not_identified_with_j_harmonic_9_or_19683"]

    selected = selected_punctured79_audit()
    assert selected["exhaustive_fine_codec_roundtrips"] == 19683
    assert selected["pointed_states"] == 196830
    assert selected["F81_nonzero_states"] == 80
    assert selected["inverse_exponent"] == 79
    assert selected["AGL1_F9_order"] == 72
    assert selected["5cube_minimal_retained_period"] == 80
    assert selected["5cube_eigenvalue_order_multiplicities"] == {
        0: 5, 8: 12, 16: 12, 40: 48, 80: 48}
    assert not selected["C5_natural_translation_into_C3xC3"]
    assert not selected["79_is_SSP15_prime"]

    projective = projective_pointed80_audit()
    assert projective["projective_line_F9_points"] == 10
    assert projective["ordinary_affine_points"] == 9
    assert projective["nonzero_vectors_per_line"] == 8
    assert projective["affine_part"] == 72
    assert projective["completion_fibre"] == 8
    assert projective["nonzero_source_roundtrip"] == 80
    assert projective["punctured_F81_count"] == 80
    assert not projective["original_modular_j_identification"]
    assert not projective["original_Monster_action_identified"]

    pgl = pgl2_f9_audit()
    assert pgl["group_order"] == 720
    assert pgl["affine_infinity_stabilizer_order"] == 72
    assert pgl["homogeneous_space_index"] == 10
    assert pgl["Singer_order10_cycle_lengths"] == [10]
    assert pgl["Singer_order5_cycle_lengths"] == [5, 5]
    assert pgl["order5_moves_completion_infinity"]
    assert not pgl["C5_in_affine_stabilizer"]

    f81_norm = f81_norm_inversion_audit()
    assert f81_norm["q_minus_two_inverse_exponent"] == 79
    assert f81_norm["subfield_F9_elements"] == 9
    assert f81_norm["norm_one_group_size"] == 10
    assert f81_norm["uniform_scalar_fibre_size"] == 8
    assert f81_norm["norm_one_frobenius_equals_inverse"]
    assert f81_norm["inverse_via_conjugate_over_norm"]
    assert f81_norm["inverse_involution_orbits"] == {"fixed":2, "pairs":4}
    f81_tower = f81_same_tower_audit()
    assert f81_tower["field_elements_bijectively_mapped"] == 81
    assert f81_tower["ordered_pairs_addition_checked"] == 6561
    assert f81_tower["ordered_pairs_multiplication_checked"] == 6561
    assert f81_tower["relative_Frobenius_9_equals_tower_conjugation"]
    assert f81_tower["relative_norm_10_equals_tower_norm"]

    jfine_s3 = jfine_s3_audit()
    assert jfine_s3["fine_size"] == 19683
    assert jfine_s3["raw_4_1_4_cardinality"] == 19683
    assert jfine_s3["all_fine_codec_roundtrips"] == 19683
    assert jfine_s3["checked_S3_gauge_actions"] == 118098
    assert jfine_s3["complex_irreps_fine"] == {
        "trivial": 3281, "sign": 3280, "standard_2d": 6561}
    assert jfine_s3["complex_irreps_pointed"] == {
        "trivial": 32810, "sign": 32800, "standard_2d": 65610}
    assert jfine_s3["pointed_C3_zeta_multiplicity_each"] == 65610
    assert jfine_s3["D4_edge_corner_natural_modules_inequivalent"]
    assert jfine_s3["D4_times_S3_orbits"] == 490
    assert jfine_s3["heisenberg_90_by_729_chart_roundtrips"] == 65610
    assert not jfine_s3["heisenberg_actual_Weyl_action_identified"]
    assert jfine_s3["D4_times_S3_orbit_histogram"] == {
        3: 1, 6: 6, 12: 17, 24: 122, 48: 344}
    assert jfine_s3["D4_times_S3_Burnside_numerator"] == 23520

    mixed = jfine_d4_s3_mixed_audit()
    assert mixed["fine_D4_by_valueS3_orbits"] == 490
    assert mixed["pointed_D4_by_valueS3_orbits"] == 4396
    assert mixed["source_fine_states"] == 19683
    assert mixed["source_pointed_states"] == 196830
    assert mixed["spatial_rowcol_S3_wreath_C2_order"] == 72
    assert mixed["spatial_72_by_valueS3_orbits"] == 84
    assert mixed["spatial_72_is_not_AGL1F9_72"]
    assert mixed["pointed_marker_moves"]
    assert mixed["D4_commutes_with_value_S3"]
    assert not mixed["original_Monster_action_intertwined"]

    h4 = heisenberg_four_pair_audit()
    assert h4["group_order"] == 19683
    assert h4["centre_order"] == 3
    assert h4["symplectic_quotient_order"] == 6561
    assert h4["exhaustive_elements"] == 19683
    assert h4["quotient_nonzero_witnesses_checked"] == 6560
    assert h4["H6_729_basis_splits_into_H4_81_blocks"] == 9
    assert h4["source_H6_zero_tail_embedding"]
    assert h4["global_C3_value_cycle_is_central_left_translation"]
    assert not h4["global_S3_value_sign_is_group_automorphism"]
    assert not h4["original_D4_mirror_preserves_chosen_cocycle"]
    assert not h4["source_monster_representation_intertwiner"]

    d4_symplectic = d4_symplectic_audit()
    assert d4_symplectic["all_rank_eight_forms_excluded"]
    assert d4_symplectic["original_GaugeFourOneFour_source_chart_roundtrips"] == 19683
    assert d4_symplectic["source_chart_D4_action_equivariant"]
    assert all(v["max_rank"] == 6 for v in d4_symplectic["multiplier_forms"].values())
    assert d4_symplectic["minimal_extra_dimensions"] == 2
    assert d4_symplectic["repaired_rank"] == 10
    assert d4_symplectic["source_restriction_rank"] == 6
    assert d4_symplectic["h6_sized_rank"] == 12
    assert d4_symplectic["d4_acts_symplectically_on_repair"]
    assert d4_symplectic["value_s3_reflection_cannot_lift_as_group_automorphism"]
    assert d4_symplectic["quadratically_corrected_value_anti_automorphism_generator_checks"] == 177147
    assert not d4_symplectic["actual_monster_intertwiner"]

    d4_h6_weld = d4_h6_weld_audit()
    assert d4_h6_weld["source_subspace_commutator_rank"] == 6
    assert d4_h6_weld["source_subspace_centre_order"] == 27
    assert d4_h6_weld["D4_H6_generator_group_law_checks"] == 338
    assert d4_h6_weld["basis_pair_checks"] == 144
    assert d4_h6_weld["H3_C3sq_nonlinear_irrep_degree"] == 27
    assert d4_h6_weld["source_H3_times_C3sq_concrete_generator_checks"] == 177147
    assert d4_h6_weld["chosen_H4_nonlinear_irrep_degree"] == 81
    assert d4_h6_weld["original_JFine_D4_centre_action_intertwined"]
    assert d4_h6_weld["source_D4_preserves_selected_repaired_group_cocycle"]
    assert d4_h6_weld["D4_simultaneous_translation_modulation_orthogonal"]
    assert not d4_h6_weld["D4_lift_needs_central_quadratic_correction"]
    assert d4_h6_weld["source_D4_repaired_group_generator_checks"] == 354294

    d4_line_bypass = d4_line_bypass_audit()
    assert d4_line_bypass["new_trits"] == 0
    assert d4_line_bypass["mirror_rank_one_operator_defect"] == 1
    assert d4_line_bypass["dual_mirror_rank_one_operator_defect"] == 1
    assert d4_line_bypass["dual_twisted_H4_automorphism_checks"] == 177147
    assert d4_line_bypass["dual_twisted_phase_D4_character"] == {
        "identity":65610, "half":162, "quarter":18,
        "axis":324, "diagonal":2916}
    assert d4_line_bypass["twisted_symplectic_rank"] == 8
    assert d4_line_bypass["twisted_D4_acts_by_H4_automorphisms"]
    assert not d4_line_bypass["source_geometric_reflection_preserved"]
    assert d4_line_bypass["relative_chart_roundtrips"] == 6561
    assert d4_line_bypass["D4_original_source_group_action_checks"] == 354294
    assert d4_line_bypass["fine_joint_orbits"] == 535
    assert d4_line_bypass["moving_marker_pointed_joint_orbits"] == 4576
    assert d4_line_bypass["zeta_D4_phase_character"] == {
        "identity": 65610, "half": 162, "quarter": 18,
        "axis": 2916, "diagonal": 324}
    assert not d4_line_bypass["actual_Monster_normalizer_same_object"]

    d4_c4_steelman = d4_c4_steelman_audit()
    assert d4_c4_steelman["quarter_operator_delta_rank"] == 2
    assert d4_c4_steelman["mirror_operator_delta_rank"] == 1
    assert d4_c4_steelman["nondegenerate_similitude_form_rank"] == 8
    assert d4_c4_steelman["D4_centre_multiplier_mirror"] == 2
    assert d4_c4_steelman["D4_H4_generator_product_checks"] == 354294
    assert d4_c4_steelman["D4_group_relations_checks"] == 59049
    assert d4_c4_steelman["zeta_phase_preserving_C4_character"] == {
        "identity":65610, "r":18, "r2":1458, "r3":18}
    assert d4_c4_steelman["necessary_3B_C4_character_match"]
    assert not d4_c4_steelman["actual_Monster_3B_D4_embedding_identified"]
    assert not d4_c4_steelman["character_match_is_sufficient_for_subgroup"]

    h4_fourier_weld = h4_fourier_weld_audit()
    assert h4_fourier_weld["source_phase_dimension"] == 65610
    assert h4_fourier_weld["target_phase_dimension"] == 65610
    assert h4_fourier_weld["source_regular_H4_zeta_copy_count"] == 810
    assert h4_fourier_weld["target_H6_Schrodinger_restricted_H4_copy_count"] == 810
    assert h4_fourier_weld["exact_fourier_gram_pairs"] == 6561
    assert h4_fourier_weld["source_to_Schrodinger_intertwiner_generator_checks"] == 59049
    assert not h4_fourier_weld["D4_normalizer_intertwiner"]
    assert not h4_fourier_weld["same_object_Monster_Wzeta_linear_recognition"]

    return {
        "contract": "iit_numeric_verification",
        "scope": "numeric_and_finite_combinatorial_only",
        "formal_source_or_agda_checks_performed": False,
        "full_ces_values_verified_here": False,
        "full_ces_oracle": "scripts/iit4_pyphi_oracle.py",
        "core": core,
        "boolean_minimality": boolean_minimality,
        "ternary_affine_minimality": ternary_minimality,
        "xor_grid": grid,
        "five_cube_relative_fibre": five_cube,
        "selected_punctured79": selected,
        "jfine_four_one_four_s3_zeta": jfine_s3,
        "jfine_d4_value_s3_mixed_character": mixed,
        "jfine_heisenberg_four_pair": h4,
        "jfine_d4_symplectic_obstruction": d4_symplectic,
        "jfine_d4_h6_model_weld": d4_h6_weld,
        "jfine_d4_single_line_orientation_bypass": d4_line_bypass,
        "jfine_d4_oriented_c4_monster_necessary_bridge": d4_c4_steelman,
        "jfine_h4_central_phase_fourier_intertwiner": h4_fourier_weld,
        "projective_f9_pointed80": projective,
        "projective_group_f9_720": pgl,
        "f81_norm_inversion": f81_norm,
        "f81_same_quadratic_tower": f81_tower,
        "large_grid": {"scanned_rows": len(lattice["rows"]),
                       "payload_sha256": lattice["payload_sha256"],
                       "scope": lattice["scope"],
                       "basis_certificates": lattice["prime_power_operator_certificates"],
                       "selected_cases": [lattice_case(2, 2, 10),
                                          lattice_case(2, 3, 5),
                                          lattice_case(3, 2, 3),
                                          lattice_case(3, 3, 3)]},
        "matched_controls": matched,
        "algebra_369": {
            "z6_2023_phi_s": z6["iit_4_0_2023"]["distinct_phi_s"],
            "s3_2023_phi_s": s3["iit_4_0_2023"]["distinct_phi_s"],
            "same_six_state_profile_observed": same_6_profile,
            "z9_2023_phi_s": z9["iit_4_0_2023"]["distinct_phi_s"],
            "f3_squared_2023_phi_s": f3sq["iit_4_0_2023"]["distinct_phi_s"],
            "same_nine_state_profile_observed": same_9_profile,
        },
        "hyperfabric_fixtures": fixtures,
        "pointed27_counts": pointed,
        "structure_arithmetic": {
            "relation_candidate_count_for_three_distinctions": relation_candidates,
            "synthetic_relation_overlap_phi": relation_overlap_phi,
            "synthetic_composed_big_phi": composed_big_phi,
        },
        "stress": stress,
    }


def main() -> None:
    receipt = verify_numeric_results()
    output = Path(__file__).with_name("data") / "outputs" / "iit_numeric_verification.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
