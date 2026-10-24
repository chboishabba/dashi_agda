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
