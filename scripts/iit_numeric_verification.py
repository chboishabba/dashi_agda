#!/usr/bin/env python3
"""Numerical/combinatorial verification for the IIT / 369 max-cut.

This file is deliberately *not* a source/build checker. It never inspects Agda
text, imports, filenames, or theorem names. Formal completeness belongs to the
Agda aggregate and the Agda compiler.

The only authority here is executable finite mathematics: enumerate states and
partitions, evaluate the finite IIT reference quantities, and check numerical
or finite-combinatorial regression targets. Full distinction/relation/CES
verification is delegated to ``iit4_pyphi_oracle.py`` when PyPhi is available;
this verifier does not pretend that stored literature calibration constants are
fresh numerical evidence.
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
from iit4_structure_reference import (
    big_phi,
    nonempty_relation_candidates,
    relation_phi_from_overlap,
)
from iit_369_algebra_scan import algebra_summary
from iit_hyperfabric_fixture_scan import fixture_summary
from iit_matched_fabric_gate_sweep import sweep_summary
from iit_pointed27_gluing_scan import gluing_summary
from iit_xor_369_stress_scan import stress_summary
from iit_xor_grid_calibration import calibration_summary


def _xor2(a: int, b: int) -> int:
    return a ^ b


def _or2(a: int, b: int) -> int:
    return int(bool(a) or bool(b))


def _tri_xor(a: int, b: int) -> int:
    return (a + b) % 3


def _phi_values(model, version: str) -> list[float]:
    return sorted(
        {
            round(system_phi(model, state, formalism=version)["phi_s"], 12)
            for state in model.states
        }
    )


def verify_numeric_results() -> dict:
    # Core finite enumeration / system-phi regression.
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

    # Actual repo 2x2 XOR-grid numerical calibration.
    grid = calibration_summary()["recurrent_xor_grid_2x2"]
    assert grid["states_tested"] == 16
    assert grid["iit_4_0_2023"]["distinct_phi_s"] == [0.0, 0.5]
    assert grid["iit_4_0_2023"]["zero_phi_states"] == 12
    assert grid["iit_4_0_2026"]["distinct_phi_s"] == [0.0]
    assert grid["iit_4_0_2026"]["zero_phi_states"] == 16

    # Same-fabric / varying-gate and same-gate / varying-fabric controls.
    matched = sweep_summary()
    fixed = matched["fixed_recurrent_fabric_vary_gate"]
    assert fixed["binary_xor"]["iit_4_0_2023"]["distinct_phi_s"] == [2.0]
    assert fixed["binary_or"]["iit_4_0_2023"]["distinct_phi_s"] == [
        0.0,
        round(math.log2(4 / 3), 12),
        2.0,
    ]
    assert fixed["binary_and"]["iit_4_0_2023"]["zero_phi_states"] == 6
    assert fixed["ternary_trixor"]["iit_4_0_2023"]["distinct_phi_s"] == [
        round(math.log2(9), 12)
    ]
    topology = matched["fixed_binary_xor_vary_fabric"]
    assert topology["feedforward"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0]
    assert topology["recurrent_three_cell"]["iit_4_0_2023"]["distinct_phi_s"] == [2.0]
    assert topology["grid_2x2"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0, 0.5]

    # 369 same-cardinality algebra control: compare computed profiles only.
    algebra = algebra_summary()
    expected9 = round(math.log2(81), 12)
    z9 = algebra["z9_cyclic"]
    f3sq = algebra["f3_squared"]
    assert z9["iit_4_0_2023"]["distinct_phi_s"] == [expected9]
    assert f3sq["iit_4_0_2023"]["distinct_phi_s"] == [expected9]
    assert z9["iit_4_0_2026"]["distinct_phi_s"] == [0.0]
    assert f3sq["iit_4_0_2026"]["distinct_phi_s"] == [0.0]
    same_369_profile = (
        z9["iit_4_0_2023"]["distinct_phi_s"]
        == f3sq["iit_4_0_2023"]["distinct_phi_s"]
    )
    assert same_369_profile

    # Hyperform/hyperfabric finite fixtures: numerical IIT outputs only.
    fixtures = fixture_summary()["fixtures"]
    assert fixtures["open_xor_path"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0]
    assert fixtures["closed_xor_cycle"]["iit_4_0_2023"]["distinct_phi_s"] == [2.0]
    assert fixtures["xor_grid_2x2"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0, 0.5]
    assert fixtures["closed_trixor_cycle"]["iit_4_0_2023"]["distinct_phi_s"] == [
        round(math.log2(9), 12)
    ]

    # Pointed-27 finite geometry counts are numerical/combinatorial receipts.
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

    # Composition-layer arithmetic only. Fresh mechanism/purview/CES values
    # belong to the PyPhi oracle, not to hard-coded calibration constants here.
    relation_candidates = len(nonempty_relation_candidates(("d1", "d2", "d3")))
    relation_overlap_phi = relation_phi_from_overlap(0.12, 3, 2)
    composed_big_phi = big_phi([0.1, 0.2, 0.3], [0.05, 0.15])
    assert relation_candidates == 7
    assert abs(relation_overlap_phi - 0.08) < 1e-12
    assert abs(composed_big_phi - 0.8) < 1e-12

    # Cross-alphabet stress values, again as numerical observations only.
    stress = stress_summary()
    assert stress["binary_recurrent_xor"]["iit_4_0_2023"]["distinct_phi_s"] == [2.0]
    assert stress["binary_xor_grid_2x2"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0, 0.5]
    assert stress["ternary_recurrent_trixor"]["iit_4_0_2023"]["distinct_phi_s"] == [
        round(math.log2(9), 12)
    ]
    assert stress["z9_recurrent_addition"]["iit_4_0_2023"]["distinct_phi_s"] == [expected9]
    assert stress["f3_squared_recurrent_addition"]["iit_4_0_2023"]["distinct_phi_s"] == [expected9]

    return {
        "contract": "iit_numeric_verification",
        "scope": "numeric_and_finite_combinatorial_only",
        "formal_source_or_agda_checks_performed": False,
        "full_ces_values_verified_here": False,
        "full_ces_oracle": "scripts/iit4_pyphi_oracle.py",
        "core": core,
        "xor_grid": grid,
        "matched_controls": matched,
        "algebra_369": {
            "z9_2023_phi_s": z9["iit_4_0_2023"]["distinct_phi_s"],
            "f3_squared_2023_phi_s": f3sq["iit_4_0_2023"]["distinct_phi_s"],
            "same_profile_observed": same_369_profile,
        },
        "hyperfabric_fixtures": fixtures,
        "pointed27_counts": {
            key: pointed[key]
            for key in (
                "carrier_size",
                "strata",
                "non_origin_count",
                "total_point_face_incidences",
                "face_count",
                "each_face_size",
                "pairwise_face_overlaps",
                "each_edge_overlap_size",
                "corner_face_triples",
                "each_corner_triple_intersection_size",
                "three_selected_cubie_choices",
            )
        },
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
