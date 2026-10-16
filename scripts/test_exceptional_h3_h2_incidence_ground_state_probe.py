from exceptional_h3_h2_incidence_ground_state_probe import verify


def test_incidence_interaction_ground_states_and_weyl_orbits():
    r = verify()
    assert r["h3_count"] == 120
    assert r["h2_count"] == 270
    assert r["incidence_count"] == 1080
    assert r["maximum_agreement_edges"] == 180
    assert r["first_excitation_agreement_edges"] == 177
    assert r["dimensionless_defect_gap"] == 3
    assert r["ground_state_exact_cover_count"] == 6642
    assert r["ground_state_weyl_orbit_sizes"] == [162, 1620, 1620, 3240]
    assert r["ground_state_stabilizer_orders"] == [320, 32, 32, 16]
    assert r["all_ground_states_are_exact_covers"] is True
    assert r["gap_three_distinct_from_fibre_laplacian_gap_without_operator_weld"] is True
    assert r["physical_interaction_coefficient_paid"] is False
