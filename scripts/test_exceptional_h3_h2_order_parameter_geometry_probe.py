from exceptional_h3_h2_order_parameter_geometry_probe import verify


def test_exceptional_h3_h2_order_parameter_geometry_probe():
    r = verify()
    assert r["h3_stabilizer_order"] == 432
    assert r["order_parameter_action_order"] == 72
    assert r["translation_subgroup_size"] == 9
    assert r["orthogonal_linear_part_size"] == 8
    assert r["action_is_F3_squared_semidirect_O2_3"] is True
    assert r["norm1_neighbor_count"] == 4
    assert r["norm2_shell_count"] == 4
    assert r["norm1_is_axial_C3xC3_adjacency"] is True
    assert r["canonical_quadratic_displacement_invariant"] is True
    assert r["physical_kinetic_coefficient_derived"] is False
