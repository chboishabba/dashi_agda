from exceptional_h3_phase_order_parameter_probe import verify


def test_exceptional_h3_phase_order_parameter_probe():
    receipt = verify()
    assert receipt["weyl_order"] == 51840
    assert receipt["selected_h3_stabilizer_order"] == 432
    assert receipt["selected_h3_local_image_order"] == 72
    assert receipt["radical_resolving_projective_covectors"] == 9
    assert receipt["phase_line_orbit_size"] == 9
    assert receipt["phase_line_stabilizer_order"] == 48
    assert receipt["local_phase_line_stabilizer_order"] == 8
    assert receipt["phase_orbit_is_all_radical_resolving_lines"] is True
    assert receipt["bare_h3_geometry_selects_unique_phase_line"] is False
    assert receipt["phase_line_is_symmetry_breaking_order_parameter"] is True
