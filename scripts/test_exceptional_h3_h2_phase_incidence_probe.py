from exceptional_h3_h2_phase_incidence_probe import verify


def test_exceptional_h3_h2_phase_incidence_probe():
    r = verify()
    assert r["h3_count"] == 120
    assert r["h2_count"] == 270
    assert r["h3_h2_incidence_count"] == 1080
    assert r["h2_per_h3"] == 9
    assert r["h3_per_h2"] == 4
    assert r["kernel_complements_equal_incident_h2_for_all_h3"] is True
    assert r["decorated_metric_count"] == 1080
    assert r["decorated_metric_determinant_mod3"] == 1
    assert r["simple_reflection_transition_checks"] == 6480
    assert r["weyl_covariant_decorated_metric"] is True
    assert r["selected_h3_stabilizer_order"] == 432
    assert r["selected_h3_h2_flag_stabilizer_order"] == 48
    assert r["phase_line_equals_incident_h2_face_same_object"] is True
