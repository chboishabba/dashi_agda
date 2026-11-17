from exceptional_h3_phase_metric_gluing_probe import verify


def test_exceptional_h3_phase_metric_gluing_probe():
    receipt = verify()
    assert receipt["plus_lifted_det_mod3"] == 1
    assert receipt["minus_lifted_det_mod3"] == 1
    assert receipt["weyl_covariant_lift"] is True
    assert receipt["affine_fibre_automorphisms_checked"] == 6
    assert receipt["orientation_inversion_leaves_metric_term_invariant"] is True
    assert receipt["global_h3_phase_bundle_identified_with_e8_zeta"] is False
