from j369_monster3b_selected_gf729_weld import build_receipt


def test_monster3b_compression_is_conjugate_to_selected_gf729_generator():
    receipt = build_receipt()

    assert receipt["selected_modulus_low_to_high"] == [1, 0, 0, 0, 1, 1, 1]
    assert receipt["compression_modulus_low_to_high"] == [1, 0, 1, 2, 0, 2, 1]
    assert receipt["affine_generator_change"] == "beta = 1 - alpha"
    assert receipt["beta_coordinates"] == [1, 2, 0, 0, 0, 0]
    assert receipt["polynomial_substitution_verified"] is True

    assert receipt["compression_matrix"] == [
        [0, 2, 1, 0, 2, 1],
        [2, 0, 2, 1, 2, 2],
        [0, 0, 0, 0, 1, 2],
        [2, 0, 1, 2, 1, 2],
        [2, 0, 2, 2, 0, 2],
        [1, 0, 1, 0, 2, 2],
    ]
    assert receipt["intertwiner_Q"] == [
        [1, 0, 0, 2, 1, 1],
        [0, 0, 0, 2, 1, 2],
        [0, 0, 2, 1, 0, 1],
        [0, 0, 1, 1, 2, 0],
        [0, 1, 1, 0, 1, 2],
        [0, 2, 0, 1, 2, 2],
    ]
    assert receipt["intertwiner_determinant_mod3"] == 2
    assert receipt["intertwining_verified"] is True
    assert receipt["cyclic_rank_e0"] == 6
    assert receipt["breaks_swap01_at_e0"] is True
    assert receipt["selected_field_presentation_weld_paid"] is True
    assert receipt["full_action_orbit_stabilizer_recognition_paid"] is False
