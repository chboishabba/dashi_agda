from j369_monster3b_selected_gf729_weld import build_receipt


def test_monster3b_compression_reaches_center_preserving_full_punctured_action():
    receipt = build_receipt()
    assert receipt["selected_modulus_low_to_high"] == [1, 0, 0, 0, 1, 1, 1]

    beta = receipt["earlier_beta_weld"]
    assert beta["multiplicative_order"] == 364
    assert beta["intertwining_verified"] is True

    inverter = receipt["primitive_inverter_comparator"]
    assert inverter["source_word"] == "g2^-1 g1 g2^-1 g1 g2 g1 g2^-1"
    assert inverter["similitude_multiplier"] == 2
    assert inverter["primitive_root_multiplicative_order"] == 728

    preferred = receipt["preferred_center_preserving_primitive_weld"]
    assert preferred["source_word"] == "g1 g2^-1 g1 g2 g1 g2^-1 g1 g2^-1"
    assert preferred["similitude_multiplier"] == 1
    assert preferred["compression_modulus_low_to_high"] == [2, 2, 1, 0, 2, 0, 1]
    assert preferred["primitive_root_coordinates"] == [0, 1, 0, 1, 1, 0]
    assert preferred["primitive_root_multiplicative_order"] == 728
    assert preferred["compression_matrix"] == [
        [2,2,0,1,1,2],
        [0,0,0,1,1,2],
        [2,1,0,0,0,0],
        [1,2,0,2,2,2],
        [0,0,1,1,1,2],
        [0,0,1,2,1,1],
    ]
    assert preferred["intertwiner_Q"] == [
        [1,1,0,1,0,0],
        [0,2,0,1,2,2],
        [0,0,1,1,0,1],
        [0,1,1,2,0,2],
        [0,2,2,0,2,2],
        [0,2,2,2,2,2],
    ]
    assert preferred["intertwiner_determinant_mod3"] == 2
    assert preferred["intertwining_verified"] is True
    assert preferred["cyclic_rank_e0"] == 6
    assert preferred["breaks_swap01_at_e0"] is True
    assert preferred["punctured_orbit_size"] == 728
    assert preferred["punctured_stabilizer_size"] == 1

    assert receipt["selected_field_presentation_weld_paid"] is True
    assert receipt["selected_field_multiplicative_action_weld_paid"] is True
    assert receipt["center_preserving_primitive_action_weld_paid"] is True
    assert receipt["full_monster_semantic_action_recognition_paid"] is False
