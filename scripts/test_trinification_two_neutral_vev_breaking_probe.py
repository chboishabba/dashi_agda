from trinification_two_neutral_vev_breaking_probe import verify


def test_trinification_two_neutral_vev_breaking_probe():
    r = verify()
    assert r["one_neutral_vev_lr_stabilizer_dimension"] == 7
    assert r["two_independent_neutral_vevs_lr_stabilizer_dimension"] == 4
    assert r["surviving_lr_generators"] == "su2_L + u1_Y"
    assert r["both_vevs_hypercharge_neutral"] is True
    assert r["color_su3_untouched"] is True
    assert r["full_low_energy_lie_algebra_dimension"] == 12
    assert r["broken_lr_generator_count"] == 12
    assert r["conditional_gauge_mass_matrix_rank"] == 12
    assert r["physical_vev_scale_derived"] is False
    assert r["higgs_potential_selects_these_vevs"] is False
