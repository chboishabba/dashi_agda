from trinification_two_vev_mass_probe import verify


def test_two_neutral_vev_mass_kernel_and_spectrum():
    r = verify()
    assert r["single_vev_stabilizer_dimension"] == 7
    assert r["two_vev_stabilizer_dimension"] == 4
    assert r["two_vev_mass_rank"] == 12
    assert r["unbroken_generators"] == ["SU2L_1", "SU2L_2", "SU2L_3", "Y"]
    assert r["hypercharge_generator_survives"] is True
    assert r["positive_mass_eigenvalue_multiplicities"] == {"1/4": 4, "1/2": 7, "5/6": 1}
    assert r["color_untouched"] is True
