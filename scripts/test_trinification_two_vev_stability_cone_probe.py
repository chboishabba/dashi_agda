from trinification_two_vev_stability_cone_probe import verify


def test_two_vev_general_coefficient_stability_cone():
    r = verify()
    assert r["zero_mode_multiplicity"] == 12
    assert r["transverse_eigenvalue_families"] == {
        "8a": 1, "8b": 1, "4e": 2, "4f": 4,
        "4c+2f": 4, "4d+2f": 4,
        "4c+2e+2f": 4, "4d+2e+2f": 4,
    }
    assert r["random_formula_replays"] == 30
    assert r["all_random_formula_replays_exact"] is True
    assert r["strict_stability_conditions"] == [
        "a>0", "b>0", "e>0", "f>0", "2c+f>0", "2d+f>0"
    ]
    assert r["unique_physical_potential_derived"] is False
