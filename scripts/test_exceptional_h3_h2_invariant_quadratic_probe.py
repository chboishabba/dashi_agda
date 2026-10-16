from exceptional_h3_h2_invariant_quadratic_probe import verify


def test_invariant_quadratic_classification_and_locality():
    r = verify()
    assert r["ordered_pair_orbit_sizes"] == [9, 36, 36]
    assert r["invariant_kernel_dimension"] == 3
    assert r["invariant_basis"] == ["I", "A_norm1", "A_norm2"]
    assert r["local_constant_annihilating_family_dimension"] == 1
    assert r["canonical_local_operator"] == "4I-A_norm1"
    assert r["canonical_local_spectrum"] == {0: 1, 3: 4, 6: 4}
    assert r["physical_kinetic_coefficient_paid"] is False
