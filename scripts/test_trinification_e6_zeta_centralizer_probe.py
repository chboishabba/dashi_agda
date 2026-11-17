from trinification_e6_zeta_centralizer_probe import verify


def test_zeta_grading_centralizer_is_trinification():
    r = verify()
    assert r["e6_norm_symmetry_dimension"] == 78
    assert r["zeta_centralizer_dimension"] == 24
    assert r["explicit_trinification_dimension"] == 24
    assert r["explicit_trinification_preserves_cubic"] is True
    assert r["explicit_trinification_commutes_with_zeta_grading"] is True
    assert r["centralizer_equals_trinification_by_inclusion_and_dimension"] is True
    assert r["two_vev_full_e6_stabilizer_dimension"] == 49
    assert r["two_vev_direct_e6_to_sm_claim"] is False
