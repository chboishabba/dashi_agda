from trinification_two_vev_invariant_potential_probe import verify


def test_two_vev_invariant_potential_selects_sm_stabilizer_orbit():
    r = verify()
    assert r["selected_pair_potential"] == 0.0
    assert r["all_sampled_terms_nonnegative"] is True
    assert r["all_sampled_gauge_transforms_preserve_potential"] is True
    assert r["all_sampled_selected_orbit_points_zero"] is True
    assert r["zero_conditions"] == ["unit_norms", "rank_one", "right_orthogonal", "left_aligned"]
    assert r["full_e6_invariance_claimed"] is False
