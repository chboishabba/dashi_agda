from trinification_two_vev_hessian_probe import verify


def test_two_vev_quartic_has_only_gauge_flat_directions():
    r = verify()
    assert r["real_field_dimension"] == 36
    assert r["broken_gauge_orbit_dimension"] == 12
    assert r["gauge_orbit_tangent_rank"] == 12
    assert r["hessian_zero_mode_count"] == 12
    assert r["hessian_positive_mode_count"] == 24
    assert r["hessian_eigenvalue_multiplicities"] == {0: 12, 4: 6, 6: 8, 8: 10}
    assert r["gauge_tangent_annihilated_by_hessian"] is True
    assert r["hessian_kernel_equals_gauge_orbit_tangent"] is True
    assert r["accidental_local_flat_directions"] is False
    assert r["physical_higgs_masses_paid"] is False
