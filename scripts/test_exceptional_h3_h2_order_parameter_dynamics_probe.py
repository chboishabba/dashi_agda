from exceptional_h3_h2_order_parameter_dynamics_probe import verify


def test_order_parameter_laplacian_spectrum_and_symmetry():
    r = verify()
    assert r["vertex_count"] == 9
    assert r["degree"] == 4
    assert r["laplacian_spectrum"] == {0: 1, 3: 4, 6: 4}
    assert r["affine_orthogonal_action_order"] == 72
    assert r["all_affine_orthogonal_actions_preserve_adjacency"] is True
    assert r["all_affine_orthogonal_actions_commute_with_laplacian"] is True
    assert r["nonzero_spectral_gap"] == 3
