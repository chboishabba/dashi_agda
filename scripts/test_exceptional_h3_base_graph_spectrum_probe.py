from exceptional_h3_base_graph_spectrum_probe import verify


def test_h3_base_graph_spectrum_and_incidence_identity():
    r = verify()
    assert r["h3_count"] == 120
    assert r["h2_count"] == 270
    assert r["h3_degree"] == 27
    assert r["adjacency_spectrum"] == {27: 1, 9: 20, 3: 15, -3: 84}
    assert r["laplacian_spectrum"] == {0: 1, 18: 20, 24: 15, 30: 84}
    assert r["base_spectral_gap"] == 18
    assert r["incidence_identity_NNt_eq_9I_plus_A"] is True
