from scripts.eisenstein_divisor_power_parity import parity_report


def test_sigma3_oeis_prefix_parity():
    report = parity_report()
    assert report["sigma3_matches_oeis_prefix"] is True
    assert report["sigma3_prefix"][:6] == [1, 9, 28, 73, 126, 252]


def test_sigma5_oeis_prefix_parity():
    report = parity_report()
    assert report["sigma5_matches_oeis_prefix"] is True
    assert report["sigma5_prefix"][:6] == [1, 33, 244, 1057, 3126, 8052]


def test_e4_oeis_prefix_parity():
    report = parity_report()
    assert report["e4_matches_oeis_prefix"] is True
    assert report["e4_prefix"][:7] == [1, 240, 2160, 6720, 17520, 30240, 60480]


def test_e6_oeis_prefix_parity():
    report = parity_report()
    assert report["e6_matches_oeis_prefix"] is True
    assert report["e6_prefix"][:7] == [1, -504, -16632, -122976, -532728, -1575504, -4058208]


def test_parity_does_not_promote_authority():
    report = parity_report()
    assert report["oeis_defines_kernel"] is False
    assert report["oeis_defines_eisenstein_coefficients"] is False
    assert report["finite_prefix_proves_infinite_series"] is False
    assert report["finite_prefix_proves_modularity"] is False
