from scripts.eisenstein_divisor_power_parity import parity_report


def test_sigma3_oeis_prefix_parity():
    report = parity_report()
    assert report["sigma3_matches_oeis_prefix"] is True
    assert report["sigma3_prefix"][:6] == [1, 9, 28, 73, 126, 252]


def test_sigma5_oeis_prefix_parity():
    report = parity_report()
    assert report["sigma5_matches_oeis_prefix"] is True
    assert report["sigma5_prefix"][:6] == [1, 33, 244, 1057, 3126, 8052]


def test_parity_does_not_promote_authority():
    report = parity_report()
    assert report["oeis_defines_kernel"] is False
    assert report["finite_prefix_proves_infinite_series"] is False
    assert report["finite_prefix_proves_modularity"] is False
