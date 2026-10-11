from phase243_core54_physical_replay import run_replay


def test_core54_nonaxisymmetric_replay():
    result = run_replay()
    assert result["representative_count"] == 54
    assert result["nonaxis_floor"] > 0.0
    assert result["best_tag"] == (2, 0, 0, 0)
    assert result["best_divergence_rms"] < 1e-12
    assert result["best_relative_B_spread"] < 0.01


if __name__ == "__main__":
    test_core54_nonaxisymmetric_replay()
    print("ok")
