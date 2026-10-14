from phase243_core54_pareto_coil import solve_maxcut


def test_phase243_core54_pareto_coil_maxcut():
    r = solve_maxcut()
    assert r["representative_count"] == 54
    assert r["record_count"] == 810
    assert r["pareto_count"] > 0
    assert r["coil_survivor_count"] > 0
    assert all(x["nonaxis_norm"] >= 0.04 - 1e-9 for x in r["pareto"])
    assert all(abs(x["M"] ** 2 + x["alpha"] + x["deltaC"] - 1) < 1e-9 for x in r["pareto"])
    assert all(x["div_rms"] < 0.015 for x in r["pareto"])
    assert all(x["coil_relative_bn_residual"] < 1.0 for x in r["coil_survivors"])


if __name__ == "__main__":
    test_phase243_core54_pareto_coil_maxcut()
    print("PASS")
