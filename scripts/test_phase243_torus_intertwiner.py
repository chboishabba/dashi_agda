from phase243_torus_intertwiner import verify


def test_phase243_torus_intertwiner():
    out = verify()
    assert out["incidence_count"] == 27
    assert out["state_count"] == 243
    assert out["max_advance_error"] < 1e-12
    assert out["max_inverse_error"] < 1e-12
    assert out["all_incidence_shifts_solved"]


if __name__ == "__main__":
    test_phase243_torus_intertwiner()
    print("ok")
