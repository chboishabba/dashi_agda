import numpy as np

from c3_winding_surface_inverse import WindingSurfaceInverse


def test_current_potential_inverse_reduces_normal_field():
    problem = WindingSurfaceInverse(nt=8, nz=9)
    target_rms = float(np.sqrt(np.mean(problem.target * problem.target)))
    assert target_rms > 0.0
    solved = problem.solve(0.1)
    assert np.isfinite(solved["relative_rms"])
    assert solved["relative_rms"] < 0.5
    phi = problem.current_potential(solved["coefficients"])
    assert phi.shape == problem.TH.shape
    assert np.all(np.isfinite(phi))


if __name__ == "__main__":
    test_current_potential_inverse_reduces_normal_field()
    print("ok")
