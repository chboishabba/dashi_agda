"""Regression tests for the Gielis/Base369 finite and numerical cut.

Run: python -m pytest -q tests/test_gielis_base369_experiments.py
"""
import importlib.util
from pathlib import Path
import sys
from fractions import Fraction

import numpy as np
import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "gielis_base369_experiments", ROOT / "scripts" / "gielis_base369_experiments.py"
)
g = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = g
SPEC.loader.exec_module(g)


def test_exact_gram_and_projector_laws():
    result = g.exact_receipt()
    assert result["gram"]["3x6"] == 0
    assert result["gram"]["3x9"] == 0
    assert result["gram"]["6x9"] == 0
    assert result["checked_basis_vectors"] == 18


@pytest.mark.parametrize("m", (3, 6, 9))
def test_continuous_symmetric_radius_and_exact_sampling(m):
    theta = np.linspace(-3.2, 3.2, 97)
    np.testing.assert_allclose(g.gielis_radius(theta + 2*np.pi/m, m),
                               g.gielis_radius(theta, m), rtol=0, atol=1e-13)
    np.testing.assert_allclose(g.gielis_radius(-theta, m),
                               g.gielis_radius(theta, m), rtol=0, atol=1e-13)
    grid = np.arange(18) * (2*np.pi/18)
    # 8*(r^(-2)-3/4) = 2*cos(m*theta), i.e. exact integral sampler.
    np.testing.assert_allclose(
        8*(g.gielis_radius(grid,m)**(-2) - .75),
        np.array(g.signature(m)), rtol=0, atol=5e-14)


def test_projector_on_rational_basis():
    e = tuple(Fraction(int(j == 7)) for j in range(18))
    assert g.projector(g.projector(e, 6), 9) == g.projector(e, 18)
    assert g.projector(g.projector(e, 3), 9) == g.projector(e, 9)
    assert g.projector(g.projector(e, 3), 6) == g.projector(e, 6)


@pytest.mark.parametrize("m", (3, 6, 9))
def test_ellipse_free_dirichlet_spectrum_positive(m):
    vals = g.laplacian_eigenvalues(m, 25, k=3)
    assert len(vals) == 3
    assert all(v > 0 for v in vals)
    assert vals == sorted(vals)


@pytest.mark.parametrize("m", (3, 6, 9))
@pytest.mark.parametrize("epsilon", (0., .12, .24))
def test_reflector_endpoint_lock_and_finite_segments(m, epsilon):
    vertices = g.spiral_vertices(m, epsilon, 192)
    assert vertices.shape == (193, 2)
    assert np.linalg.norm(vertices[0]) == pytest.approx(.75)
    assert np.linalg.norm(vertices[-1]) == pytest.approx(1.55)
    assert np.isfinite(vertices).all()


def test_baseline_independent_of_m_when_epsilon_zero():
    np.testing.assert_allclose(g.spiral_vertices(3, 0, 256),
                               g.spiral_vertices(9, 0, 256), rtol=0, atol=1e-15)


def test_specular_reflection_and_single_ray_export():
    boundary = g.spiral_vertices(3, .12, 384)
    trace = g.trace_ray(.37*np.pi, boundary, max_bounces=5, record=True)
    assert trace["exit_reason"] in {
        "absorbed_at_target", "outer_gate", "escaped_open_reflector",
        "reflection_limit"
    }
    assert trace["path"] and len(trace["path"][0]) == 2
    assert len(trace["collisions"]) <= 6
    assert trace["absolute_torque"] >= abs(trace["signed_torque"]) - 1e-12


def test_small_pareto_sweep_and_determinism():
    runs1 = g.optical_sweep(rays=24, segments=128, bounces=3)
    runs2 = g.optical_sweep(rays=24, segments=128, bounces=3)
    assert runs1 == runs2 and len(runs1) == 7
    assert g.pareto(runs1)
    assert all(0 <= row["focus_fraction"] <= 1 for row in runs1)


def test_exact_18_to_36_nyquist_phase_resolution():
    r = g.nyquist36_receipt()
    assert r["coarse_sine_samples_zero"] == 18
    assert r["fine_sine9_j1"] == 1
    assert r["fine_sine27_j1"] == -1
    assert r["cos_sin9_gram"] == 0


def test_zero_reflection_budget_is_strict():
    scene = g.spiral_vertices(3, 0.12, 192)
    for angle in (.1,.6,1.1,2.8,4.8):
        row = g.trace_ray(angle, scene, max_bounces=0, record=True)
        assert row["reflections"] == 0
        assert len(row["collisions"]) == 0


def test_bounce_budget_never_exceeded():
    scene = g.spiral_vertices(6, 0.24, 192)
    for angle in np.linspace(0, 2*np.pi, 31,endpoint=False):
        row = g.trace_ray(float(angle), scene, max_bounces=3, record=True)
        assert row["reflections"] <= 3
        assert row["reflections"] == len(row["collisions"])


def test_pareto_both_legal_torque_objectives():
    designs = [
        {"name":"A", "focus_fraction":.60, "mean_abs_torque":1.},
        {"name":"B", "focus_fraction":.40, "mean_abs_torque":2.},
        {"name":"C", "focus_fraction":.20, "mean_abs_torque":.25},
    ]
    assert [x["name"] for x in g.pareto(designs, "min")] == ["A","C"]
    assert [x["name"] for x in g.pareto(designs, "max")] == ["A","B"]
    with pytest.raises(ValueError):
        g.pareto(designs, "unspecified")


def test_non369_controls_are_not_silently_excluded():
    controls = g.optical_sweep(rays=16,segments=128,bounces=2,
                               include_controls=True)
    assert len(controls)==13
    assert {item["m"] for item in controls} == {3,4,5,6,7,9}
    assert all(item["total_reflections"] <= 16*2 for item in controls)


def test_roadmap_has_complete_exact_leaves_and_deliverables():
    import re
    roadmap = (ROOT / "Docs/support/reference/GielisBase369Roadmap.md").read_text()
    ids = re.findall(r"^\| (G\d\d) \|",roadmap,flags=re.MULTILINE)
    assert ids == [f"G{i:02d}" for i in range(1,22)]
    for phase in range(6):
        assert f"P{phase} " in roadmap or f"P{phase} —" in roadmap
    for deliverable in range(8):
        assert f"D{deliverable}" in roadmap
    for owner in (
        "Base369CirclePhase.agda",
        "DNAHelixDihedralExact.agda",
        "TorqueTrialectic369Exact.agda",
        "AnalyticLogPolarSpiralCompilerExact.agda",
        "ShannonInformationEntropyBoundary.agda",
        "GielisBase369NyquistPhase36Exact.agda",
    ):
        assert owner in roadmap
    assert "OPEN" in roadmap and "kernel" in roadmap


def test_roadmap_named_new_sources_exist():
    for relpath in (
        "DASHI/Geometry/GielisBase369FiniteExact.agda",
        "DASHI/Geometry/GielisBase369NyquistPhase36Exact.agda",
        "DASHI/Geometry/GielisBase369ExistingOwnersWeldExact.agda",
        "Docs/support/reference/GielisBase369Roadmap.md",
    ):
        assert (ROOT / relpath).is_file()
