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


def test_model_code_is_reversible_and_baseline_canonical():
    assert g.model_encode(3,0.) == g.model_encode(9,0.) == "0"
    assert g.model_decode("0") == (0,0.)
    codes = set()
    for m in range(1,10):
        for q in range(1,451):
            epsilon=q/1000
            bits=g.model_encode(m,epsilon)
            assert g.model_decode(bits) == (m,epsilon)
            codes.add(bits)
    assert len(codes)==9*450
    # In sorted order a strict prefix would precede its extensions.
    ordered=sorted(codes)
    assert all(not b.startswith(a) for a,b in zip(ordered,ordered[1:]))
    with pytest.raises(ValueError):
        g.model_decode("101")


def test_model_code_is_distinct_from_information_optimality():
    result=g.optical_sweep(rays=12,segments=128,bounces=1)
    assert all(row["model_code_bits"]>=1 for row in result)
    assert result[0]["model_code_bits"]==1
    assert all(row["comparison_to_legacy"]=="not_same_apparatus" for row in result)


@pytest.mark.parametrize("m,epsilon", ((3,.12),(6,.24),(9,.12)))
def test_wall_angular_impulse_conserves_ray_angular_momentum(m,epsilon):
    """The wall receives the negative of the ray's angular impulse."""
    scene = g.spiral_vertices(m,epsilon,256)
    for angle in np.linspace(.05, 2*np.pi-.05, 37):
        row = g.trace_ray(float(angle), scene, max_bounces=5, record=True)
        assert row["reflections"] == len(row["collisions"])
        total_wall_impulse = 0.0
        for hit in row["collisions"]:
            pin = np.array(hit["incoming_unit_momentum"])
            pout = np.array(hit["outgoing_unit_momentum"])
            normal = np.array(hit["normal"])
            point = np.array(hit["point"])
            np.testing.assert_allclose(pout, pin-2*np.dot(pin,normal)*normal,
                                       rtol=0,atol=3e-13)
            np.testing.assert_allclose(hit["wall_unit_impulse"],pin-pout,
                                       rtol=0,atol=3e-13)
            assert abs(hit["angular_momentum_balance_residual"]) < 1e-13
            assert hit["wall_angular_impulse"] == pytest.approx(
                g.cross(point,pin-pout),abs=3e-13)
            total_wall_impulse += hit["wall_angular_impulse"]
        assert row["signed_torque"] == pytest.approx(total_wall_impulse,abs=3e-13)
        assert row["absolute_torque"]+1e-12 >= abs(total_wall_impulse)


def test_ideal_specular_power_torque_is_dimensionally_scaled():
    import math
    assert g.SPEED_OF_LIGHT_M_S == 299792458
    for watts in (0., .5, 25., 1000.):
        for angular_m in (-3.5, 0., 1.25):
            result = g.ideal_specular_wall_torque_nm(angular_m, watts)
            assert result == pytest.approx(watts*angular_m/299792458,abs=1e-18)
    with pytest.raises(ValueError):
        g.ideal_specular_wall_torque_nm(1., -1.)
    with pytest.raises(ValueError):
        g.ideal_specular_wall_torque_nm(1., math.inf)


def test_symbolic_gielis_certificates_if_sympy_available():
    pytest.importorskip("sympy")
    spec = importlib.util.spec_from_file_location(
        "gielis_base369_symbolic_certificates",
        ROOT / "scripts/gielis_base369_symbolic_certificates.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    receipt=module.prove()
    assert receipt["status"] == "exact_symbolic_identities_passed"
    assert receipt["area"] == "sqrt(2)*pi"
    assert receipt["wall_ray_angular_impulse_balance"]
    assert not receipt["agda_kernel_accepted"]
    assert not receipt["physical_optics_validated"]


def test_exact_agda_tables_source_audit():
    spec = importlib.util.spec_from_file_location(
        "gielis_base369_source_audit",
        ROOT / "scripts/gielis_base369_source_audit.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    receipt=module.source_audit(ROOT)
    assert receipt["finite_checks"] == 648
    assert receipt["complete_18_case_theorems"] == 19
    assert receipt["gram_369"] == [[36,0,0],[0,36,0],[0,0,72]]
    assert not receipt["agda_kernel_accepted"]


def test_exact_q_zeta36_character_orthogonality_and_reconstruction():
    spec=importlib.util.spec_from_file_location(
        "gielis_cyclotomic36_exact",
        ROOT/"scripts/gielis_cyclotomic36_exact.py")
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    r=module.receipt()
    assert r["full_character_orthogonality_pairs"] == 1296
    assert r["recovered_coefficients"] == 7
    assert r["all_36_sample_reconstruction"]
    assert not r["float_computation"]
    assert not r["agda_kernel_accepted"]


def test_exact_rational_sector_spectral_convergence_certificate():
    spec=importlib.util.spec_from_file_location(
        "gielis_sector_spectral_certificate",
        ROOT/"scripts/gielis_sector_spectral_certificate.py")
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    r=module.certificate(9,2048)
    from fractions import Fraction
    assert Fraction(r["relative_eigenvalue_error_upper"]) < Fraction(1,100)
    assert r["rigorous_radial_relative_error_upper"] == "495/100352"
    assert r["all_dirichlet_eigenvalues_continuum_sector_domain"]
    assert not r["certified_cartesian_fd_eigensolver_error"]
    for m in (3,6,9):
        errors=[
            Fraction(module.certificate(m,n)["relative_eigenvalue_error_upper"])
            for n in (64,128,256,512)
        ]
        assert all(x>y for x,y in zip(errors,errors[1:]))
        assert module.minimal_sector_count(m,Fraction(1,100)) > 0


def test_independent_analytic_spiral_first_hit_parity_smoke():
    pytest.importorskip("scipy")
    spec=importlib.util.spec_from_file_location(
        "gielis_reflection_parity",
        ROOT/"scripts/gielis_reflection_parity.py")
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    r=module.parity(m=3,epsilon=.12,rays=12,segments=384,brackets=3072)
    assert r["rays"] == 12
    assert r["paired"] >= 1
    assert not r["same_as_original_Kozyrev_HTML_SDF"]
    assert not r["grazing_and_tangency_completeness_proved"]


def test_random_angle_hoeffding_optical_receipt_is_explicitly_simulated():
    spec=importlib.util.spec_from_file_location(
        "gielis_optical_statistics",
        ROOT/"scripts/gielis_optical_statistics.py")
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    r=module.matched_random_sweep(rays=24,segments=128,bounces=2,
                                  seed=369,include_controls=False)
    assert r["familywise_simultaneous_coverage_at_least"] == .95
    assert len(r["results"]) == 7
    assert r["no_inference_for_deterministic_grid"]
    for design in r["results"]:
        lo,hi=design["focus_hoeffding_interval"]
        assert lo <= design["focus_fraction"] <= hi
        lo,hi=design["mean_abs_impulse_hoeffding_interval"]
        assert lo <= design["mean_abs_torque"] <= hi
        assert not design["physical_calibration"]



def test_exact_radial_rayleigh_ritz_bound():
    pytest.importorskip("sympy")
    spec=importlib.util.spec_from_file_location(
        "gielis_rayleigh_spectral_bound",
        ROOT/"scripts/gielis_rayleigh_spectral_bound.py")
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    proof=module.theorem()
    assert proof["m3_continuum_lambda1_upper_rational_strict"]=="1273/264"
    assert proof["m3_upper_decimal"]<4.822
    assert not proof["certified_numeric_FD_error"]


def test_new_smooth_spiral_first_hit_refinement():
    pytest.importorskip("scipy")
    spec=importlib.util.spec_from_file_location(
        "gielis_reflection_parity_convergence",
        ROOT/"scripts/gielis_reflection_parity.py")
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    coarse=module.parity(m=3,epsilon=.12,rays=20,segments=384,brackets=6144)
    fine=module.parity(m=3,epsilon=.12,rays=20,segments=1536,brackets=6144)
    assert coarse["paired"]>=1 and fine["paired"]>=1
    assert coarse["unpaired"]==0 and fine["unpaired"]==0
    assert fine["max_first_hit_error_m"]<coarse["max_first_hit_error_m"]
    assert not fine["same_as_original_Kozyrev_HTML_SDF"]


def test_original_pr1404_kozyrev_bridge_fails_closed_without_sources(tmp_path):
    spec=importlib.util.spec_from_file_location(
        "gielis_kozyrev_pr1404_bridge",
        ROOT/"scripts/gielis_kozyrev_pr1404_bridge.py")
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    receipt=module.match_original_owners(tmp_path,segments=128,
                                         first_hit_rays=12)
    assert receipt["status"]=="NOT_CHECKED"
    assert receipt["original_pr"]==1404
    assert not receipt["original_HTML_SDF_parity"]
    assert set(receipt["missing_original_files"]) == set(module.ORIGINAL_FILES)


def test_kozyrev_legacy_pr1404_baseline_mathematical_centerline_identity():
    import math
    t=np.linspace(0.,3*math.pi,257)
    geom= g.spiral_vertices(3,0.,segments=256)
    theta=t
    r=.75*np.exp(math.log(1.55/.75)*theta/(3*math.pi))
    independent=np.column_stack((r*np.cos(theta),r*np.sin(theta)))
    np.testing.assert_allclose(geom,independent,rtol=0,atol=1e-14)


def test_kozyrev_bridge_real_sources_if_checked_out():
    spec=importlib.util.spec_from_file_location(
        "gielis_kozyrev_pr1404_bridge",
        ROOT/"scripts/gielis_kozyrev_pr1404_bridge.py")
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    receipt=module.match_original_owners(segments=256,first_hit_rays=24)
    if receipt["status"]=="NOT_CHECKED":
        pytest.skip("PR1404 original owners are in a different open Git ref")
    assert receipt["status"]=="CENTRELINE_PARITY_CHECKED"
    assert receipt["matched_centreline_max_position_error_m"]<1e-12
    assert receipt["first_hit_comparison_skipped"]==0
    assert receipt["first_hit_max_difference_m"]<1e-11
    assert receipt["power_ledger_event_count"]>=1
    assert receipt["max_angular_residual_Nm"]<1e-12
    assert not receipt["original_HTML_SDF_parity"]


def test_hoeffding_paired_random_angle_baseline_controls():
    spec=importlib.util.spec_from_file_location(
        "gielis_optical_statistics_paired",
        ROOT/"scripts/gielis_optical_statistics.py")
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    receipt=module.matched_random_sweep(rays=36,segments=128,bounces=2,
                                        seed=369,include_controls=True)
    assert len(receipt["paired_baseline_intervals"]) == 12
    assert receipt["paired_familywise_coverage_at_least"] == .95
    for row in receipt["paired_baseline_intervals"]:
        lo,hi=row["focus_difference_simultaneous_interval"]
        assert lo <= row["focus_difference_from_baseline"] <= hi
        lo,hi=row["impulse_difference_simultaneous_interval"]
        assert lo <= row["absolute_impulse_difference_from_baseline"] <= hi
        assert row["interpretation"].endswith("only")
