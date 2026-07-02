from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = REPO_ROOT / "scripts" / "ns_triad_kn_cross_shell_schur_symbolic_audit.py"
SCRIPTS_DIR = str(REPO_ROOT / "scripts")
if SCRIPTS_DIR not in sys.path:
    sys.path.insert(0, SCRIPTS_DIR)

SPEC = importlib.util.spec_from_file_location("ns_triad_kn_cross_shell_schur_symbolic_audit", MODULE_PATH)
assert SPEC is not None
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)

_schur_complement_from_blocks = MODULE._schur_complement_from_blocks
_gate2a_transport_margin_diagnostics = MODULE._gate2a_transport_margin_diagnostics
_projected_quadratic_form_comparison = MODULE._projected_quadratic_form_comparison
_gate2a_schur_sign_split_comparison_diagnostics = (
    MODULE._gate2a_schur_sign_split_comparison_diagnostics
)
_schur_lift_identity_diagnostics = MODULE._schur_lift_identity_diagnostics
_schur_lift_operator = MODULE._schur_lift_operator


def test_schur_lift_operator_gives_exact_pullback_identity() -> None:
    a_gg = np.asarray([[3.0, 0.4], [0.4, 2.0]], dtype=np.float64)
    a_gc = np.asarray([[0.5, -0.3], [0.2, 0.6]], dtype=np.float64)
    a_cc = np.asarray([[2.5, 0.1], [0.1, 1.7]], dtype=np.float64)
    a_cg = a_gc.T
    a_blk = np.block([[a_gg, a_gc], [a_cg, a_cc]])

    schur = _schur_complement_from_blocks(a_gg, a_gc, a_cc)
    lift = _schur_lift_operator(a_gg, a_gc)
    pulled_back = lift.T @ a_blk @ lift

    assert np.allclose(pulled_back, schur, atol=1.0e-12, rtol=1.0e-12)


def test_schur_lift_identity_diagnostics_reports_exact_identity() -> None:
    a_gg = np.asarray([[4.0]], dtype=np.float64)
    a_gc = np.asarray([[1.0, -2.0]], dtype=np.float64)
    a_cc = np.asarray([[3.0, 0.2], [0.2, 5.0]], dtype=np.float64)
    a_blk = np.block([[a_gg, a_gc], [a_gc.T, a_cc]])

    diag = _schur_lift_identity_diagnostics(a_blk, ng=1)

    assert diag["status"] == "ok"
    assert diag["g_dim"] == 1
    assert diag["c_dim"] == 2
    assert diag["identity_holds"] is True
    assert diag["defect_max_abs"] <= 1.0e-12


def test_projected_quadratic_form_comparison_recovers_exact_scale() -> None:
    base = np.asarray(
        [
            [2.0, -1.0, -1.0],
            [-1.0, 1.0, 0.0],
            [-1.0, 0.0, 1.0],
        ],
        dtype=np.float64,
    )
    diag = _projected_quadratic_form_comparison(2.5 * base, base)

    assert diag["status"] == "ok"
    assert diag["comparable"] is True
    assert abs(diag["lower_bound"] - 2.5) <= 1.0e-12
    assert abs(diag["upper_bound"] - 2.5) <= 1.0e-12


def test_gate2a_comparison_diag_records_nontrivial_comparison_surface() -> None:
    ln_block = np.asarray(
        [
            [2.0, -1.0, -1.0],
            [-1.0, 1.0, 0.0],
            [-1.0, 0.0, 1.0],
        ],
        dtype=np.float64,
    )
    la_block = np.asarray(
        [
            [3.0, -2.0, -1.0],
            [-2.0, 2.0, 0.0],
            [-1.0, 0.0, 1.0],
        ],
        dtype=np.float64,
    )
    s_c = _schur_complement_from_blocks(
        ln_block[:1, :1] - MODULE.C0 * la_block[:1, :1],
        ln_block[:1, 1:] - MODULE.C0 * la_block[:1, 1:],
        ln_block[1:, 1:] - MODULE.C0 * la_block[1:, 1:],
    )

    diag = _gate2a_schur_sign_split_comparison_diagnostics(
        S_C=s_c,
        Ln_block=ln_block,
        La_block=la_block,
        ng=1,
        c0=MODULE.C0,
    )

    assert diag["status"] == "ok"
    assert diag["comparison_target"].startswith("Compare Schur(L_neg)")
    assert diag["common_comparison_map_constructed"] is False
    assert diag["schur_neg_vs_L_bad_bounds_one_perp"]["status"] in {"ok", "denominator_not_coercive"}
    assert diag["schur_abs_vs_L_good_bounds_one_perp"]["status"] in {"ok", "denominator_not_coercive"}


def test_gate2a_transport_margin_diag_records_directional_and_coarse_ledgers() -> None:
    l_good = np.asarray(
        [
            [2.0, -1.0, -1.0],
            [-1.0, 1.0, 0.0],
            [-1.0, 0.0, 1.0],
        ],
        dtype=np.float64,
    )
    l_bad = 0.4 * l_good
    schur_abs = 2.0 * l_good
    schur_neg = 0.8 * l_bad
    x = np.asarray([1.0, -0.5, -0.5], dtype=np.float64)

    diag = _gate2a_transport_margin_diagnostics(
        schur_neg=schur_neg,
        schur_abs=schur_abs,
        L_bad=l_bad,
        L_good=l_good,
        seam_extremizer=x,
        seam_rho=0.4,
        coarse_abs_lower=1.5,
        coarse_neg_upper=0.9,
    )

    assert diag["status"] == "ok"
    assert diag["directional_transported_ratio"] > 0.0
    assert diag["coarse_transported_upper_bound"] > 0.0
    assert diag["directional_improvement_over_coarse"] is not None
