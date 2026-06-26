from __future__ import annotations

import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DOC = REPO_ROOT / "docs" / "ns_triad_kn_cross_shell_schur_nullmode.md"
SIGNED_DOC = REPO_ROOT / "docs" / "ns_triad_kn_cross_shell_signed_domination.md"
SUMMARY = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_cross_shell_schur_audit_20260626"
    / "schur_audit.json"
)
SIGNED_SUMMARY = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_cross_shell_schur_signed_factorization_audit_20260625"
    / "schur_audit.json"
)
DOMINATION_SUMMARY_10 = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_cross_shell_domination_ratio_audit_20260626"
    / "schur_audit.json"
)
DOMINATION_SUMMARY_HI = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_cross_shell_domination_ratio_audit_hi_20260626"
    / "schur_audit.json"
)
DOMINATION_SUMMARY_16 = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_cross_shell_domination_ratio_audit_n16_20260626"
    / "schur_audit.json"
)
DOMINATION_SECTOR_SUMMARY_12 = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_cross_shell_domination_ratio_sector_audit_n12_20260626"
    / "schur_audit.json"
)


def test_schur_nullmode_doc_uses_candidate_only_language() -> None:
    text = DOC.read_text(encoding="utf-8")
    squashed = " ".join(text.split())
    assert "Schur/Kron-style gauge mode" in text
    assert "supporting evidence" in text
    assert "No promotion claim made." in text
    assert "matrix-free `eigsh`" in text
    assert "Observed at N=6,8,10,12,14. Proof open; live route is signed domination." in text
    assert "S_C \\mathbf{1}_C = 0" in text
    assert "constant-on-\\(C\\) null mode is not merely observed numerically" in text
    assert "ordinary Kron-reduced edge weights" in text
    assert "uniform signed domination bound" in squashed
    assert "Do not upgrade this to a generic \"balanced signed graph\" theorem." in text


def test_signed_domination_doc_records_live_gate1_target() -> None:
    text = SIGNED_DOC.read_text(encoding="utf-8")
    squashed = " ".join(text.split())
    assert "This is the live Gate 1 theorem surface." in text
    assert "\\rho_6 \\approx 0.6076" in text
    assert "\\rho_8 \\approx 0.6257" in text
    assert "\\rho_{10} \\approx 0.6144" in text
    assert "\\rho_{12} \\approx 0.6577" in text
    assert "\\rho_{14} \\approx 0.5956" in text
    assert "\\rho_{16} \\approx 0.5812" in text
    assert "below \\(2/3\\)" in text
    assert "The focused \\(N=12\\) symmetry audit" in text
    assert "86\\%" in text
    assert "positive off-diagonals occur in the dense sign audit" in text
    assert "balanced signed graph" in text
    assert "single live Gate 1 proof obligation" in text
    assert "signedDominationProbeInstalled = true" in text
    assert "signedDominationRatioUniformlyBounded = false" in text
    assert "Focused Agda check: passed" in text
    assert "Full Everything.agda check: attempted, killed exit 137" in text
    assert "Exit `137` is an environment/resource failure, not a proof failure." in text
    assert "sup_{x \\perp \\mathbf{1}_C}" in squashed


def test_schur_audit_summary_records_matrix_free_receipt_flags() -> None:
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["candidate_only"] is True
    assert payload["theorem_promoted"] is False
    assert payload["gate1_closed"] is False
    assert payload["gate1_supported_at_tested_shells"] is True
    assert payload["schurNullModeIsConstantProved"] is True
    assert payload["kronStyleSchurReductionIdentified"] is True
    assert payload["ordinaryKronLaplacianIdentified"] is False
    assert payload["effectiveOffdiagNonpositiveProved"] is False
    assert payload["effectiveGraphConnectedObserved"] is False
    assert payload["effectiveGraphConnectedProved"] is False
    assert payload["schurComplementPsdVerified"] is True
    assert payload["schurComplementNullityOneObserved"] is True
    assert payload["schurSignedPsdRequired"] is True
    assert payload["signedDominationProbeInstalled"] is False
    assert payload["signedDominationRatioBelowOneObserved"] is False
    assert payload["signedDominationRatioUniformlyBounded"] is False
    assert payload["schurComplementMatrixFreeAuditInstalled"] is True
    assert payload["schurNullModeConstantOnCObserved"] is True
    assert payload["schurComplementPsdProved"] is False
    assert payload["schurNullModeIdentified"] is False
    assert payload["schurSignedFactorizationProved"] is False
    assert payload["schurNullModeFactorizationProved"] is False
    assert payload["gate1ConditionalTheoremProved"] is False
    assert payload["ordinaryKronLaplacianRoute"] is False
    assert payload["balancedSignedGraphRoute"] is False

    rows = {row["N"]: row for row in payload["rows"]}
    assert set(rows) == {12, 14}
    for shell in (12, 14):
        row = rows[shell]
        assert row["verdict"] == "schur_psd"
        assert row["S_C"]["evaluation_method"] == "eigsh"
        assert row["S_C"]["nullity_estimate"] == 1
        assert len(row["S_C"]["bottom_eigs"]) == 3
        assert row["row_sum_diagnostics"]["max_abs_row_sum"] < 1.0e-12
        assert abs(row["null_vector_diagnostics"]["corr_constant"]) > 0.999
        sign_diag = row["effective_laplacian_sign_diagnostics"]
        assert sign_diag["audit_requested"] is True
        assert sign_diag["dense_audit_available"] is False
        assert sign_diag["route_verdict"] == "signed_psd_required"


def test_dense_signed_factorization_audit_records_domination_probe() -> None:
    payload = json.loads(SIGNED_SUMMARY.read_text(encoding="utf-8"))
    assert payload["candidate_only"] is True
    assert payload["theorem_promoted"] is False
    assert payload["gate1_closed"] is False
    assert payload["effectiveGraphConnectedObserved"] is True
    assert payload["schurSignedPsdRequired"] is True
    assert payload["signedDominationProbeInstalled"] is True
    assert payload["signedDominationRatioBelowOneObserved"] is True
    assert payload["signedDominationRatioUniformlyBounded"] is False
    assert payload["schurComplementPsdVerified"] is True
    assert payload["schurComplementNullityOneObserved"] is True
    assert payload["schurSignedFactorizationProved"] is False
    assert payload["gate1ConditionalTheoremProved"] is False
    assert payload["ordinaryKronLaplacianRoute"] is False
    assert payload["balancedSignedGraphRoute"] is False

    rows = {row["N"]: row for row in payload["rows"]}
    assert set(rows) == {6, 8}
    for shell in (6, 8):
        row = rows[shell]
        assert row["verdict"] == "schur_psd"
        sign_diag = row["effective_laplacian_sign_diagnostics"]
        assert sign_diag["dense_audit_available"] is True
        assert sign_diag["route_verdict"] == "signed_psd_required"
        assert sign_diag["num_positive_offdiag"] > 0
        assert sign_diag["negative_edge_support_components"] == 1
        factor_diag = row["signed_factorization_diagnostics"]
        assert factor_diag["dense_audit_available"] is True
        assert factor_diag["decomposition"] == "S_C = L_good - L_bad"
        assert factor_diag["L_good_nullity_estimate"] == 1
        assert factor_diag["domination_ratio_sup_one_perp"] < 1.0
        assert factor_diag["domination_holds_strictly_observed"] is True


def test_matrix_free_domination_ratio_audits_record_10_12_14_16() -> None:
    payload_10 = json.loads(DOMINATION_SUMMARY_10.read_text(encoding="utf-8"))
    payload_hi = json.loads(DOMINATION_SUMMARY_HI.read_text(encoding="utf-8"))
    payload_16 = json.loads(DOMINATION_SUMMARY_16.read_text(encoding="utf-8"))

    rows_10 = {row["N"]: row for row in payload_10["rows"]}
    rows_hi = {row["N"]: row for row in payload_hi["rows"]}
    rows_16 = {row["N"]: row for row in payload_16["rows"]}

    assert set(rows_10) == {10}
    assert set(rows_hi) == {12, 14}
    assert set(rows_16) == {16}

    expected_upper = {10: 2.0 / 3.0, 12: 2.0 / 3.0, 14: 2.0 / 3.0, 16: 2.0 / 3.0}
    all_rows = {**rows_10, **rows_hi, **rows_16}
    for shell, row in all_rows.items():
        assert row["verdict"] == "schur_psd"
        assert row["S_C"]["nullity_estimate"] == 1
        diag = row["domination_ratio_matrix_free_diagnostics"]
        assert diag["status"] == "ok"
        assert diag["domination_holds_strictly_observed"] is True
        assert diag["domination_ratio_sup_one_perp"] < expected_upper[shell]
        assert diag["L_good_lambda1_one_perp"] > 0.0
        assert diag["L_bad_lambda_max_one_perp"] > 0.0
        assert diag["worst_eigenvector_diagnostics"]["axis_concentration"] < 0.001
        shell_mass = diag["worst_eigenvector_diagnostics"]["shell_mass"]
        assert len(shell_mass) == 2
        assert max(shell_mass.values()) < 0.6
        top_modes = diag["worst_eigenvector_diagnostics"]["top_modes"]
        assert len(top_modes) >= 5
        assert top_modes[0]["is_axis"] is False


def test_n12_sector_audit_records_nonaxis_zero_free_resonance() -> None:
    payload = json.loads(DOMINATION_SECTOR_SUMMARY_12.read_text(encoding="utf-8"))
    rows = {row["N"]: row for row in payload["rows"]}
    assert set(rows) == {12}
    row = rows[12]
    diag = row["domination_ratio_matrix_free_diagnostics"]
    assert diag["status"] == "ok"
    assert diag["domination_ratio_sup_one_perp"] < 2.0 / 3.0

    sector = diag["symmetry_sector_diagnostics"]
    assert sector is not None
    assert sector["axis_class_mass"]["nonaxis"] > 0.999
    assert sector["zero_coordinate_class_mass"]["0-zero"] > 0.86
    assert sector["zero_coordinate_class_mass"]["1-zero"] < 0.14

    orbit_mass = sector["coordinate_permutation_orbit_mass"]
    top_orbits = list(orbit_mass)[:2]
    assert top_orbits == ["(1,7,12)", "(0,1,11)"]

    shell_ratio = sector["shell_class_component_ratio"]
    assert shell_ratio["shell-11"]["ratio"] < 0.58
    assert shell_ratio["shell-12"]["ratio"] < 0.58

    axis_ratio = sector["axis_class_component_ratio"]
    assert axis_ratio["nonaxis"]["ratio"] > 0.65
    assert axis_ratio["axis"]["ratio"] < 0.2

    source = diag["source_decomposition"]
    assert source["shell_pair"]["11<->12"]["ratio"] > 0.7
    assert source["shell_pair"]["11<->11"]["ratio"] < 2.0 / 3.0
    assert source["shell_pair"]["12<->12"]["ratio"] < 2.0 / 3.0
