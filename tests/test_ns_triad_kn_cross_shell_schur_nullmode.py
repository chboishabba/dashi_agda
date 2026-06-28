from __future__ import annotations

import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DOC = REPO_ROOT / "docs" / "ns_triad_kn_cross_shell_schur_nullmode.md"
SIGNED_DOC = REPO_ROOT / "docs" / "ns_triad_kn_cross_shell_signed_domination.md"
SCRIPT = REPO_ROOT / "scripts" / "ns_triad_kn_cross_shell_schur_symbolic_audit.py"
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
DOMINATION_SECTOR_FRAME_SUMMARY_10121416 = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_cross_shell_domination_ratio_sector_frame_audit_10121416_20260626"
    / "schur_audit.json"
)
RESTRICTED_SECTOR_SUMMARY_12 = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_cross_shell_restricted_sector_audit_n12_20260626"
    / "schur_audit.json"
)
HALO_GROWTH_SUMMARY_12 = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_cross_shell_domination_halo_growth_n12_20260627"
    / "schur_audit.json"
)
COARSE_QUOTIENT_SUMMARY_12 = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_cross_shell_domination_coarse_quotient_n12_20260627"
    / "schur_audit.json"
)
COARSE_QUOTIENT_PARITY_SUMMARY_12 = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_cross_shell_domination_coarse_quotient_parity_n12_20260627"
    / "schur_audit.json"
)
ROW_PAIRING_SUMMARY_12 = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_cross_shell_domination_row_pairing_n12_20260627"
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
    assert "comparative \\(N=10,12,14,16\\) sector/frame audit" in text
    assert "\\((1,7,N)\\)" in text
    assert "restricted-sector localization test at \\(N=12\\)" in text
    assert "about \\(7.03\\)" in text
    assert "about \\(0.057\\)" in text
    assert "first halo-growth audit at \\(N=12\\)" in text
    assert "dimension \\(6352\\)" in text
    assert "about \\(0.997\\)" in text
    assert "first coarse-quotient audit at \\(N=12\\)" in text
    assert "\\(167\\) classes" in text
    assert "\\rho_{\\mathrm{quotient}} \\approx 0.433" in text
    assert "`shell-zero-orbit-parity` quotient" in text
    assert "\\(334\\) classes" in text
    assert "\\rho_{\\mathrm{quotient}} \\approx 0.507" in text
    assert "row-pairing audit at `N=12`" in text
    assert "naive row ratios are badly above one" in text
    assert "lambda_min(Q|1_C^⊥) ≈ 1.11e-4" in text
    assert "Waleffe helical decomposition is now the best candidate representation lens" in text
    assert "phase-based Schur sign split" in text
    assert "not yet identified with a helical triad operator" in text
    assert "Q_N = D_N + E_N" in text
    assert "0.595611 < 1" in text
    assert "not a uniform theorem" in text
    assert "N = 6, 8, 10, 14, 16" in text
    assert "GPU/Vulkan reuse from `../dashiCORE` is a performance scout only" in text
    assert "`vulkan-scout` backend" in text
    assert "positive off-diagonals occur in the dense sign audit" in text
    assert "balanced signed graph" in text
    assert "single live Gate 1 proof obligation" in text
    assert "signedDominationProbeInstalled = true" in text
    assert "qHelicalCouplingBoundObserved = true" in text
    assert "qHelicalCouplingUniformlyBounded = false" in text
    assert "qHelicalBlockFloorUniformlyProved = false" in text
    assert "signedDominationRatioUniformlyBounded = false" in text
    assert "gpuSchurMatvecInstalled = true" in text
    assert "gpuCpuParityObserved = false" in text
    assert "gpuHelicalCouplingScout = false" in text
    assert "gpuKnAuthority = false" in text
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


def test_helical_lift_audit_is_wired_fail_closed_in_script_source() -> None:
    text = SCRIPT.read_text(encoding="utf-8")
    assert "--audit-q-helical-lift" in text
    assert "--audit-q-helical-coupling-certificate" in text
    assert "--helical-coupling-max-dense-dim" in text
    assert "--write-schur-checkpoint" in text
    assert "--read-schur-checkpoint" in text
    assert "profile_from_weight_matrices" in text
    assert "vulkan-scout" in text
    assert "qHelicalLiftAuditInstalled" in text
    assert "qHelicalCouplingCertificateAuditInstalled" in text
    assert "qHelicalCouplingBoundObserved" in text
    assert "qHelicalCouplingUniformlyBounded" in text
    assert "gpuSchurMatvecInstalled" in text
    assert "gpuCpuParityObserved" in text
    assert "gpuHelicalCouplingScout" in text
    assert "skipped_oom_guard" in text
    assert "Q_N = D_N + E_N" in text
    assert "waleffeHelicalBasisRelevantObserved" in text
    assert "qHelicalBlockDiagonalizationObserved" in text
    assert "qHelicalSectorPsdProved" in text
    assert "qEqualsWaleffeTriadOperatorProved" in text
    assert "qGlobalPsdProved" in text
    assert "candidate canonical helical-channel lift" in text
    assert "Current DASHI Q acts on scalar seam amplitudes" in text
    assert "checkpoint overlay" in text
    assert "Partial receipt" in text


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


def test_sector_frame_audit_10121416_records_global_nonaxis_pattern() -> None:
    payload = json.loads(DOMINATION_SECTOR_FRAME_SUMMARY_10121416.read_text(encoding="utf-8"))
    rows = {row["N"]: row for row in payload["rows"]}
    assert set(rows) == {10, 12, 14, 16}

    mixed_shell_ratios: dict[int, float] = {}
    for shell in (10, 12, 14, 16):
        row = rows[shell]
        diag = row["domination_ratio_matrix_free_diagnostics"]
        assert diag["domination_ratio_sup_one_perp"] < 2.0 / 3.0

        sector = diag["symmetry_sector_diagnostics"]
        angular = diag["extremizer_angular_frame_diagnostics"]
        assert sector is not None
        assert angular is not None

        rho_total = diag["domination_ratio_sup_one_perp"]
        rho_nonaxis = sector["axis_class_component_ratio"]["nonaxis"]["ratio"]
        rho_zero_free = sector["zero_coordinate_class_component_ratio"]["0-zero"]["ratio"]
        assert abs(rho_total - rho_nonaxis) < 1.0e-4
        assert rho_zero_free < rho_total

        orbit_mass = sector["coordinate_permutation_orbit_mass"]
        top_orbits = list(orbit_mass)[:2]
        assert f"(0,1,{shell - 1})" in top_orbits
        assert f"(1,7,{shell})" in top_orbits
        if shell != 12:
            assert orbit_mass[f"(1,7,{shell})"] > orbit_mass.get(f"(1,{shell - 5},{shell})", 0.0)

        source = diag["source_decomposition"]
        mixed_shell = source["shell_pair"][f"{shell - 1}<->{shell}"]["ratio"]
        mixed_shell_ratios[shell] = mixed_shell
        assert mixed_shell > rho_total

        target_mass = angular["pairwise_dot_target_mass"]
        assert target_mass["-1/2"] > 0.0
        assert target_mass["0"] > 0.0
        assert angular["frame_trace_over_operator_norm"] > 1.2

    assert mixed_shell_ratios[12] > mixed_shell_ratios[10]
    assert mixed_shell_ratios[12] > mixed_shell_ratios[14]
    assert mixed_shell_ratios[12] > mixed_shell_ratios[16]


def test_restricted_sector_audit_n12_rules_out_two_orbit_localization() -> None:
    payload = json.loads(RESTRICTED_SECTOR_SUMMARY_12.read_text(encoding="utf-8"))
    rows = {row["N"]: row for row in payload["rows"]}
    assert set(rows) == {12}

    row = rows[12]
    full_diag = row["domination_ratio_matrix_free_diagnostics"]
    restricted = row["domination_ratio_restricted_sector_diagnostics"]
    assert full_diag["status"] == "ok"
    assert restricted["status"] == "ok"
    assert restricted["gpu_kn_authority"] is False
    assert restricted["matvec_backend"] == "cpu"
    assert restricted["sector_spec"]["nonaxis_only"] is True
    assert restricted["sector_spec"]["orbit_labels"][:2] == ["(0,1,11)", "(1,7,12)"]
    assert restricted["sector_dimension"] == 72
    assert full_diag["domination_ratio_sup_one_perp"] < 2.0 / 3.0
    assert restricted["domination_ratio_sup_one_perp"] > 1.0

    comparison = restricted["full_comparison"]
    assert comparison["rho_ratio_to_full"] > 10.0
    assert comparison["full_extremizer_sector_projected_overlap"] < 0.1
    assert comparison["full_extremizer_sector_mass"] < 0.2


def test_halo_growth_audit_n12_shows_one_step_near_global_closure() -> None:
    payload = json.loads(HALO_GROWTH_SUMMARY_12.read_text(encoding="utf-8"))
    rows = {row["N"]: row for row in payload["rows"]}
    assert set(rows) == {12}

    row = rows[12]
    diag = row["domination_halo_growth_diagnostics"]
    assert diag["status"] == "ok"
    assert diag["gpu_kn_authority"] is False
    assert diag["best_radius"] is None

    radii = diag["radii"]
    assert len(radii) == 2

    radius0, radius1 = radii
    assert radius0["radius"] == 0
    assert radius0["sector_dimension"] == 72
    assert radius0["domination_ratio_sup_one_perp"] > 7.0
    assert radius0["rho_ratio_to_full"] > 10.0
    assert radius0["full_extremizer_sector_projected_overlap"] < 0.1
    assert radius0["boundary_flux_ratio"] > 0.8

    assert radius1["radius"] == 1
    assert radius1["sector_dimension"] == 6352
    assert radius1["rho_ratio_to_full"] < 1.01
    assert radius1["full_extremizer_sector_projected_overlap"] > 0.99
    assert radius1["full_extremizer_sector_mass"] > 0.999
    assert radius1["good_energy_capture"] > 0.99
    assert radius1["bad_energy_capture"] > 0.99
    assert radius1["boundary_flux_ratio"] > 0.49


def test_coarse_quotient_audits_n12_rule_out_first_class_indicator_compressions() -> None:
    payload_basic = json.loads(COARSE_QUOTIENT_SUMMARY_12.read_text(encoding="utf-8"))
    payload_parity = json.loads(COARSE_QUOTIENT_PARITY_SUMMARY_12.read_text(encoding="utf-8"))

    row_basic = payload_basic["rows"][0]
    row_parity = payload_parity["rows"][0]
    diag_basic = row_basic["domination_coarse_quotient_diagnostics"]
    diag_parity = row_parity["domination_coarse_quotient_diagnostics"]

    assert payload_basic["coarseQuotientDominationAuditInstalled"] is True
    assert payload_parity["coarseQuotientDominationAuditInstalled"] is True

    assert diag_basic["status"] == "ok"
    assert diag_basic["scheme"] == "shell-zero-orbit"
    assert diag_basic["sector_dimension"] == 6352
    assert diag_basic["class_count"] == 167
    assert diag_basic["quotient_domination_ratio_sup_one_perp"] < 0.5
    assert diag_basic["full_comparison"]["rho_ratio_to_full"] < 0.7
    assert diag_basic["full_comparison"]["full_extremizer_projected_overlap"] < 0.1

    assert diag_parity["status"] == "ok"
    assert diag_parity["scheme"] == "shell-zero-orbit-parity"
    assert diag_parity["sector_dimension"] == 6352
    assert diag_parity["class_count"] == 334
    assert diag_parity["quotient_domination_ratio_sup_one_perp"] < 0.55
    assert diag_parity["full_comparison"]["rho_ratio_to_full"] < 0.8
    assert diag_parity["full_comparison"]["full_extremizer_projected_overlap"] < 0.2

    assert diag_parity["quotient_domination_ratio_sup_one_perp"] > diag_basic["quotient_domination_ratio_sup_one_perp"]
    assert diag_parity["full_comparison"]["full_extremizer_projected_overlap"] > diag_basic["full_comparison"]["full_extremizer_projected_overlap"]


def test_row_pairing_audit_n12_rules_out_naive_rowwise_domination_but_keeps_q_psd() -> None:
    payload = json.loads(ROW_PAIRING_SUMMARY_12.read_text(encoding="utf-8"))
    assert payload["rowPairingDominationAuditInstalled"] is True

    rows = {row["N"]: row for row in payload["rows"]}
    assert set(rows) == {12}
    row = rows[12]
    full_diag = row["domination_ratio_matrix_free_diagnostics"]
    diag = row["domination_row_pairing_diagnostics"]

    assert full_diag["domination_ratio_sup_one_perp"] < 2.0 / 3.0
    assert diag["status"] == "ok"
    assert diag["Q_psd_observed_on_one_perp"] is True
    assert diag["Q_lambda_min_one_perp"] > 0.0
    assert diag["Q_sign_diagnostics"]["ordinary_laplacian_candidate"] is False
    assert diag["Q_sign_diagnostics"]["num_positive_offdiag"] > 0
    assert diag["Q_sign_diagnostics"]["min_diag"] < 0.0
    assert diag["Q_sign_diagnostics"]["gershgorin_lower_bound"] < 0.0
    assert diag["Q_row_sum_max_abs"] < 1.0e-12

    assert diag["max_row_3bad_2good_ratio"] > 1.6
    assert diag["mean_row_3bad_2good_ratio"] > 1.4
    assert diag["rows_with_3bad_2good_ratio_above_one"] > 6000
    assert diag["extremizer_mass_weighted_row_3bad_2good_ratio"] > 1.4

    worst = diag["worst_rows_by_3bad_2good_ratio"][0]
    assert worst["mode"] == [11, 1, -10]
    assert worst["row_3bad_2good_ratio"] > 1.6

    top_ext = diag["extremizer_top_rows"][0]
    assert top_ext["mode"] == [1, -7, 12]
    assert top_ext["row_3bad_2good_ratio"] > 1.5
