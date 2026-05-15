#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import importlib
import json
import math
import sys
from pathlib import Path
from typing import Any, Callable

EXIT_USAGE = 64
EXIT_DIGEST_MISMATCH = 20
EXIT_PARSE_ERROR = 21
EXIT_PREDICTION_MISSING = 42
EXIT_PREDICTION_INVALID = 43
EXIT_STRICT_COMPARISON_INVALID = 44

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

DATA_DIR = REPO_ROOT / "scripts" / "data" / "hepdata"
T43_PATH = DATA_DIR / "ins2079374_phistar_mass_50-76_over_mass_76-106_t43.csv"
T44_PATH = DATA_DIR / "ins2079374_Covariance_phistar_mass_50-76_over_mass_76-106_t44.csv"
T45_PATH = DATA_DIR / "ins2079374_phistar_mass_106-170_over_mass_76-106_t45.csv"
T46_PATH = DATA_DIR / "ins2079374_Covariance_phistar_mass_106-170_over_mass_76-106_t46.csv"
T21_PATH = DATA_DIR / "ins2079374_phistar_mass_76-106_t21.csv"
T22_PATH = DATA_DIR / "ins2079374_Covariance_phistar_mass_76-106_t22.csv"

KNOWN_DIGESTS = {
    T21_PATH.name: "4ece677d0e2640a786351e19d0190454aeb3dc49f7e6fbda4814e3fe88dc3270",
    T22_PATH.name: "718588d67d3c41195d25a6f01c4ff4bcf2d0d85c193e27ebd22925474a0d9ea7",
    T43_PATH.name: "0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b",
    T44_PATH.name: "3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b",
    T45_PATH.name: "bcc1450c5c7818e2792f06f1882c6facdea2e4079070b777f2c5ac3b87343433",
    T46_PATH.name: "e325d82ec3ba6962042c54f6b98a911d456f9bf00db22d2238b0cd76e71dcb3f",
}


def display_path(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def verify_digest(path: Path) -> dict[str, Any]:
    expected = KNOWN_DIGESTS.get(path.name)
    if expected is None:
        if not path.exists():
            return {
                "path": display_path(path),
                "sha256": None,
                "expectedSha256": None,
                "status": "missing",
            }
        return {
            "path": display_path(path),
            "sha256": None,
            "expectedSha256": None,
            "status": "unknown-input",
        }
    try:
        actual = sha256_file(path)
    except OSError as exc:
        return {
            "path": display_path(path),
            "sha256": None,
            "expectedSha256": expected,
            "status": "unreadable",
            "error": str(exc),
        }
    return {
        "path": display_path(path),
        "sha256": actual,
        "expectedSha256": expected,
        "status": "ok" if actual == expected else "mismatch",
    }


def _to_float(raw: str, *, context: str) -> float:
    try:
        value = float(raw)
    except ValueError as exc:
        raise ValueError(f"{context}: expected float, got {raw!r}") from exc
    if not math.isfinite(value):
        raise ValueError(f"{context}: expected finite float, got {raw!r}")
    return value


def read_hepdata_csv(path: Path) -> tuple[list[str], list[list[str]], list[str]]:
    comments: list[str] = []
    records: list[list[str]] = []
    header: list[str] | None = None

    with path.open("r", encoding="utf-8", newline="") as handle:
        for raw_line in handle:
            if raw_line.startswith("#:"):
                comments.append(raw_line.rstrip("\n"))
                continue
            if not raw_line.strip():
                continue
            row = next(csv.reader([raw_line]))
            if header is None:
                header = row
            else:
                records.append(row)

    if header is None:
        raise ValueError(f"{path}: missing CSV header")
    return header, records, comments


def parse_t43(path: Path) -> dict[str, Any]:
    header, rows, comments = read_hepdata_csv(path)
    expected_prefix = [
        "$\\varphi^*$",
        "$\\varphi^*$ LOW",
        "$\\varphi^*$ HIGH",
    ]
    if header[:3] != expected_prefix or len(header) < 4:
        raise ValueError(f"{path}: unexpected data header prefix {header[:4]!r}")
    value_column = header[3]

    bins: list[dict[str, Any]] = []
    for index, row in enumerate(rows):
        if len(row) != len(header):
            raise ValueError(f"{path}: row {index} has {len(row)} fields, expected {len(header)}")
        bins.append(
            {
                "index": index,
                "phiStar": _to_float(row[0], context=f"t43 row {index} phiStar"),
                "phiStarLow": _to_float(row[1], context=f"t43 row {index} phiStarLow"),
                "phiStarHigh": _to_float(row[2], context=f"t43 row {index} phiStarHigh"),
                "ratio": _to_float(row[3], context=f"t43 row {index} ratio"),
                "valueColumn": value_column,
                "uncertainties": {
                    header[column]: _to_float(row[column], context=f"t43 row {index} {header[column]}")
                    for column in range(4, len(header))
                },
            }
        )

    return {
        "path": display_path(path),
        "commentPreamble": comments,
        "columns": header,
        "valueColumn": value_column,
        "rowCount": len(bins),
        "bins": bins,
    }


def _comment_value(comments: list[str], key: str) -> str | None:
    prefix = f"#: {key}:"
    for comment in comments:
        if comment.startswith(prefix):
            return comment[len(prefix):].strip()
    return None


def selection_metadata_for_t43(t43: dict[str, Any], *, prediction_mode: str) -> dict[str, Any]:
    comments = t43.get("commentPreamble", [])
    if not isinstance(comments, list):
        comments = []
    description = _comment_value(comments, "description") or ""
    observable = _comment_value(comments, "keyword observables") or t43.get("valueColumn", "")
    table_doi = _comment_value(comments, "table_doi") or "MISSING"
    cm_energy = _comment_value(comments, "keyword cmenergies") or "MISSING"
    name = _comment_value(comments, "name") or "phistar mass 50-76 over mass 76-106"
    at_least_one_jet = "At least one jet is required" in description
    not_bin_width_normalized = "not normalized by the bin width" in description

    missing_fields = [
        "central_acceptance_A",
        "acceptance_source",
        "emst_fiducial_power_correction_surface",
    ]
    missing_critical = [
        "central_acceptance_A",
        "emst_fiducial_power_correction_surface",
    ]

    return {
        "record": "ins2079374",
        "hepdata_doi": table_doi,
        "ratio_table_doi": table_doi,
        "covariance_table_doi": "10.17182/hepdata.115656.v1/t44",
        "observable": observable,
        "observable_name": observable,
        "table_name": name,
        "process": "pp -> Z/gamma* -> ll + >=1 jet",
        "sqrt_s_GeV": int(cm_energy) if str(cm_energy).isdigit() else cm_energy,
        "dataset_label": "t43_below_Z",
        "numerator_mass_window_GeV": {"low": 50.0, "high": 76.0, "high_inclusive": False},
        "denominator_mass_window_GeV": {"low": 76.0, "high": 106.0, "high_inclusive": False},
        "ratio_numerator_mass_window_GeV": [50.0, 76.0],
        "ratio_denominator_mass_window_GeV": [76.0, 106.0],
        "mass_window_source": "HEPData t43 table preamble",
        "fiducial_selection_source": {
            "analysis": "CMS-SMP-20-003",
            "arxiv": "2205.04897",
            "paper_doi": "10.1140/epjc/s10052-023-11631-7",
            "source_section": "Event selection and unfolding particle-level phase space",
            "source_notes": [
                "arXiv source SMP-20-003_temp.tex lines 163-197",
                "particle-level phase-space statement lines 346-352",
                "jet clustering statement lines 153-154",
            ],
        },
        "at_least_one_jet": at_least_one_jet,
        "requires_at_least_one_jet": at_least_one_jet,
        "jet_pT_min_GeV": 30.0,
        "jet_rapidity_abs_max": 2.4,
        "jet_eta_max": "not_used_particle_level_uses_abs_y_lt_2p4",
        "jet_algorithm": "anti-kt",
        "jet_radius": 0.4,
        "jet_lepton_deltaR_min": 0.4,
        "b_tagged_jet_veto": True,
        "leading_lepton_pT_min_GeV": 25.0,
        "subleading_lepton_pT_min_GeV": 20.0,
        "lepton_pT_min_GeV": {"leading": 25.0, "subleading": 20.0},
        "lepton_eta_max": 2.4,
        "lepton_isolation": "exactly_two_isolated_leptons_same_flavour_opposite_charge; detailed isolation criteria referenced to CMS Sirunyan:2019bzr",
        "lepton_flavour": "ee_or_mumu_combined_after_compatibility_check",
        "third_lepton_veto": {"pT_min_GeV": 10.0, "eta_abs_max": 2.4},
        "trigger_channel": {
            "dielectron": {"leading_pT_threshold_GeV": 23.0, "subleading_pT_threshold_GeV": 12.0},
            "dimuon": {"leading_pT_threshold_GeV": 18.0, "subleading_pT_threshold_GeV": 7.0},
            "single_muon": {"pT_threshold_GeV": 24.0},
        },
        "central_acceptance_A": "MISSING",
        "acceptance_source": "MISSING",
        "bin_convention": "not_bin_width_normalized_ratio_values"
        if not_bin_width_normalized
        else "UNKNOWN",
        "bin_variable": "phiStar",
        "values_normalized_by_bin_width": not not_bin_width_normalized,
        "phi_star_bin_count": t43.get("rowCount"),
        "phi_star_bin_edges_source": "t43 CSV LOW/HIGH columns",
        "prediction_bin_treatment": prediction_mode,
        "bin_integration_status": "not_implemented_for_sigma_dashi_v4_strict_log_contract",
        "acceptance_metadata_status": "fiducial_selection_complete_acceptance_surface_missing",
        "missing_fields": missing_fields,
        "missing_fields_count": len(missing_fields),
        "missing_critical": missing_critical,
        "comparison_contract_status": "non_promoting",
        "strict_log_interpretation": (
            "chi2/dof is informative but not a pure shape-law test until "
            "the fiducial acceptance contract is represented in the predictor"
        ),
        "reason": (
            "sigma_dashi_v4 is compared against a fiducial unfolded HEPData "
            "ratio table requiring at least one jet. The CMS fiducial selection "
            "metadata is now machine-readable, but the local predictor still "
            "does not encode the central A(M,phi*) acceptance surface or EMST "
            "fiducial power-correction surface, so strict-log chi2 conflates "
            "acceptance gaps with shape-law failure."
        ),
    }


def warn_incomplete_acceptance_contract(selection_metadata: dict[str, Any]) -> None:
    if selection_metadata.get("acceptance_metadata_status") == "complete":
        return
    print("  WARNING: strict-log chi2 computed with incomplete acceptance contract.")
    print(f"  Missing critical fields: {selection_metadata.get('missing_critical', [])}")
    print("  chi2 result is informative but NOT promotable until contract is complete.")
    print()


def parse_t44(path: Path, bins: list[dict[str, Any]]) -> dict[str, Any]:
    header, rows, comments = read_hepdata_csv(path)
    expected_prefix = [
        "$\\varphi^*$",
        "$\\varphi^*$ LOW",
        "$\\varphi^*$ HIGH",
        "$\\varphi^*$",
        "$\\varphi^*$ LOW",
        "$\\varphi^*$ HIGH",
    ]
    if header[:6] != expected_prefix or len(header) != 7:
        raise ValueError(f"{path}: unexpected t44 header {header!r}")

    sections: dict[str, list[list[str]]] = {header[6]: []}
    current_label = header[6]
    for row in rows:
        if row[:6] == expected_prefix and len(row) == 7:
            current_label = row[6]
            sections.setdefault(current_label, [])
            continue
        sections[current_label].append(row)

    n = len(bins)
    total_label = next((label for label in sections if label.startswith("Total uncertainty")), None)
    if total_label is None:
        raise ValueError(f"{path}: missing Total uncertainty covariance section")
    total_rows = sections[total_label]
    if len(total_rows) != n * n:
        raise ValueError(
            f"{path}: expected {n * n} Total uncertainty covariance rows for {n} bins, got {len(total_rows)}"
        )

    by_bin = {
        (round(item["phiStar"], 15), round(item["phiStarLow"], 15), round(item["phiStarHigh"], 15)): item["index"]
        for item in bins
    }
    covariance = [[0.0 for _ in range(n)] for _ in range(n)]
    entries: list[dict[str, Any]] = []

    for row_index, row in enumerate(total_rows):
        if len(row) != len(header):
            raise ValueError(f"{path}: row {row_index} has {len(row)} fields, expected {len(header)}")
        left = tuple(round(_to_float(row[column], context=f"t44 row {row_index} left {column}"), 15) for column in range(3))
        right = tuple(round(_to_float(row[column], context=f"t44 row {row_index} right {column}"), 15) for column in range(3, 6))
        if left not in by_bin or right not in by_bin:
            raise ValueError(f"{path}: row {row_index} references a bin not present in t43")
        i = by_bin[left]
        j = by_bin[right]
        value = _to_float(row[6], context=f"t44 row {row_index} total uncertainty")
        covariance[i][j] = value
        entries.append({"row": i, "column": j, "totalUncertainty": value})

    symmetric = all(
        math.isclose(covariance[i][j], covariance[j][i], rel_tol=1e-12, abs_tol=1e-18)
        for i in range(n)
        for j in range(n)
    )

    return {
        "path": display_path(path),
        "commentPreamble": comments,
        "columns": header,
        "rowCount": len(total_rows),
        "sectionCount": len(sections),
        "totalUncertaintySection": total_label,
        "sections": [
            {"name": name, "rowCount": len(section_rows)}
            for name, section_rows in sections.items()
        ],
        "matrixShape": [n, n],
        "symmetric": symmetric,
        "covariance": covariance,
        "entries": entries,
    }


def load_prediction_api(spec: str | None) -> tuple[Callable[[list[dict[str, Any]]], list[float]] | None, str]:
    if not spec:
        return None, "no --prediction-api supplied; compute_dashi_ratio is not wired"
    if ":" not in spec:
        raise ValueError("--prediction-api must use module:function")
    module_name, function_name = spec.split(":", 1)
    module = importlib.import_module(module_name)
    function = getattr(module, function_name)
    if not callable(function):
        raise TypeError(f"{spec} is not callable")
    return function, f"loaded {spec}"


def dirty_z_peak_prediction_contract_status(spec: str | None, value_column: str) -> tuple[str, str | None]:
    if value_column == "Ratio":
        return "ratio", None
    if not spec:
        return "missing", "no --prediction-api supplied for t21 Z-peak d sigma/d phistar [pb]"
    module_name, _, function_name = spec.partition(":")
    try:
        module = importlib.import_module(module_name)
        metadata_function = getattr(module, "metadata", None)
        metadata = metadata_function() if callable(metadata_function) else {}
    except Exception as exc:
        return "invalid", f"prediction API metadata unavailable for dirty-z-peak: {exc}"

    supports_absolute = metadata.get("supportsDirtyZPeakAbsolutePrediction") is True
    declared_absolute = metadata.get("dirtyZPeakAbsolutePredictionCallable") == spec
    if supports_absolute and declared_absolute:
        return "absolute", None

    supports_shape = metadata.get("supportsDirtyZPeakShapePrediction") is True
    declared_shape = metadata.get("dirtyZPeakShapePredictionCallable") == spec
    if supports_shape and declared_shape:
        return "shape-with-fitted-scale", None

    return (
        "invalid",
        "dirty-z-peak requires a batch callable declared by metadata as "
        "either supportsDirtyZPeakAbsolutePrediction with dirtyZPeakAbsolutePredictionCallable "
        "or supportsDirtyZPeakShapePrediction with dirtyZPeakShapePredictionCallable "
        f"matching {spec!r}; {module_name}:{function_name} is not such a callable"
    )


def finalize_artifact(payload: dict[str, Any]) -> dict[str, Any]:
    payload = dict(payload)
    payload["projectionDigest"] = ""
    stable = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["projectionDigest"] = hashlib.sha256(stable.encode("utf-8")).hexdigest()
    return payload


def source_authority_for_mode(mode: str) -> dict[str, Any]:
    if mode == "dirty-z-peak":
        return {
            "record": "ins2079374",
            "measurementTableDoi": "10.17182/hepdata.115656.v1/t21",
            "covarianceTableDoi": "10.17182/hepdata.115656.v1/t22",
        }
    return {
        "record": "ins2079374",
        "ratioTableDoi": "10.17182/hepdata.115656.v1/t43",
        "covarianceTableDoi": "10.17182/hepdata.115656.v1/t44",
    }


def incomplete_artifact(
    *,
    mode: str,
    freeze_hash: str,
    digest_results: list[dict[str, Any]],
    t43: dict[str, Any] | None,
    t44: dict[str, Any] | None,
    reason: str,
    prediction_api_status: str,
) -> dict[str, Any]:
    return finalize_artifact({
        "artifactSchema": "dashi-hepdata-t43-projection-v1",
        "schemaVersion": "0.1.0",
        "generatedUtc": "deterministic-artifact",
        "worker": "HEP-R32",
        "scope": "scripts-only fail-closed t43/t44 projection runner",
        "mode": mode,
        "projectionComplete": False,
        "comparisonLawStatus": "incomplete",
        "failureCode": "prediction-missing",
        "failureReason": reason,
        "nonPromotionBoundary": [
            "no W3 promotion",
            "no W4 promotion",
            "no W5 promotion",
            "no W8 promotion",
            "no empirical adequacy claim",
            "no fake DASHI projection",
        ],
        "predictionFreeze": {
            "freezeHash": freeze_hash,
            "runnerHashBinding": "caller-supplied",
            "worktreeCleanCertificate": "not asserted by this runner",
        },
        "sourceAuthority": source_authority_for_mode(mode),
        "inputs": {
            "digests": digest_results,
            "t43": t43,
            "t44": t44,
        },
        "predictionApi": {
            "expected": "compute_dashi_ratio",
            "status": prediction_api_status,
        },
        "comparison": {
            "chi2": None,
            "chi2PerDof": None,
            "perBinTwoSigmaLaw": None,
            "status": "not-computed",
        },
    })


def _validate_prediction_values(raw: Any, *, expected_len: int) -> list[float]:
    if not isinstance(raw, list):
        raise TypeError("prediction API must return a list[float]")
    if len(raw) != expected_len:
        raise ValueError(f"prediction API returned {len(raw)} values, expected {expected_len}")
    values: list[float] = []
    for index, item in enumerate(raw):
        if not isinstance(item, (int, float)):
            raise TypeError(f"prediction value {index} is not numeric: {item!r}")
        value = float(item)
        if not math.isfinite(value):
            raise ValueError(f"prediction value {index} is not finite: {item!r}")
        values.append(value)
    return values


def _solve_linear_system(matrix: list[list[float]], vector: list[float]) -> list[float]:
    n = len(vector)
    if len(matrix) != n or any(len(row) != n for row in matrix):
        raise ValueError("linear solve requires a square matrix matching the vector length")
    augmented = [list(row) + [vector[index]] for index, row in enumerate(matrix)]
    for column in range(n):
        pivot_row = max(range(column, n), key=lambda row: abs(augmented[row][column]))
        pivot = augmented[pivot_row][column]
        if abs(pivot) < 1.0e-30:
            raise ArithmeticError("covariance matrix is singular for scale fit")
        if pivot_row != column:
            augmented[column], augmented[pivot_row] = augmented[pivot_row], augmented[column]
        pivot = augmented[column][column]
        for item in range(column, n + 1):
            augmented[column][item] /= pivot
        for row in range(n):
            if row == column:
                continue
            factor = augmented[row][column]
            if factor == 0.0:
                continue
            for item in range(column, n + 1):
                augmented[row][item] -= factor * augmented[column][item]
    return [augmented[row][n] for row in range(n)]


def _dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right, strict=True))


def _matrix_condition_estimate(matrix: list[list[float]]) -> float | None:
    diagonal = [abs(row[index]) for index, row in enumerate(matrix)]
    positive = [value for value in diagonal if value > 0.0 and math.isfinite(value)]
    if len(positive) != len(matrix):
        return None
    return max(positive) / min(positive)


def _log_covariance_diagnostics(
    *,
    residual: list[float],
    propagated_covariance: list[list[float]],
    full_chi2: float,
    phi_star_values: list[float],
) -> dict[str, Any]:
    diagonal_terms: list[float] = []
    for index, value in enumerate(residual):
        variance = propagated_covariance[index][index]
        if variance <= 0.0 or not math.isfinite(variance):
            raise ArithmeticError(f"log covariance diagonal variance is invalid at bin {index}: {variance!r}")
        diagonal_terms.append((value * value) / variance)
    diagonal_chi2 = sum(diagonal_terms)
    off_diagonal_contribution = full_chi2 - diagonal_chi2

    diagnostics: dict[str, Any] = {
        "diagnosticStatus": "computed-diagonal-only",
        "diagonalOnlyChi2": diagonal_chi2,
        "diagonalOnlyChi2PerDof": diagonal_chi2 / len(residual),
        "diagonalOnlyTerms": diagonal_terms,
        "fullOverDiagonalChi2": full_chi2 / diagonal_chi2 if diagonal_chi2 > 0.0 else None,
        "offDiagonalContributionToChi2": off_diagonal_contribution,
        "offDiagonalContributionFraction": (
            off_diagonal_contribution / full_chi2 if full_chi2 > 0.0 else None
        ),
        "offDiagonalDominanceDiagnostic": (
            "full-covariance-smaller-than-diagonal"
            if full_chi2 < diagonal_chi2
            else "full-covariance-larger-than-diagonal"
        ),
    }

    try:
        import numpy as np  # type: ignore[import-not-found]
    except Exception as exc:
        diagnostics["eigenmodeStatus"] = "unavailable"
        diagnostics["eigenmodeFailureReason"] = f"numpy import failed: {exc}"
        return diagnostics

    covariance = np.array(propagated_covariance, dtype=float)
    residual_vector = np.array(residual, dtype=float)
    try:
        inverse_covariance = np.linalg.inv(covariance)
        symmetric_inverse = 0.5 * (inverse_covariance + inverse_covariance.T)
        eigenvalues, eigenvectors = np.linalg.eigh(symmetric_inverse)
    except Exception as exc:
        diagnostics["eigenmodeStatus"] = "failed"
        diagnostics["eigenmodeFailureReason"] = str(exc)
        return diagnostics

    order = np.argsort(eigenvalues)[::-1]
    eigenvalues = eigenvalues[order]
    eigenvectors = eigenvectors[:, order]
    projections = eigenvectors.T @ residual_vector
    contributions = eigenvalues * projections * projections
    contribution_sum = float(np.sum(contributions))
    top_count = min(6, len(residual))
    top_modes: list[dict[str, Any]] = []
    for rank in range(top_count):
        vector = eigenvectors[:, rank]
        top_modes.append({
            "rank": rank + 1,
            "eigenvalue": float(eigenvalues[rank]),
            "projection": float(projections[rank]),
            "chi2Contribution": float(contributions[rank]),
            "chi2ContributionFraction": (
                float(contributions[rank] / contribution_sum)
                if contribution_sum > 0.0
                else None
            ),
            "eigenvector": [float(item) for item in vector.tolist()],
        })

    residual_norm = float(np.linalg.norm(residual_vector))
    leading_cosine = None
    if residual_norm > 0.0:
        leading_cosine = float(abs(projections[0]) / residual_norm)
    positive_eigenvalues = [float(value) for value in eigenvalues.tolist() if value > 0.0]

    diagnostics.update({
        "diagnosticStatus": "computed",
        "eigenmodeStatus": "computed",
        "inverseCovarianceSymmetrization": "0.5 * (C^-1 + (C^-1)^T)",
        "eigenvalueOrdering": "descending inverse-covariance eigenvalue",
        "eigenConditionNumber": (
            max(positive_eigenvalues) / min(positive_eigenvalues)
            if len(positive_eigenvalues) == len(residual)
            else None
        ),
        "eigenContributionSum": contribution_sum,
        "eigenContributionVsFullChi2AbsDelta": abs(contribution_sum - full_chi2),
        "leadingModeContributionFraction": (
            float(contributions[0] / contribution_sum)
            if contribution_sum > 0.0
            else None
        ),
        "leadingModeEuclideanCosineAbs": leading_cosine,
        "topInverseCovarianceModes": top_modes,
    })
    if len(phi_star_values) == len(residual) and all(value > 0.0 for value in phi_star_values):
        log_phi = np.log(np.array(phi_star_values, dtype=float))
        design = np.column_stack([np.ones(len(residual)), log_phi])
        try:
            normal = design.T @ symmetric_inverse @ design
            rhs = design.T @ symmetric_inverse @ residual_vector
            coefficients = np.linalg.solve(normal, rhs)
            fitted = design @ coefficients
            residual_minus_fit = residual_vector - fitted
            fitted_chi2 = float(fitted.T @ symmetric_inverse @ fitted)
            remaining_chi2 = float(residual_minus_fit.T @ symmetric_inverse @ residual_minus_fit)
            diagnostics["logPhiLinearSubspaceDiagnostic"] = {
                "status": "computed",
                "basis": ["1", "log(phiStar)"],
                "fitInnerProduct": "inverse propagated log covariance",
                "intercept": float(coefficients[0]),
                "logPhiSlope": float(coefficients[1]),
                "fittedChi2": fitted_chi2,
                "remainingChi2AfterProjection": remaining_chi2,
                "fittedChi2FractionOfFull": fitted_chi2 / full_chi2 if full_chi2 > 0.0 else None,
                "remainingChi2FractionOfFull": remaining_chi2 / full_chi2 if full_chi2 > 0.0 else None,
            }
        except Exception as exc:
            diagnostics["logPhiLinearSubspaceDiagnostic"] = {
                "status": "failed",
                "failureReason": str(exc),
            }
    else:
        diagnostics["logPhiLinearSubspaceDiagnostic"] = {
            "status": "unavailable",
            "failureReason": "phiStar values missing, nonpositive, or length-mismatched",
        }
    return diagnostics


def _log_covariance_transform(
    *,
    data_values: list[float],
    predictions: list[float],
    covariance: list[list[float]],
    threshold: float,
    phi_star_values: list[float],
) -> dict[str, Any]:
    if threshold <= 0.0 or not math.isfinite(threshold):
        raise ValueError("strict chi2/dof threshold must be finite and positive")
    for index, value in enumerate(data_values):
        if value <= 0.0 or not math.isfinite(value):
            raise ValueError(f"log transform requires positive finite data value at bin {index}, got {value!r}")
    for index, value in enumerate(predictions):
        if value <= 0.0 or not math.isfinite(value):
            raise ValueError(f"log transform requires positive finite prediction at bin {index}, got {value!r}")

    log_data = [math.log(value) for value in data_values]
    log_predictions = [math.log(value) for value in predictions]
    residual = [pred - data for pred, data in zip(log_predictions, log_data, strict=True)]
    jacobian = [1.0 / value for value in data_values]
    propagated_covariance = [
        [
            jacobian[i] * covariance[i][j] * jacobian[j]
            for j in range(len(data_values))
        ]
        for i in range(len(data_values))
    ]
    c_inv_residual = _solve_linear_system(propagated_covariance, residual)
    chi2 = _dot(residual, c_inv_residual)
    if chi2 < -1.0e-9 or not math.isfinite(chi2):
        raise ArithmeticError(f"strict log-covariance chi2 is invalid: {chi2!r}")
    chi2 = max(0.0, chi2)
    dof = len(data_values)
    chi2_per_dof = chi2 / dof
    diagnostics = _log_covariance_diagnostics(
        residual=residual,
        propagated_covariance=propagated_covariance,
        full_chi2=chi2,
        phi_star_values=phi_star_values,
    )
    return {
        "transform": "log-ratio",
        "transformKind": "other-declared",
        "thresholdChi2PerDof": threshold,
        "strictProtocolPass": chi2_per_dof <= threshold,
        "fitParameterCount": 0,
        "dof": dof,
        "chi2": chi2,
        "chi2PerDof": chi2_per_dof,
        "residualDefinition": "log(R_pred) - log(R_data)",
        "covariancePropagationLaw": "C_log[i,j] = C_raw[i,j] / (R_data[i] * R_data[j])",
        "jacobianDiagonal": jacobian,
        "logData": log_data,
        "logPredictions": log_predictions,
        "logResiduals": residual,
        "propagatedCovariance": propagated_covariance,
        "diagnostics": diagnostics,
        "solver": "Gauss-Jordan solve of propagated covariance; no regularization",
        "conditionEstimateFromDiagonal": _matrix_condition_estimate(propagated_covariance),
        "failurePolicy": [
            "fail closed on nonpositive data or predictions",
            "fail closed on singular propagated covariance",
            "fail closed on undeclared prediction API",
            "no scalar refit and no posterior retuning",
        ],
    }


def _fit_dirty_z_peak_scale(
    shape_predictions: list[float],
    data_values: list[float],
    covariance: list[list[float]],
) -> dict[str, Any]:
    c_inv_data = _solve_linear_system(covariance, data_values)
    c_inv_shape = _solve_linear_system(covariance, shape_predictions)
    denominator = _dot(shape_predictions, c_inv_shape)
    if denominator <= 0.0 or not math.isfinite(denominator):
        raise ArithmeticError("non-positive denominator in dirty Z-peak scale fit")
    numerator = _dot(shape_predictions, c_inv_data)
    scale = numerator / denominator
    if not math.isfinite(scale) or scale <= 0.0:
        raise ArithmeticError("non-finite or non-positive dirty Z-peak scale fit")
    scaled = [scale * value for value in shape_predictions]
    residual = [prediction - data for prediction, data in zip(scaled, data_values, strict=True)]
    c_inv_residual = _solve_linear_system(covariance, residual)
    chi2 = _dot(residual, c_inv_residual)
    dof = max(len(data_values) - 1, 1)
    return {
        "scale": scale,
        "scaledPredictions": scaled,
        "chi2": chi2,
        "chi2PerDof": chi2 / dof,
        "dof": dof,
        "fitParameterCount": 1,
        "method": "covariance-weighted scalar fit: argmin_A (A shape - data)^T C^-1 (A shape - data)",
    }


def completed_projection_artifact(
    *,
    mode: str,
    freeze_hash: str,
    digest_results: list[dict[str, Any]],
    t43: dict[str, Any],
    t44: dict[str, Any],
    prediction_api_status: str,
    predictions: list[float],
    prediction_mode: str = "direct",
    calibration: dict[str, Any] | None = None,
    strict_comparison: dict[str, Any] | None = None,
) -> dict[str, Any]:
    bins: list[dict[str, Any]] = []
    per_bin: list[dict[str, Any]] = []
    selection_metadata = selection_metadata_for_t43(
        t43,
        prediction_mode=prediction_mode,
    )
    for row, prediction in zip(t43["bins"], predictions, strict=True):
        data = row["ratio"]
        index = row["index"]
        uncertainty = math.sqrt(t44["covariance"][index][index])
        residual = prediction - data
        pull = residual / uncertainty if uncertainty > 0.0 else 0.0
        bins.append(
            {
                "index": index,
                "phiStar": row["phiStar"],
                "phiStarLow": row["phiStarLow"],
                "phiStarHigh": row["phiStarHigh"],
                "R_data": data,
                "R_dashi": prediction,
                "residual": residual,
                "uncertainties": row["uncertainties"],
            }
        )
        per_bin.append(
            {
                "bin": index,
                "phiStar": row["phiStar"],
                "phiStarLow": row["phiStarLow"],
                "phiStarHigh": row["phiStarHigh"],
                "pred": prediction,
                "data": data,
                "unc": uncertainty,
                "pull": pull,
            }
        )

    return finalize_artifact({
        "artifactSchema": "dashi-hepdata-t43-projection-v1",
        "schemaVersion": "0.1.0",
        "generatedUtc": "deterministic-artifact",
        "worker": "HEP-R33",
        "scope": "digest-bound t43/t44 projection runner with caller-supplied prediction API",
        "mode": mode,
        "projectionComplete": True,
        "comparisonLawStatus": "not-claimed",
        "failureCode": None,
        "failureReason": None,
        "nonPromotionBoundary": [
            "no W3 promotion",
            "no W4 promotion",
            "no W5 promotion",
            "no W8 promotion",
            "no empirical adequacy claim",
            "projection artifact still requires comparison-law receipt review",
            "strict log-covariance diagnostics are non-promoting unless a separate receipt accepts them",
        ],
        "predictionFreeze": {
            "freezeHash": freeze_hash,
            "runnerHashBinding": "caller-supplied",
            "worktreeCleanCertificate": "not asserted by this runner",
        },
        "sourceAuthority": source_authority_for_mode(mode),
        "inputs": {
            "digests": digest_results,
            "t43": {
                "path": t43["path"],
                "columns": t43["columns"],
                "rowCount": t43["rowCount"],
            },
            "t44": {
                "path": t44["path"],
                "columns": t44["columns"],
                "rowCount": t44["rowCount"],
                "sectionCount": t44["sectionCount"],
                "matrixShape": t44["matrixShape"],
                "symmetric": t44["symmetric"],
            },
        },
        "predictionApi": {
            "expected": "batch callable: list[t43 bin dict] -> list[float]",
            "status": prediction_api_status,
            "predictionMode": prediction_mode,
        },
        "calibration": calibration,
        "strictComparison": strict_comparison,
        "selection_metadata": selection_metadata,
        "acceptance_metadata_status": selection_metadata["acceptance_metadata_status"],
        "comparison_contract_status": selection_metadata["comparison_contract_status"],
        "at_least_one_jet": selection_metadata["at_least_one_jet"],
        "bins": bins,
        "per_bin": per_bin,
        "comparison": {
            "chi2": (
                strict_comparison["chi2"]
                if strict_comparison is not None
                else None if calibration is None else calibration["chi2"]
            ),
            "chi2PerDof": (
                strict_comparison["chi2PerDof"]
                if strict_comparison is not None
                else None if calibration is None else calibration["chi2PerDof"]
            ),
            "perBinTwoSigmaLaw": None,
            "status": (
                "strict-log-covariance"
                if strict_comparison is not None
                else "not-computed" if calibration is None else "dirty-z-peak-scale-fit"
            ),
        },
    })


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Fail-closed HEPData ratio/covariance DASHI projection runner.")
    parser.add_argument(
        "--freeze-hash",
        "--freeze",
        dest="freeze_hash",
        required=True,
        help="Caller-supplied prediction freeze hash.",
    )
    parser.add_argument(
        "--output",
        default="/tmp/t43_projection_diagnostic.json",
        help="JSON artifact path. Defaults to /tmp/t43_projection_diagnostic.json.",
    )
    parser.add_argument(
        "--mode",
        choices=["t43-ratio", "dirty-z-peak", "t43-strict-log"],
        default="t43-ratio",
        help="Diagnostic mode label. t43-strict-log computes a non-promoting log-covariance chi2/dof diagnostic.",
    )
    parser.add_argument("--t43", dest="data", default=str(T43_PATH), help="Path to t43 ratio CSV.")
    parser.add_argument("--t44", dest="covariance", default=str(T44_PATH), help="Path to t44 covariance CSV.")
    parser.add_argument("--data", dest="data", help="Path to measurement/ratio CSV. Alias for --t43.")
    parser.add_argument("--covariance", dest="covariance", help="Path to covariance CSV. Alias for --t44.")
    parser.add_argument(
        "--prediction-api",
        help="Optional module:function callable. Omit until compute_dashi_ratio is wired.",
    )
    parser.add_argument(
        "--strict-threshold",
        type=float,
        default=2.0,
        help="Strict diagnostic chi2/dof threshold for t43-strict-log. Defaults to 2.0.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    t43_path = Path(args.data)
    t44_path = Path(args.covariance)
    output_path = Path(args.output)

    digest_results = [verify_digest(t43_path), verify_digest(t44_path)]
    if any(result["status"] != "ok" for result in digest_results):
        artifact = incomplete_artifact(
            mode=args.mode,
            freeze_hash=args.freeze_hash,
            digest_results=digest_results,
            t43=None,
            t44=None,
            reason="data/covariance digest verification failed",
            prediction_api_status="not-attempted",
        )
        artifact["failureCode"] = "digest-mismatch"
        artifact = finalize_artifact(artifact)
        write_json(output_path, artifact)
        return EXIT_DIGEST_MISMATCH

    try:
        t43 = parse_t43(t43_path)
        t44 = parse_t44(t44_path, t43["bins"])
    except Exception as exc:
        artifact = incomplete_artifact(
            mode=args.mode,
            freeze_hash=args.freeze_hash,
            digest_results=digest_results,
            t43=None,
            t44=None,
            reason=f"data/covariance CSV parse failed: {exc}",
            prediction_api_status="not-attempted",
        )
        artifact["failureCode"] = "parse-error"
        artifact = finalize_artifact(artifact)
        write_json(output_path, artifact)
        return EXIT_PARSE_ERROR

    try:
        prediction_api, prediction_status = load_prediction_api(args.prediction_api)
    except Exception as exc:
        prediction_api = None
        prediction_status = f"unavailable: {exc}"

    if prediction_api is None:
        artifact = incomplete_artifact(
            mode=args.mode,
            freeze_hash=args.freeze_hash,
            digest_results=digest_results,
            t43=t43,
            t44=t44,
            reason="DASHI ratio prediction is unavailable; compute_dashi_ratio is not wired",
            prediction_api_status=prediction_status,
        )
        write_json(output_path, artifact)
        return EXIT_PREDICTION_MISSING

    dirty_prediction_mode, dirty_contract_error = (
        dirty_z_peak_prediction_contract_status(args.prediction_api, t43["valueColumn"])
        if args.mode == "dirty-z-peak"
        else ("direct", None)
    )
    if dirty_contract_error is not None:
        artifact = incomplete_artifact(
            mode=args.mode,
            freeze_hash=args.freeze_hash,
            digest_results=digest_results,
            t43=t43,
            t44=t44,
            reason=dirty_contract_error,
            prediction_api_status=prediction_status,
        )
        artifact["failureCode"] = "prediction-contract-missing"
        artifact = finalize_artifact(artifact)
        write_json(output_path, artifact)
        return EXIT_PREDICTION_MISSING

    try:
        raw_predictions = _validate_prediction_values(
            prediction_api(t43["bins"]),
            expected_len=t43["rowCount"],
        )
    except Exception as exc:
        artifact = incomplete_artifact(
            mode=args.mode,
            freeze_hash=args.freeze_hash,
            digest_results=digest_results,
            t43=t43,
            t44=t44,
            reason=f"prediction API returned invalid output: {exc}",
            prediction_api_status=prediction_status,
        )
        artifact["failureCode"] = "prediction-invalid"
        artifact = finalize_artifact(artifact)
        write_json(output_path, artifact)
        return EXIT_PREDICTION_INVALID

    calibration = None
    strict_comparison = None
    predictions = raw_predictions
    if args.mode == "dirty-z-peak" and dirty_prediction_mode == "shape-with-fitted-scale":
        try:
            calibration = _fit_dirty_z_peak_scale(
                raw_predictions,
                [row["ratio"] for row in t43["bins"]],
                t44["covariance"],
            )
            predictions = calibration["scaledPredictions"]
        except Exception as exc:
            artifact = incomplete_artifact(
                mode=args.mode,
                freeze_hash=args.freeze_hash,
                digest_results=digest_results,
                t43=t43,
                t44=t44,
                reason=f"dirty Z-peak scale fit failed: {exc}",
                prediction_api_status=prediction_status,
            )
            artifact["failureCode"] = "calibration-fit-invalid"
            artifact = finalize_artifact(artifact)
            write_json(output_path, artifact)
            return EXIT_PREDICTION_INVALID
    elif args.mode == "t43-strict-log":
        try:
            warn_incomplete_acceptance_contract(
                selection_metadata_for_t43(
                    t43,
                    prediction_mode=dirty_prediction_mode,
                )
            )
            strict_comparison = _log_covariance_transform(
                data_values=[row["ratio"] for row in t43["bins"]],
                predictions=predictions,
                covariance=t44["covariance"],
                threshold=args.strict_threshold,
                phi_star_values=[row["phiStar"] for row in t43["bins"]],
            )
        except Exception as exc:
            artifact = incomplete_artifact(
                mode=args.mode,
                freeze_hash=args.freeze_hash,
                digest_results=digest_results,
                t43=t43,
                t44=t44,
                reason=f"strict log-covariance comparison failed: {exc}",
                prediction_api_status=prediction_status,
            )
            artifact["failureCode"] = "strict-comparison-invalid"
            artifact["strictComparison"] = {
                "transform": "log-ratio",
                "thresholdChi2PerDof": args.strict_threshold,
                "status": "failed-closed",
                "failureReason": str(exc),
            }
            artifact = finalize_artifact(artifact)
            write_json(output_path, artifact)
            return EXIT_STRICT_COMPARISON_INVALID

    artifact = completed_projection_artifact(
        mode=args.mode,
        freeze_hash=args.freeze_hash,
        digest_results=digest_results,
        t43=t43,
        t44=t44,
        prediction_api_status=prediction_status,
        predictions=predictions,
        prediction_mode=dirty_prediction_mode,
        calibration=calibration,
        strict_comparison=strict_comparison,
    )
    write_json(output_path, artifact)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except BrokenPipeError:
        raise SystemExit(EXIT_USAGE)
