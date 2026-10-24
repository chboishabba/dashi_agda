#!/usr/bin/env python3
"""Source-bounded exploratory paired-DMT vs placebo fMRI connectivity.

Inspired by the metric TYPE in Timmermann et al. PNAS 2023,
DOI 10.1073/pnas.2218949120, DMT_Imaging/Scripts/StaticGFC.m.
NOT a paper re-run: preprocessing, exclusions, time alignment and nuisance
regression are external. No claims about qualia, hidden targets or entities.
Primary source static GFC: t(15)=3.11, p=0.007, 95% CI [0.028,0.15]
for eight minutes post-injection, with n=16 distinct paired participants.
"""
from __future__ import annotations
import json
from dataclasses import dataclass
from pathlib import Path
import numpy as np
from scipy.io import loadmat
from scipy import stats


@dataclass(frozen=True)
class ConnectivityResult:
    parcels: int
    timepoints: int
    mean_fisher_z_including_zero_diagonal: float
    mean_fisher_z_excluding_diagonal: float


def static_connectivity(bold: np.ndarray,
                        expected_parcels: int | None = 112) -> ConnectivityResult:
    """BOLD_AAL rows=parcel, cols=time per the original dRSFC.m.

    Preserve the StaticGFC convention of zeroing the diagonal before averaging
    while additionally returning an explicitly off-diagonal alternative.
    Neither windows nor edges are independent subjects.
    """
    arr = np.asarray(bold, dtype=np.float64)
    if arr.ndim != 2:
        raise ValueError("BOLD_AAL must be a 2D parcel-by-time matrix")
    n, t = arr.shape
    if n < 3 or t < 22 or (expected_parcels is not None and n != expected_parcels):
        raise ValueError("Unexpected number of parcels/timepoints")
    if not np.isfinite(arr).all() or (np.std(arr, axis=1) <= 1e-12).any():
        raise ValueError("Nonfinite or near-constant parcel series")
    corr = np.corrcoef(arr)
    if not np.isfinite(corr).all():
        raise ValueError("Nonfinite correlations")
    mask = ~np.eye(n, dtype=bool)
    edges = corr[mask]
    if (np.abs(edges) >= 1.0).any():
        raise ValueError("Perfect parcel correlation creates infinite Fisher z")
    z = np.arctanh(edges)
    return ConnectivityResult(n, t, float(z.sum()/(n*n)), float(z.mean()))


def load_parcelled_mat(path: Path, variable: str = "BOLD_AAL") -> np.ndarray:
    try:
        obj = loadmat(path, variable_names=[variable], squeeze_me=False)
    except (OSError, ValueError, NotImplementedError) as error:
        raise ValueError("Cannot read verified MATLAB v5 BOLD parcel matrix") from error
    if variable not in obj:
        raise ValueError("Missing expected BOLD_AAL variable")
    return np.asarray(obj[variable], dtype=np.float64)


def paired_effects(pairs: dict[str, tuple[np.ndarray, np.ndarray]],
                   expected_parcels: int | None = 112) -> dict:
    """Exploratory effect over independent subject pairs, not time frames."""
    if len(pairs) < 2:
        raise ValueError("At least two independently eligible pairs required")
    subjects = sorted(pairs)
    deltas = []
    for subject in subjects:
        dmt, pcb = pairs[subject]
        x = static_connectivity(dmt, expected_parcels)
        y = static_connectivity(pcb, expected_parcels)
        if (x.parcels, x.timepoints) != (y.parcels, y.timepoints):
            raise ValueError("Paired DMT/placebo shape mismatch for " + subject)
        deltas.append(x.mean_fisher_z_including_zero_diagonal -
                      y.mean_fisher_z_including_zero_diagonal)
    delta = np.asarray(deltas)
    if not np.isfinite(delta).all():
        raise ValueError("Nonfinite paired effect")
    avg = float(delta.mean())
    if np.std(delta, ddof=1) <= 1e-12:
        return {"subjects": len(subjects), "mean_delta": avg,
                "status": "degenerate_variance_no_t_inference", "p_two_sided": None,
                "source_claim": "synthetic_or_exploratory_not_replayed"}
    t = float(avg / (delta.std(ddof=1) / np.sqrt(len(delta))))
    p = float(2 * stats.t.sf(abs(t), len(delta) - 1))
    width = float(stats.t.ppf(0.975, len(delta) - 1) *
                  delta.std(ddof=1)/np.sqrt(len(delta)))
    return {"subjects": len(subjects), "mean_delta": avg,
            "ci95_subject_level": [avg-width, avg+width],
            "t_subject_level": t, "p_two_sided": p,
            "status": "exploratory_paired_connectivity_not_original_paper_replay",
            "source_claim": "synthetic_or_exploratory_not_replayed"}


def pair_verified_files(manifest: dict, eligible_subjects: list[str]) -> dict[str, dict[str, str]]:
    """Explicit source-derived eligibility; never infer 15 subjects from 20 files."""
    if len(set(eligible_subjects)) != len(eligible_subjects) or not eligible_subjects:
        raise ValueError("Eligibility list must be explicit and unique")
    declared = set(manifest.get("motion_eligible_subjects", []))
    if not declared or declared != set(eligible_subjects):
        raise ValueError("Eligibility list not locked to source manifest")
    if not manifest.get("motion_exclusion_source_reference"):
        raise ValueError("Missing original motion-quality exclusion receipt")
    by_subject: dict[str, dict[str, str]] = {s: {} for s in eligible_subjects}
    for e in manifest.get("files", []):
        s = e["subject_id"]
        if s in by_subject:
            condition = e["condition"]
            if condition in by_subject[s]:
                raise ValueError("Duplicate subject-condition")
            by_subject[s][condition] = e["relative_path"]
    if any(set(row) != {"DMT", "placebo"} for row in by_subject.values()):
        raise ValueError("Unpaired or missing condition for QC-eligible subject")
    return by_subject


# Source-specific consumer identification, not universally interchangeable QC.
# Original PNAS main static GFC: four of twenty excluded in post-DMT 8 min.
# Three further excluded in original full-28-minute dynamic analyses.
# The public repository README's n=15 concerns a separately described cohort.
PUBLISHED_STATIC_GFC = {
    "paper": "Timmermann et al. PNAS (2023) doi:10.1073/pnas.2218949120",
    "analysis": "original_static_gfc",
    "eligible_subject_count": 16,
    "time_tr_seconds": 2.0,
    "window_minutes_after_scan_start": [8, 16],
    "target_t": 3.11,
    "target_p_two_sided": 0.007,
    "target_ci95": [0.028, 0.15],
}
EXPLORATORY_PARCELLED_ANALYSIS = "exploratory_parcelled_static_fc"
ORIGINAL_DYNAMIC_ELIGIBLE_N = 13
PUBLIC_REPO_README_SURVIVED_MOTION_N = 15
ORIGINAL_JOINT_EEG_FMRI_N = 12


def declared_static_window(bold: np.ndarray) -> np.ndarray:
    """Eight-minute immediately post-injection window: sample [240:480] at TR=2s.

    Caller must separately document time alignment and preprocessed file origin.
    Source-compliant index arithmetic does not certify source-compliant data.
    """
    if bold.ndim != 2 or bold.shape[1] < 480:
        raise ValueError("Postinjection 8-16min requires >=480 TR-aligned samples")
    result = bold[:, 240:480]
    if result.shape[1] != 240:
        raise AssertionError("Invalid frozen eight-minute analysis window")
    return result




def evaluate_verified_manifest(data_root: Path, manifest_path: Path,
                               source_receipt: Path | None = None) -> dict:
    """Admission for BOLD_AAL exploratory comparison; NEVER source-equivalent PNAS replay."""
    from preflight_dmt_imaging_data import check_manifest
    gate = check_manifest(data_root, manifest_path, source_receipt)
    if gate["status"] != "admissible_manifest_only":
        raise ValueError("File/right/source preflight blocked: " + repr(gate["errors"]))
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    analysis = manifest.get("analysis")
    if analysis == PUBLISHED_STATIC_GFC["analysis"]:
        raise ValueError("Original StaticGFC requires voxelwise preprocessed NIfTI and "
                         "Schaeff1007NExt atlas, not source-released BOLD_AAL MAT")
    if analysis != EXPLORATORY_PARCELLED_ANALYSIS:
        raise ValueError("This evaluator admits only exploratory_parcelled_static_fc")
    if manifest.get("input_representation") != "BOLD_AAL_MAT":
        raise ValueError("Input is not explicitly the released parcelled BOLD_AAL MAT representation")
    if manifest.get("source_metric_relationship") != "exploratory_not_source_equivalent":
        raise ValueError("Source equivalence not established; exploratory analysis required")
    eligibility = manifest.get("motion_eligible_subjects")
    if (not isinstance(eligibility, list)
            or len(eligibility) != PUBLISHED_STATIC_GFC["eligible_subject_count"]
            or len(set(eligibility)) != len(eligibility)):
        raise ValueError("Exploratory n16 comparison requires an independently justified 16-person eligible set")
    if not manifest.get("motion_exclusion_source_reference"):
        raise ValueError("Original motion exclusion requires an author/QC provenance receipt")
    if not manifest.get("alignment_preprocessing_source_reference"):
        raise ValueError("Exploratory comparison requires a verified preprocessing/time-alignment receipt")
    file_pairs = pair_verified_files(manifest, eligibility)
    matrices = {s: (load_parcelled_mat(data_root / row["DMT"]),
                    load_parcelled_mat(data_root / row["placebo"]))
                for s, row in file_pairs.items()}
    sliced = {person: (declared_static_window(dmt), declared_static_window(pcb))
              for person, (dmt, pcb) in matrices.items()}
    result = paired_effects(sliced)
    result["analysis"] = analysis
    result["input_representation"] = "BOLD_AAL_MAT"
    result["source_metric_relationship"] = "exploratory_not_source_equivalent"
    result["original_source_input_match"] = False
    result["original_source_execution_reproduced"] = False
    result["published_original_static_gfc_target"] = PUBLISHED_STATIC_GFC.copy()
    result["reference_original_static_cohort_count"] = len(eligibility)
    result["source_analysis_window_tr"] = [240, 480]
    result["matching_paper_measurement_reproduced"] = False
    result.update({
        "source_commit": gate["source_commit"],
        "source_repo": gate["source_repo"],
        "file_hashes_verified": gate["git_source_blob_checks_passed"],
        "motion_exclusion_source_reference": manifest["motion_exclusion_source_reference"],
        "alignment_preprocessing_source_reference": manifest["alignment_preprocessing_source_reference"],
        "participant_ids_reported": False,
        "full_preprocessing_reproduction": False,
        "brainit_training_or_evaluation_performed": False,
        "subjective_qualia_or_entity_identification": False,
    })
    return result


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-root", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--source-receipt", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = evaluate_verified_manifest(args.data_root, args.manifest, args.source_receipt)
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print(json.dumps({"status": "blocked", "reason": str(exc),
                          "data_replayed": False}))
        return 2
    as_json = json.dumps(result, indent=2, sort_keys=True)
    if args.output:
        args.output.write_text(as_json+"\n", encoding="utf-8")
    else:
        print(as_json)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
