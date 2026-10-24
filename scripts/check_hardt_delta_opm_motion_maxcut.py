#!/usr/bin/env python3
"""Synthetic low-frequency biomagnetic source/motion identification gates.

No human EEG/OPM/MEG data are loaded. This is a source-specific exact-rational
counterexample and receipt validator, not a numerical replication of any paper.
Original method inspirations: Christiano & Michelmann (2026), 10.1162/IMAG.a.1218;
Yu et al. (2026), 10.1016/j.bspc.2026.110149; prior OPM gradiometry.
"""
from __future__ import annotations
import argparse
import json
import re
from fractions import Fraction as Q
from itertools import product
from math import isclose, sin, pi, isfinite
from pathlib import Path


def rref(matrix):
    a = [[Q(v) for v in row] for row in matrix]
    if not a:
        return [], []
    assert all(len(row) == len(a[0]) for row in a)
    lead, pivots = 0, []
    for col in range(len(a[0])):
        k = next((i for i in range(lead, len(a)) if a[i][col]), None)
        if k is None:
            continue
        a[lead], a[k] = a[k], a[lead]
        scale = a[lead][col]
        a[lead] = [v / scale for v in a[lead]]
        for i in range(len(a)):
            if i != lead:
                c = a[i][col]
                a[i] = [v - c*w for v, w in zip(a[i], a[lead])]
        pivots.append(col)
        lead += 1
        if lead == len(a):
            break
    return a, pivots


def rank(rows):
    return len(rref(rows)[1]) if rows else 0


def null_basis(rows):
    """Build exact source-nullspace witnesses independently of rank admission."""
    reduced, pivots = rref(rows)
    n = len(rows[0])
    basis = []
    for j in range(n):
        if j in pivots:
            continue
        vector = [Q(0)] * n
        vector[j] = Q(1)
        for i, p in enumerate(pivots):
            vector[p] = -reduced[i][j]
        assert all(sum(Q(a)*b for a,b in zip(row,vector)) == 0 for row in rows)
        basis.append(vector)
    assert len(basis) == n-rank(rows)
    return basis


def field_identifiable(sensors, target):
    """True iff requested linear source contrast factors through sensors."""
    return rank(sensors + [target]) == rank(sensors)


def source_vs_artifact():
    # Coordinates x = [neural source field, movement field, background field].
    brain = [1, 0, 0]
    only_sensor = [[1, 1, 1]]
    ref_sensor = [0, 1, 1]
    same_gain_sensor = [1, 1, 1]
    assert not field_identifiable(only_sensor, brain)
    assert field_identifiable(only_sensor + [ref_sensor], brain)
    assert not field_identifiable(only_sensor + [same_gain_sensor], brain)
    # A reference sensitive to the same neural field can subtract signal too.
    # Even with a clean reference, nuisance components may remain confounded.
    assert not field_identifiable(only_sensor + [ref_sensor], [0, 1, 0])
    vectors = [(1,0,0), (0,1,0), (0,0,1)]
    assert [sum(a*b for a,b in zip(only_sensor[0], v)) for v in vectors] == [1,1,1]
    exhaustive = 0
    for row1, row2 in product(product((-1,0,1), repeat=3), repeat=2):
        if not any(row1) or not any(row2):
            continue
        for target in vectors:
            mat=[row1,row2]
            by_rank = field_identifiable(mat, list(target))
            by_null = all(sum(Q(a)*n for a,n in zip(target,vector)) == 0
                          for vector in null_basis(mat))
            assert by_rank == by_null
            exhaustive += 1
    assert exhaustive == 26 * 26 * 3
    return {"source_coordinates":["brain","motion","background"],
            "single_channel_identifies_brain":False,
            "brain_blind_reference_identifies_brain":True,
            "identical_sensitivity_reference_identifies_brain":False,
            "brain_and_motion_separately_fully_recovered":False,
            "finite_rank_checks":exhaustive,
            "status":"SYNTHETIC_EXACT_LINEAR_ONLY"}


def motion_lock_negative_control():
    fs, n, hz = 32, 128, 2
    brain=[sin(2*pi*hz*t/fs) for t in range(n)]
    neural_only=brain
    motion_only=brain
    assert all(isclose(a,b,abs_tol=1e-12) for a,b in zip(neural_only,motion_only))
    freq_bin=hz*n//fs
    assert hz*n%fs == 0 and freq_bin == 8
    assert freq_bin < 4*n/fs
    # A correlation fit on condition-confounded training perfectly predicts
    # the selected train data yet fails under motion reversal at test.
    treatment=[1,-1,1,-1]
    train_motion=treatment
    train_y=[u+m for u,m in zip(treatment,train_motion)]
    train_pred=[y/2 for y in train_y]
    assert train_pred == treatment
    test_motion=[-u for u in treatment]
    test_y=[u+m for u,m in zip(treatment,test_motion)]
    test_pred=[y/2 for y in test_y]
    assert test_pred == [0]*4 and test_pred != treatment
    reference=[m for m in test_motion]
    correctly_recovered=[y-r for y,r in zip(test_y,reference)]
    assert correctly_recovered == treatment
    return {"synthetic_frequency_hz":2,
            "within_delta_0p5_4Hz":True,
            "overlaps_reported_motion_artifact_band_up_to_3Hz":True,
            "highpass_4Hz_removes_2Hz_source":True,
            "source_vs_artifact_single_stream_indistinguishable":True,
            "confounded_train_fit_accuracy":1.0,
            "motion_reversed_test_fit_accuracy":0.0,
            "clean_reference_recovers_test_source":True,
            "status":"SYNTHETIC_NEGATIVE_CONTROL"}


def common_stimulus_negative_control():
    movie=[1,-1,0,1,0,-1,1,-1]
    two_receivers=[list(movie),list(movie)]
    assert two_receivers[0] == two_receivers[1]
    shifted=movie[1:]+movie[:1]
    assert shifted != movie
    return {"independent_receivers_share_external_stimulus":True,
            "their_traces_are_perfectly_matched":True,
            "direct_receiver_to_receiver_coupling_in_model":False,
            "shifted_stimulus_breaks_exact_match":True,
            "status":"SYNTHETIC_COMMON_CAUSE_ONLY"}


REQUIRED_RECEIPTS = (
    "source_dataset_identifier", "source_author", "source_revision_or_doi",
    "raw_data_sha256", "subject_session_and_trial_ids", "recording_modality",
    "sensor_positions_and_orientations", "sampling_hz", "source_and_reference_timestamps",
    "measured_delta_0p5_4Hz_noise_spectrum", "motion_channels_or_pose_trace",
    "heldout_split_manifest_sha256", "control_and_blind_manifest_sha256",
    "independent_unit_of_analysis", "analysis_plan_frozen_before_outcome",
)


def validate_receipt(candidate):
    missing=[k for k in REQUIRED_RECEIPTS if not candidate.get(k)]
    errors=[]
    for name in ("raw_data_sha256", "heldout_split_manifest_sha256",
                 "control_and_blind_manifest_sha256"):
        val=candidate.get(name)
        if val is not None and not re.fullmatch(r"[0-9a-fA-F]{64}", str(val)):
            errors.append(name + " must be 64 hexadecimal characters")
    if any(str(v).strip().lower() in ("dummy", "placeholder", "synthetic-placeholder")
           for v in candidate.values()):
        errors.append("placeholder values cannot be promoted as experimental receipts")
    try:
        f=float(candidate.get("sampling_hz",0))
        if isinstance(candidate.get("sampling_hz"), bool) or not isfinite(f) or f <= 8.0:
            errors.append("sampling_hz must be finite and exceed twice 4 Hz")
    except (TypeError,ValueError):
        errors.append("sampling_hz must be numeric")
    modality=candidate.get("recording_modality")
    if modality not in ("human-EEG+OPM-MEG","human-OPM-MEG","human-EEG+SQUID-MEG"):
        errors.append("wrong modality for intended human neural magnetometry")
    if candidate.get("measured_delta_0p5_4Hz_noise_spectrum") in ("40-Hz-SNR", "cardiac-NV-MCG"):
        errors.append("not a measured delta-band sensor noise spectrum")
    return {"admissible_for_experimental_review":not missing and not errors,
            "missing_receipts":missing, "hard_errors":errors,
            "note":"Receipt validation does not establish causal or exotic field efficacy"}


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--receipt-json",type=Path)
    args=p.parse_args()
    out={"scope":"synthetic exact signal/artefact discriminator only",
         "source_observability":source_vs_artifact(),
         "delta_motion":motion_lock_negative_control(),
         "common_stimulus":common_stimulus_negative_control(),
         "empty_experimental_receipt":validate_receipt({})}
    assert not out["empty_experimental_receipt"]["admissible_for_experimental_review"]
    if args.receipt_json:
        out["provided_experimental_receipt"]=validate_receipt(json.loads(args.receipt_json.read_text()))
    print(json.dumps(out,indent=2,sort_keys=True))


if __name__=="__main__":main()
