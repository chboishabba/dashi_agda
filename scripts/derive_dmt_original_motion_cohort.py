#!/usr/bin/env python3
"""Paper-specific fMRI motion-QC cohort *derivation*, not guessed identities.

Primary source: Timmermann et al., PNAS 2023, doi:10.1073/pnas.2218949120.
Original: 4/20 >20% of DMT 8-min post-bolus frames (FD>0.4 mm) excluded
for static fMRI; 3 more excluded for full 28-min dynamic fMRI; joint EEG-fMRI
uses separate EEG QC (n=12). This tool requires ACTUAL AUTHOR/SOURCE FD
vectors and bolus-TR alignment to derive IDs. It cannot infer FD from BOLD.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path

ORIGINAL_SOURCE = "doi:10.1073/pnas.2218949120"
TR_SECONDS = 2.0
FD_THRESHOLD_MM = 0.4
REJECT_FRACTION = 0.20
STATIC_START = 240
STATIC_END = 480
WHOLE_END = 840
# Exact primary StaticGFC.m source coordinates (Git blob
# f87d99f448848c3b0531fea0780ee241ebd77549).
# Source-file identity is not motion eligibility.
SOURCE_PSEUDONYMS = frozenset([
    "S01", "S02", "S03", "S06", "S07", "S08", "S09", "S10",
    "S11", "S12", "S13", "S14", "S15", "S16", "S17", "S18",
    "S19", "S22", "S23", "S25",
])


def excluded(fd, begin, end):
    if len(fd) < end:
        raise ValueError("Not enough source-aligned 2-second FD volumes")
    frame = fd[begin:end]
    if any(not isinstance(x, (int, float)) or isinstance(x, bool)
           or x < 0 or x != x or x == float("inf") for x in frame):
        raise ValueError("Nonfinite, negative or malformed FD volume")
    outliers = sum(float(x) > FD_THRESHOLD_MM for x in frame)
    # Paper uses 'more than 20%', so equality is retained.
    return {"scrubbed": outliers, "total": len(frame),
            "fraction": outliers / len(frame),
            "exclude": outliers / len(frame) > REJECT_FRACTION}


def derive_motion_cohorts(payload):
    if payload.get("source") != ORIGINAL_SOURCE:
        raise ValueError("FD record must identify the primary 2023 source")
    if not payload.get("author_or_processor_qc_receipt"):
        raise ValueError("Missing provenance and preprocessing reference for FD vectors")
    if payload.get("tr_seconds") != TR_SECONDS or payload.get("bolus_start_tr") != 240:
        raise ValueError("Source bolus/TR alignment not established")
    participants = payload.get("participants")
    if not isinstance(participants, dict) or set(participants) != SOURCE_PSEUDONYMS:
        raise ValueError("Must match exactly twenty author-listed pseudonymous IDs")
    static, dynamic = [], []
    audit = {}
    for subject in sorted(participants):
        row = participants[subject]
        if not isinstance(row, dict) or "dmt_fd" not in row:
            raise ValueError("Missing DMT FD for " + subject)
        fd = row["dmt_fd"]
        if not isinstance(fd, list) or len(fd) < WHOLE_END:
            raise ValueError("Missing 28-minute motion series: " + subject)
        short = excluded(fd, STATIC_START, STATIC_END)
        full = excluded(fd, 0, WHOLE_END)
        audit[subject] = {"post_dmt_8min": short, "full_28min": full}
        if not short["exclude"]:
            static.append(subject)
            if not full["exclude"]:
                dynamic.append(subject)
    if len(static) != 16 or len(dynamic) != 13:
        raise ValueError("Source QC did not reproduce primary original cohorts; "
                         "do NOT adjust threshold or invent IDs to force match. "
                         "static=%s dynamic=%s" % (len(static), len(dynamic)))
    return {
        "source": ORIGINAL_SOURCE,
        "qc_reference": payload["author_or_processor_qc_receipt"],
        "cohort_role": "original_primary_2023_motion_thresholds_only",
        "static_n16": static, "dynamic_n13": dynamic,
        "per_subject_qc": audit, "joint_eeg_fmri_n12_inferred": False,
        "readme_n15_substituted": False, "independent_source_verified": False,
        "human_fmri_statistic_recomputed": False
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fd-manifest", required=True, type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        value = derive_motion_cohorts(json.loads(args.fd_manifest.read_text()))
    except (ValueError, OSError, TypeError, KeyError) as error:
        print(json.dumps({"status": "blocked", "reason": str(error)}))
        return 2
    out = json.dumps(value, indent=2, sort_keys=True)
    if args.output:
        args.output.write_text(out + "\n")
    else:
        print(out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
