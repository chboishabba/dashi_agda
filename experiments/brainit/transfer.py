"""Build a no-leakage calibration budget curve from *actual* evaluated runs.

Input is a JSON array of entries:
  {"minutes":15,"evaluation":"...json","checkpoint_sha256":"..."}
Do not substitute the published T7 table or infer cross-subject replication.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from inventory import digest


def calibration_curve(entries: list[dict]) -> dict:
    if len(entries) < 2:
        raise ValueError("At least two real calibration-budget receipts required")
    seen = set()
    records = []
    anchor = None
    for entry in entries:
        minutes = entry["minutes"]
        if minutes <= 0 or minutes in seen:
            raise ValueError("Calibration minutes must be unique positive durations")
        seen.add(minutes)
        path = Path(entry["evaluation"])
        result = json.loads(path.read_text())
        if result.get("schema") != "brainit-reconstruction-evaluation-v1":
            raise ValueError("Unrecognized evaluator receipt")
        if result["condition"] != "paired":
            raise ValueError("Calibration comparisons require correctly paired fMRI")
        key = (result["subject"], result["seed"], result["branch"],
               result["metric_version"], result["artifact_hashes"]["images"],
               tuple(x["stimulus_id"] for x in result["rows"]))
        if anchor is not None and key != anchor:
            raise ValueError("Calibration runs use mismatched subjects, seeds or stimuli")
        anchor = key
        checkpoint_hash = entry.get("checkpoint_sha256", "")
        if len(checkpoint_hash) != 64 or not all(c in "0123456789abcdef"
                                               for c in checkpoint_hash):
            raise ValueError("Require measured lowercase sha256 of each checkpoint")
        records.append({
            "minutes": minutes, "checkpoint_sha256": checkpoint_hash,
            "evaluation_sha256": digest(path),
            "metrics": result["aggregate"],
        })
    return {
        "schema": "brainit-calibration-curve-v1",
        "records": sorted(records, key=lambda r: r["minutes"]),
        "same_test_stimuli_and_rng_required": True,
        "single_subject_only": anchor[0],
        "status": "within-declared-subject calibration report; not a population claim",
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--entries", type=Path, required=True,
                    help="JSON array: minutes, evaluation path, checkpoint sha256")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args(argv)
    r = calibration_curve(json.loads(args.entries.read_text()))
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(r, indent=2, sort_keys=True) + "\n")
    print(json.dumps(r["records"], indent=2))


if __name__ == "__main__":
    main()
