#!/usr/bin/env python3
"""Read-only EEGLAB .set epoch-arm identity and .fdt geometry source preflight.

Source: Niedernhuber et al. (2026), doi:10.1177/02698811261481062.
Original 2026 analysis uses getconds on DMT, harmine and placebo from
disemb_mc_mkcoh.m; .set events encode those source labels, NOT a complete
replay of getconds or +microstate G1. The string 'DMT' is an original arm
label, not evidence of DMT-alone rather than the original DMT/harmine
protocol. Requires scipy for MATLAB .set structure but NEVER decodes
physiological .fdt sample values; validates only declared byte extent.
"""
from __future__ import annotations
import argparse
import json
from collections import Counter
from pathlib import Path
from scipy.io import loadmat

ARMS = ("DMT", "harmine", "placebo")


def _epoch_event_types(epoch):
    e = epoch.eventtype
    if isinstance(e, str):
        return [e]
    return [str(a) for a in e]


def metadata_audit(set_file, fdt_file=None):
    set_file = Path(set_file)
    if not set_file.is_file():
        raise ValueError("Missing source EEGLAB .set")
    meta = loadmat(set_file, squeeze_me=True, struct_as_record=False)
    eeg = meta.get("EEG")
    if eeg is None:
        raise ValueError("Source .set missing EEG struct")
    title = str(eeg.setname)
    prefix = title.split("_equalised.set")[0]
    if (not prefix.isdecimal() or len(prefix) != 4
            or title != prefix + "_equalised.set"
            or str(eeg.data) != prefix + "_equalised.fdt"):
        raise ValueError("Source .set/.fdt name linkage fails")
    channels = int(eeg.nbchan)
    points = int(eeg.pnts)
    trials = int(eeg.trials)
    rate = float(eeg.srate)
    if channels <= 0 or points <= 0 or trials <= 0 or rate <= 0:
        raise ValueError("Invalid original epoch dimensions")
    epochs = eeg.epoch
    if len(epochs) != trials:
        raise ValueError("Epoch table does not span declared trials")
    counts = Counter()
    arm_only_boundary_markers = Counter()
    visit_label = {}
    for epoch in epochs:
        events = _epoch_event_types(epoch)
        tagged = set()
        for name in events:
            for arm in ARMS:
                if name.endswith("_" + arm):
                    tagged.add(arm)
        if len(tagged) != 1:
            raise ValueError("Ambiguous or missing original epoch treatment identity")
        arm = tagged.pop()
        visits = set()
        for name in events:
            if name.endswith("_" + arm):
                head = name.split(" _ condition")[0]
                parts = head.split("_")
                if len(parts) == 2 and parts[0] == prefix and parts[1].isdigit():
                    visits.add(int(parts[1]))
        if len(visits) != 1:
            if not visits and all(name == "X_" + arm for name in events):
                arm_only_boundary_markers[arm] += 1
                continue
            raise ValueError("Original visit marker is not unique")
        visit = visits.pop()
        if arm in visit_label and visit_label[arm] != visit:
            raise ValueError("One arm labels multiple session indices")
        visit_label[arm] = visit
        counts[arm] += 1
    if any(counts[arm] == 0 for arm in ARMS) or len(set(visit_label.values())) != 3:
        raise ValueError("Source 3-arm visit construction absent")
    required_fdt_bytes = channels * points * trials * 4
    verified_fdt_extent = False
    if fdt_file is not None:
        fdt_file = Path(fdt_file)
        if fdt_file.name.removesuffix(".bin") != str(eeg.data):
            raise ValueError("Not the associated EEGLAB sample payload")
        if (not fdt_file.is_file() or fdt_file.is_symlink()
                or fdt_file.stat().st_size != required_fdt_bytes):
            raise ValueError("Original .fdt extent differs from 32-bit samples")
        verified_fdt_extent = True
    return {
        "schema": "dashi-dmt-niedernhuber-original-epoch-metadata-v1",
        "pseudonym_file_prefix": prefix,
        "nbchan": channels, "pnts_per_epoch": points,
        "trials": trials, "sample_rate_hz": rate,
        "original_arm_epoch_counts": {arm: counts[arm] for arm in ARMS},
        "original_arm_visit_indices": {arm: visit_label[arm] for arm in ARMS},
        "source_X_arm_only_boundary_marker_epochs": {
            arm: arm_only_boundary_markers[arm] for arm in ARMS},
        "individual_X_epoch_visit_identity_verified": False,
        "required_fdt_bytes": required_fdt_bytes,
        "fdt_extent_matched": verified_fdt_extent,
        "original_three_arm_metadata_located": True,
        "actual_getconds_replayed": False,
        "original_microstate_G1_computed": False,
        "real_eeg_samples_interpreted": False,
        "agent_ontology_inferred": False,
    }


def main():
    a = argparse.ArgumentParser(description=__doc__)
    a.add_argument("--set", type=Path, required=True)
    a.add_argument("--fdt", type=Path)
    args = a.parse_args()
    print(json.dumps(metadata_audit(args.set, args.fdt), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
