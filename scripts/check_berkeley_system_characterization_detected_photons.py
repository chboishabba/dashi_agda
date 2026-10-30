#!/usr/bin/env python3
"""Convert public PLD system-characterization TIFFs to estimated detected photons.

This uses Berkeley's source-executed displayed photon-transfer coefficients and
never promotes raw detected counts to exposure-normalized or incident throughput.
"""
from __future__ import annotations
import argparse, hashlib, io, json, statistics, zipfile
from pathlib import Path
import numpy as np
from PIL import Image

SOURCE_DRIVE_FOLDER = "1nr1pUrg80JQm8WyLa6wvFktmJ_pniOio"
RML_DRIVE_ID = "1mHJp99Twe0nSL3_HbNXjXjmV9zDy3YvI"
DIFFUSER_DRIVE_ID = "1-0rpd6gHgjdFshVMl6Gw1M0NqAliechM"
CALIBRATION = {
    "rml": {"slope": 0.02, "intercept": 1.46},
    "diffuser": {"slope": 0.03, "intercept": 0.36},
}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def read_system(path: Path, system: str) -> dict[str, dict]:
    p = CALIBRATION[system]
    out = {}
    with zipfile.ZipFile(path) as zf:
        for name in sorted(zf.namelist()):
            if not name.lower().endswith(".tiff") or "/._" in name:
                continue
            digital = np.asarray(Image.open(io.BytesIO(zf.read(name))), dtype=np.float64)
            photons = np.clip((digital - p["intercept"]) / p["slope"], 0, None)
            stem = Path(name).stem
            prefix = system + "_"
            position = stem[len(prefix):] if stem.startswith(prefix) else stem
            out[position] = {
                "shape": list(map(int, digital.shape)),
                "dn_mean": float(digital.mean()),
                "dn_max": int(digital.max()),
                "estimated_detected_photon_mean_per_pixel": float(photons.mean()),
                "estimated_detected_photon_sum": float(photons.sum()),
            }
    return out


def analyse(rml_zip: Path, diffuser_zip: Path) -> dict:
    rml, diffuser = read_system(rml_zip, "rml"), read_system(diffuser_zip, "diffuser")
    positions = sorted(set(rml) & set(diffuser))
    pairs, ratios = {}, []
    for pos in positions:
        r = rml[pos]["estimated_detected_photon_sum"]
        d = diffuser[pos]["estimated_detected_photon_sum"]
        ratio = r / d
        ratios.append(ratio)
        pairs[pos] = {
            "rml_estimated_detected_photons": r,
            "diffuser_estimated_detected_photons": d,
            "rml_to_diffuser_raw_detected_count_ratio": ratio,
        }
    return {
        "receipt_kind": "real_system_characterization_detected_photon_estimate",
        "source_drive_folder": SOURCE_DRIVE_FOLDER,
        "rml_archive": {"drive_id": RML_DRIVE_ID, "sha256": sha256_file(rml_zip)},
        "diffuser_archive": {"drive_id": DIFFUSER_DRIVE_ID, "sha256": sha256_file(diffuser_zip)},
        "calibration": {"rml": CALIBRATION["rml"], "diffuser": CALIBRATION["diffuser"],
                        "formula": "clip((digital - intercept) / slope, 0, infinity)",
                        "coefficients_are_source_display_rounded": True},
        "matched_positions": len(positions), "pairs": pairs,
        "ratio_summary": {"min": min(ratios), "median": statistics.median(ratios),
                          "mean": statistics.mean(ratios), "max": max(ratios)},
        "real_measured_tiffs_used": True, "detected_photon_estimate_paid": True,
        "characterization_exposure_metadata_recovered": False,
        "exposure_normalized_response_paid": False, "incident_throughput_paid": False,
        "matched_incident_photon_budget_paid": False,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rml-zip", type=Path, required=True)
    ap.add_argument("--diffuser-zip", type=Path, required=True)
    ap.add_argument("--json-out", type=Path)
    a = ap.parse_args()
    encoded = json.dumps(analyse(a.rml_zip, a.diffuser_zip), indent=2, sort_keys=True) + "\n"
    print(encoded, end="")
    if a.json_out: a.json_out.write_text(encoded, encoding="utf-8")


if __name__ == "__main__": main()
