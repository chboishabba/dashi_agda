"""Ingest deposited Co1/4TaSe2 Igor binary-wave files without inventing data.

Requires the user/researcher to obtain the public UCF STARS dataset payload.
This execution environment received HTTP 403 from the native download endpoint
on 2026-10-08, so no raw file is bundled in the repository.

The script hashes every .ibw file and extracts array/scaling metadata using
igor2.  It deliberately does not guess which wave is spin-up/down or how photon
energy maps to kz; those mappings require dataset metadata or an explicit
calibration manifest.
"""
import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

DATASET_URL = "https://stars.library.ucf.edu/datasets/30/"
SOURCE_DOI = "10.1038/s41467-026-76784-x"


def _sha256(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def load_wave(path):
    try:
        from igor2 import binarywave
    except ImportError as exc:
        raise RuntimeError("igor2 is required: pip install igor2") from exc
    obj = binarywave.load(str(path))
    wave = obj["wave"]
    data = np.asarray(wave["wData"])
    header = wave.get("wave_header", {})
    sf_a = np.asarray(header.get("sfA", []), dtype=float).tolist()
    sf_b = np.asarray(header.get("sfB", []), dtype=float).tolist()
    return {
        "shape": list(data.shape),
        "dtype": str(data.dtype),
        "finite_fraction": float(np.isfinite(data).mean()) if data.size else 1.0,
        "scale_delta": sf_a,
        "scale_origin": sf_b,
    }


def ingest(root):
    root = Path(root)
    files = sorted(root.rglob("*.ibw"))
    if not files:
        raise FileNotFoundError("no .ibw files found; raw UCF payload is required")
    entries = []
    for path in files:
        info = load_wave(path)
        entries.append({
            "relative_path": str(path.relative_to(root)),
            "sha256": _sha256(path),
            **info,
        })
    return {
        "source_doi": SOURCE_DOI,
        "dataset_url": DATASET_URL,
        "wave_count": len(entries),
        "waves": entries,
        "spin_channel_assignment_present": False,
        "photon_energy_to_kz_calibration_present": False,
        "spectral_observer_ready": False,
        "epistemic_boundary": "raw waves hashed and decoded only; channel semantics/calibration remain explicit obligations",
    }


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("dataset_directory")
    p.add_argument("--manifest")
    a = p.parse_args()
    result = ingest(a.dataset_directory)
    text = json.dumps(result, indent=2) + "\n"
    if a.manifest:
        Path(a.manifest).write_text(text)
    print(text, end="")
