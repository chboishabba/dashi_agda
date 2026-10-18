"""Strict fit on *independently calibrated* spin-ARPES peak splitting CSV.
NOT an Igor binary-wave reader, not an automatic peak-finding inverse solver,
and never silently substitutes synthetic data for measured observations.
Required columns: kx,ky,kz (reciprocal units), delta_e_ev, sigma_e_ev,
source_file and photon_energy_ev.  Rows must be separately extracted from
the raw data deposited at https://stars.library.ucf.edu/datasets/30/.
"""
import csv
import json
import hashlib
import argparse
from pathlib import Path

import numpy as np
from scipy.optimize import least_squares
from co_tase2_bloch_symmetry import harmonic

COLUMNS = ("kx","ky","kz","delta_e_ev","sigma_e_ev","source_file","photon_energy_ev")

def fit(path):
    path = Path(path)
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle)
        if not set(COLUMNS).issubset(reader.fieldnames or []):
            raise ValueError(f"missing CSV columns: {set(COLUMNS)-set(reader.fieldnames or [])}")
        rows = list(reader)
    if len(rows) < 8:
        raise ValueError("at least 8 independent measured observations required")
    k = np.array([[float(r[c]) for c in ("kx","ky","kz")] for r in rows])
    y = np.array([float(r["delta_e_ev"]) for r in rows])
    sigma = np.array([float(r["sigma_e_ev"]) for r in rows])
    if not (np.isfinite(k).all() and np.isfinite(y).all() and
            np.isfinite(sigma).all() and (sigma > 0).all()):
        raise ValueError("invalid coordinates, splits, or uncertainties")
    for r in rows:
        if not r["source_file"].strip():
            raise ValueError("missing raw-file reference on an observation")
        if not np.isfinite(float(r["photon_energy_ev"])):
            raise ValueError("invalid photon energy")
    f = np.array([harmonic(row, character=True) for row in k])
    if np.max(np.abs(f)) < 1e-10:
        raise ValueError("the projected harmonic is zero over all input points")
    order = np.random.default_rng(194).permutation(len(y))
    cut = max(2, int(.75*len(y)))
    train, test = order[:cut], order[cut:]
    result = least_squares(
        lambda p: (2*p[0]*f[train]-y[train])/sigma[train], x0=[.1])
    parameter = float(result.x[0])
    residual = (2*parameter*f-y)/sigma
    return dict(
        input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        source_doi="10.1038/s41467-026-76784-x",
        observations=len(y),
        holdout_observations=len(test),
        coupling_ev=parameter,
        train_weighted_rmse=float(np.sqrt(np.mean(residual[train]**2))),
        holdout_weighted_rmse=float(np.sqrt(np.mean(residual[test]**2))),
        source_files=sorted({r["source_file"] for r in rows}),
        epistemic_boundary="conditional fit to extracted peaks only; NOT fitted raw Igor ARPES")
if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("calibrated_peaks_csv")
    parser.add_argument("--receipt")
    args=parser.parse_args()
    answer=fit(args.calibrated_peaks_csv)
    if args.receipt:
        Path(args.receipt).write_text(json.dumps(answer,indent=2)+"\n")
    print(json.dumps(answer,indent=2))
