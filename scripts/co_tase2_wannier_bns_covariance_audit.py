"""Audit a literal Wannier Hamiltonian against BNS 194.268 in the SAME basis.

Inputs:
  * Wannier90 `*_hr.dat` electronic Hamiltonian.
  * literal BNS authority JSON already stored in this repo.
  * NPZ samples containing SAME-BASIS sewing matrices supplied by the electronic
    structure/symmetry producer.

Required NPZ fields:
  operation_triplet            shape (Nsamples,), strings matching authority
  antiunitary                  shape (Nsamples,), bool
  k_fractional                 shape (Nsamples,3)
  transformed_k_fractional     shape (Nsamples,3)
  sewing                       shape (Nsamples,Nw,Nw), complex
  source_identity              scalar non-empty string

For each sample it checks
  U_g(k) [H(k)^* if antiunitary else H(k)] U_g(k)^† = H(gk)
and U_g(k)^† U_g(k) = I.

Every one of the 24 literal authority operations must appear at least once with
matching antiunitary parity. This consumer deliberately does NOT manufacture
sewing matrices from orbital labels or atomic positions: such a representation
must come from the same Wannier calculation/symmetry analysis. A passing result
therefore pays the material-basis covariance CHECK, not the producer itself.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

from co_tase2_wannier90_spectral import _load_hr, h_of_k


def _text_scalar(x):
    a = np.asarray(x)
    if a.size != 1:
        raise ValueError("source_identity must be scalar")
    v = a.reshape(()).item()
    if isinstance(v, bytes):
        v = v.decode()
    v = str(v).strip()
    if not v:
        raise ValueError("source_identity must be non-empty")
    return v


def _load_authority(path: Path):
    d = json.loads(path.read_text())
    ops = d.get("operations")
    if not isinstance(ops, list) or len(ops) != 24:
        raise ValueError("literal BNS authority must contain exactly 24 operations")
    mapping = {}
    for op in ops:
        key = str(op["triplet"])
        if key in mapping:
            raise ValueError("duplicate authority operation triplet")
        mapping[key] = bool(op["antiunitary"])
    return d, mapping


def audit(hr_path, authority_path, samples_path, tolerance=1e-7):
    hr_path = Path(hr_path)
    authority_path = Path(authority_path)
    samples_path = Path(samples_path)
    num_wann, rvec, hblocks, degeneracy = _load_hr(hr_path)
    authority, op_map = _load_authority(authority_path)

    with np.load(samples_path, allow_pickle=False) as d:
        required = {
            "operation_triplet", "antiunitary", "k_fractional",
            "transformed_k_fractional", "sewing", "source_identity",
        }
        missing = required - set(d.files)
        if missing:
            raise ValueError(f"symmetry sample artifact missing {sorted(missing)}")
        triplet = np.asarray(d["operation_triplet"])
        anti = np.asarray(d["antiunitary"], bool)
        k = np.asarray(d["k_fractional"], float)
        gk = np.asarray(d["transformed_k_fractional"], float)
        sewing = np.asarray(d["sewing"], complex)
        source_identity = _text_scalar(d["source_identity"])

    n = len(triplet)
    if anti.shape != (n,) or k.shape != (n, 3) or gk.shape != (n, 3):
        raise ValueError("operation/parity/k-point sample shapes are inconsistent")
    if sewing.shape != (n, num_wann, num_wann):
        raise ValueError("sewing must have shape (Nsamples,num_wann,num_wann)")
    if n < 24:
        raise ValueError("at least one sample per literal BNS operation is required")
    if not (np.isfinite(k).all() and np.isfinite(gk).all() and
            np.isfinite(sewing.real).all() and np.isfinite(sewing.imag).all()):
        raise ValueError("non-finite symmetry sample values")

    covered = set()
    max_unitarity = 0.0
    max_covariance = 0.0
    identity = np.eye(num_wann)
    for i in range(n):
        name = str(triplet[i])
        if name not in op_map:
            raise ValueError(f"sample operation not in literal BNS authority: {name}")
        if bool(anti[i]) != op_map[name]:
            raise ValueError(f"antiunitary parity mismatch for {name}")
        u = sewing[i]
        unitary_defect = float(np.max(np.abs(u.conj().T @ u - identity)))
        max_unitarity = max(max_unitarity, unitary_defect)
        if unitary_defect > tolerance:
            raise ValueError(f"non-unitary sewing matrix for {name}: {unitary_defect:g}")

        hk = h_of_k(k[i], rvec, hblocks, degeneracy)
        hgk = h_of_k(gk[i], rvec, hblocks, degeneracy)
        source_h = hk.conj() if bool(anti[i]) else hk
        transformed = u @ source_h @ u.conj().T
        covariance_defect = float(np.max(np.abs(transformed - hgk)))
        max_covariance = max(max_covariance, covariance_defect)
        if covariance_defect > tolerance:
            raise ValueError(
                f"Wannier-basis covariance failure for {name}: {covariance_defect:g}"
            )
        covered.add(name)

    missing_ops = sorted(set(op_map) - covered)
    if missing_ops:
        raise ValueError(f"literal BNS operations lack Wannier-basis samples: {missing_ops}")

    return {
        "authority": authority.get("authority", ""),
        "bns_number": authority.get("bns_number", ""),
        "source_identity": source_identity,
        "num_wann": num_wann,
        "authority_operations": len(op_map),
        "covered_operations": len(covered),
        "samples": n,
        "max_unitarity_defect": max_unitarity,
        "max_covariance_defect": max_covariance,
        "tolerance": tolerance,
        "epistemic_boundary": (
            "passing receipt verifies covariance of the supplied same-basis Wannier/sewing artifacts; "
            "it does not prove the artifacts were generated from the experimental material unless their provenance does"
        ),
    }


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("wannier90_hr_dat")
    p.add_argument("literal_bns_json")
    p.add_argument("sewing_samples_npz")
    p.add_argument("--tolerance", type=float, default=1e-7)
    p.add_argument("--receipt")
    a = p.parse_args()
    result = audit(a.wannier90_hr_dat, a.literal_bns_json, a.sewing_samples_npz, a.tolerance)
    if a.receipt:
        Path(a.receipt).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
