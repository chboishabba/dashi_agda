"""Wannier90 hr.dat -> spin-projected spectral artifact for Co1/4TaSe2.

This is a strict PRODUCER FORMAT ADAPTER, not a material calculation. It consumes
an independently generated Wannier90 real-space Hamiltonian plus explicit
metadata and a k-path, then emits the `material_spectral.npz` schema consumed by
`co_tase2_arpes_forward_fit.py`.

Required metadata JSON fields:
  soc_included: true
  exchange_included: true
  spin_basis_model: non-empty string
  spin_projectors: shape (Ns, num_wann), diagonal projector weights in [0,1]
  reciprocal_cartesian_inv_a: 3x3 matrix; fractional k @ matrix -> 1/Angstrom
  fermi_energy_ev: number
  temperature_k: positive number
  broadening_ev: positive Lorentzian half-width
  matrix_element_model: non-empty string
  kz_broadening_model: non-empty string
  source_identity: non-empty string

Required k-path JSON field:
  k_fractional: list of >=2 [k1,k2,k3] reciprocal fractional coordinates.

Wannier90 `*_hr.dat` convention:
  line 1 comment; line 2 num_wann; line 3 nrpts; ceil(nrpts/15) degeneracy
  integers; then nrpts*num_wann^2 records
      R1 R2 R3 m n Re(H_mn(R)) Im(H_mn(R)).
The interpolant uses the standard degeneracy divisor:
  H(k) = sum_R H(R) exp(2*pi*i*k.R) / ndegen(R).

For each declared diagonal projector P_s, the spectral channel is
  A_s(k,w) = sum_n <u_n|P_s|u_n> * eta/pi / ((w-(E_n-EF))^2+eta^2).
This permits spinor-Wannier bases when the producer explicitly supplies the
spin-projection weights. It does not infer orbital labels, spin axes, SOC,
exchange, matrix elements, or kz broadening from the file name.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np


def _sha256_bytes(*chunks: bytes) -> str:
    h = hashlib.sha256()
    for chunk in chunks:
        h.update(chunk)
    return h.hexdigest()


def _require_text(d, key):
    value = str(d.get(key, "")).strip()
    if not value:
        raise ValueError(f"metadata {key} must be explicitly declared")
    return value


def _load_hr(path: Path):
    lines = path.read_text().splitlines()
    if len(lines) < 4:
        raise ValueError("Wannier90 hr.dat is too short")
    try:
        num_wann = int(lines[1].strip())
        nrpts = int(lines[2].strip())
    except Exception as exc:
        raise ValueError("invalid num_wann/nrpts header") from exc
    if num_wann <= 0 or nrpts <= 0:
        raise ValueError("num_wann and nrpts must be positive")

    ndegen_count = math.ceil(nrpts / 15)
    deg_tokens = []
    for line in lines[3:3 + ndegen_count]:
        deg_tokens.extend(line.split())
    if len(deg_tokens) < nrpts:
        raise ValueError("incomplete Wannier90 degeneracy table")
    degeneracy = np.asarray([int(x) for x in deg_tokens[:nrpts]], int)
    if np.any(degeneracy <= 0):
        raise ValueError("Wannier90 degeneracies must be positive")

    body = lines[3 + ndegen_count:]
    expected = nrpts * num_wann * num_wann
    if len(body) != expected:
        raise ValueError(f"expected {expected} hr records, found {len(body)}")

    r_vectors = []
    h_blocks = []
    cursor = 0
    for ir in range(nrpts):
        block = np.zeros((num_wann, num_wann), complex)
        r_this = None
        seen = set()
        for _ in range(num_wann * num_wann):
            parts = body[cursor].split()
            cursor += 1
            if len(parts) != 7:
                raise ValueError("invalid Wannier90 hr record")
            r = tuple(int(parts[i]) for i in range(3))
            m, n = int(parts[3]), int(parts[4])
            if not (1 <= m <= num_wann and 1 <= n <= num_wann):
                raise ValueError("Wannier orbital index out of range")
            if r_this is None:
                r_this = r
            elif r != r_this:
                raise ValueError("R vector changed inside one Wannier90 block")
            key = (m, n)
            if key in seen:
                raise ValueError("duplicate orbital pair in Wannier90 block")
            seen.add(key)
            block[m - 1, n - 1] = float(parts[5]) + 1j * float(parts[6])
        if len(seen) != num_wann * num_wann:
            raise ValueError("incomplete Wannier orbital block")
        r_vectors.append(r_this)
        h_blocks.append(block)

    return (
        num_wann,
        np.asarray(r_vectors, int),
        np.asarray(h_blocks, complex),
        degeneracy,
    )


def h_of_k(k_frac, r_vectors, h_blocks, degeneracy):
    k = np.asarray(k_frac, float)
    phase = np.exp(2j * np.pi * (r_vectors @ k)) / degeneracy
    h = np.tensordot(phase, h_blocks, axes=(0, 0))
    # A physical Wannier Hamiltonian must interpolate Hermitian matrices. Fail
    # closed rather than silently symmetrizing a malformed/incomplete artifact.
    defect = float(np.max(np.abs(h - h.conj().T)))
    if defect > 1e-7:
        raise ValueError(f"non-Hermitian H(k), max defect={defect:g}")
    return h


def _validate_metadata(meta, num_wann):
    if meta.get("soc_included") is not True:
        raise ValueError("metadata must explicitly declare soc_included=true")
    if meta.get("exchange_included") is not True:
        raise ValueError("metadata must explicitly declare exchange_included=true")
    spin_basis_model = _require_text(meta, "spin_basis_model")
    matrix_element_model = _require_text(meta, "matrix_element_model")
    kz_broadening_model = _require_text(meta, "kz_broadening_model")
    source_identity = _require_text(meta, "source_identity")

    p = np.asarray(meta.get("spin_projectors"), float)
    if p.ndim != 2 or p.shape[1] != num_wann or p.shape[0] < 1:
        raise ValueError("spin_projectors must have shape (Ns,num_wann)")
    if not np.isfinite(p).all() or np.any(p < 0) or np.any(p > 1):
        raise ValueError("spin projector weights must be finite and in [0,1]")
    if np.any(np.sum(p, axis=0) > 1.0 + 1e-9):
        raise ValueError("declared diagonal projector weights exceed identity")

    reciprocal = np.asarray(meta.get("reciprocal_cartesian_inv_a"), float)
    if reciprocal.shape != (3, 3) or not np.isfinite(reciprocal).all():
        raise ValueError("reciprocal_cartesian_inv_a must be finite 3x3")
    if abs(np.linalg.det(reciprocal)) < 1e-12:
        raise ValueError("reciprocal lattice matrix is singular")

    fermi = float(meta.get("fermi_energy_ev"))
    temperature = float(meta.get("temperature_k"))
    eta = float(meta.get("broadening_ev"))
    if not (np.isfinite(fermi) and np.isfinite(temperature) and np.isfinite(eta)):
        raise ValueError("fermi/temperature/broadening must be finite")
    if temperature <= 0 or eta <= 0:
        raise ValueError("temperature and broadening must be positive")

    e_min = float(meta.get("energy_min_ev", -1.0))
    e_max = float(meta.get("energy_max_ev", 0.25))
    e_n = int(meta.get("energy_points", 801))
    if not (e_min < e_max and e_n >= 8):
        raise ValueError("invalid energy grid declaration")

    return {
        "spin_projectors": p,
        "reciprocal": reciprocal,
        "fermi": fermi,
        "temperature": temperature,
        "eta": eta,
        "energy": np.linspace(e_min, e_max, e_n),
        "spin_basis_model": spin_basis_model,
        "matrix_element_model": matrix_element_model,
        "kz_broadening_model": kz_broadening_model,
        "source_identity": source_identity,
    }


def _load_kpath(path: Path):
    d = json.loads(path.read_text())
    k = np.asarray(d.get("k_fractional"), float)
    if k.ndim != 2 or k.shape[1] != 3 or k.shape[0] < 2:
        raise ValueError("k_fractional must have shape (Nk,3), Nk>=2")
    if not np.isfinite(k).all():
        raise ValueError("non-finite k path")
    return k


def _path_distance(k_frac, reciprocal):
    cart = k_frac @ reciprocal
    step = np.linalg.norm(np.diff(cart, axis=0), axis=1)
    return np.concatenate([[0.0], np.cumsum(step)])


def produce(hr_path, metadata_path, kpath_path, output_path, receipt_path=None):
    hr_path = Path(hr_path)
    metadata_path = Path(metadata_path)
    kpath_path = Path(kpath_path)
    output_path = Path(output_path)

    hr_bytes = hr_path.read_bytes()
    meta_bytes = metadata_path.read_bytes()
    kpath_bytes = kpath_path.read_bytes()
    metadata = json.loads(meta_bytes)
    num_wann, rv, hb, deg = _load_hr(hr_path)
    m = _validate_metadata(metadata, num_wann)
    k_frac = _load_kpath(kpath_path)
    momentum = _path_distance(k_frac, m["reciprocal"])
    energy = m["energy"]
    projectors = m["spin_projectors"]
    spectral = np.zeros((projectors.shape[0], k_frac.shape[0], energy.size), float)
    max_hermiticity_defect = 0.0

    for ik, k in enumerate(k_frac):
        h = h_of_k(k, rv, hb, deg)
        max_hermiticity_defect = max(
            max_hermiticity_defect,
            float(np.max(np.abs(h - h.conj().T))),
        )
        evals, evecs = np.linalg.eigh(h)
        evals = evals - m["fermi"]
        orbital_prob = np.abs(evecs) ** 2  # orbital x band
        channel_band_weight = projectors @ orbital_prob
        lorentz = (
            m["eta"] / np.pi
            / ((energy[None, :] - evals[:, None]) ** 2 + m["eta"] ** 2)
        )
        spectral[:, ik, :] = channel_band_weight @ lorentz

    artifact_digest = _sha256_bytes(hr_bytes, meta_bytes, kpath_bytes)
    np.savez_compressed(
        output_path,
        energy_ev=energy,
        momentum_inv_a=momentum,
        spectral=spectral,
        temperature_k=np.asarray(m["temperature"]),
        source_sha256=np.asarray(artifact_digest),
        soc_included=np.asarray(True),
        exchange_included=np.asarray(True),
        matrix_element_model=np.asarray(m["matrix_element_model"]),
        kz_broadening_model=np.asarray(m["kz_broadening_model"]),
    )

    receipt = {
        "producer": "wannier90_hr.dat -> spin-projected Lorentzian spectral function",
        "source_identity": m["source_identity"],
        "hr_sha256": hashlib.sha256(hr_bytes).hexdigest(),
        "metadata_sha256": hashlib.sha256(meta_bytes).hexdigest(),
        "kpath_sha256": hashlib.sha256(kpath_bytes).hexdigest(),
        "combined_source_sha256": artifact_digest,
        "num_wann": num_wann,
        "nrpts": int(len(rv)),
        "spin_channels": int(projectors.shape[0]),
        "k_points": int(k_frac.shape[0]),
        "energy_points": int(energy.size),
        "temperature_k": m["temperature"],
        "broadening_ev": m["eta"],
        "spin_basis_model": m["spin_basis_model"],
        "matrix_element_model": m["matrix_element_model"],
        "kz_broadening_model": m["kz_broadening_model"],
        "max_hermiticity_defect": max_hermiticity_defect,
        "output_npz": str(output_path),
        "epistemic_boundary": (
            "this adapter can consume a literal SOC+exchange Wannier artifact; "
            "it does not create or validate the underlying DFT/Wannier calculation"
        ),
    }
    if receipt_path:
        Path(receipt_path).write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("wannier90_hr_dat")
    p.add_argument("metadata_json")
    p.add_argument("kpath_json")
    p.add_argument("output_npz")
    p.add_argument("--receipt")
    a = p.parse_args()
    print(json.dumps(produce(
        a.wannier90_hr_dat,
        a.metadata_json,
        a.kpath_json,
        a.output_npz,
        a.receipt,
    ), indent=2))
