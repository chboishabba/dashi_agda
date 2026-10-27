"""Explicit-manifest Igor-wave -> calibrated ARPES observer builder.

This is the missing raw-bytes -> `calibrated_arpes.npz` adapter for the Co lane.
It NEVER guesses channel semantics, dimension roles, physical axis conversions,
uncertainty model, or polarimeter treatment.

Manifest JSON schema (top-level):
  photon_energy_ev: number
  temperature_k: number
  spin_channels_calibrated: true
  polarimeter_response_model: non-empty string
  waves: list of channel objects

Each channel object requires:
  path: relative/absolute .ibw path
  spin_label: non-empty string
  energy_axis: integer dimension index
  momentum_axis: integer dimension index, distinct from energy_axis
  energy_scale_to_ev: number multiplied into Igor axis coordinate
  energy_offset_ev: additive correction after scaling
  momentum_scale_to_inv_a: number multiplied into Igor axis coordinate
  momentum_offset_inv_a: additive correction after scaling
  uncertainty_model: "poisson_sqrt_counts" or "constant"
If constant:
  sigma_intensity_constant: positive number
Optional:
  reverse_energy: bool
  reverse_momentum: bool

Igor dimension coordinates are reconstructed as sfB[axis] + i*sfA[axis].
All non-selected dimensions must be singleton after squeeze; each wave must reduce
to a 2D momentum-energy plane. Every channel must land on exactly the same axes.

The resulting NPZ matches `co_tase2_arpes_forward_fit.py`:
  energy_ev, momentum_inv_a, intensity[Ns,Nk,Ne], sigma_intensity,
  source_sha256, photon_energy_ev, temperature_k, spin_channels_calibrated,
  polarimeter_response_model.

A successful conversion proves only that the supplied manifest calibrates the
supplied bytes consistently. Same-object scientific validity remains provenance-
dependent and requires the actual UCF dataset plus defensible calibration values.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _combined_digest(digests):
    h = hashlib.sha256()
    for d in digests:
        if len(d) != 64:
            raise ValueError("source digest must be SHA256 hex")
        h.update(d.encode("ascii"))
    return h.hexdigest()


def _load_ibw(path: Path):
    try:
        from igor2 import binarywave
    except ImportError as exc:
        raise RuntimeError("igor2 is required: pip install igor2") from exc
    obj = binarywave.load(str(path))
    wave = obj["wave"]
    data = np.asarray(wave["wData"], float)
    header = wave.get("wave_header", {})
    sf_a = np.asarray(header.get("sfA", []), dtype=float)
    sf_b = np.asarray(header.get("sfB", []), dtype=float)
    return data, sf_a, sf_b


def _axis(sf_a, sf_b, axis, size):
    if axis < 0 or axis >= len(sf_a) or axis >= len(sf_b):
        raise ValueError(f"Igor scaling metadata missing for axis {axis}")
    if not (np.isfinite(sf_a[axis]) and np.isfinite(sf_b[axis])):
        raise ValueError("non-finite Igor axis scaling")
    return sf_b[axis] + np.arange(size, dtype=float) * sf_a[axis]


def _orient_plane(data, energy_axis, momentum_axis):
    if energy_axis == momentum_axis:
        raise ValueError("energy_axis and momentum_axis must differ")
    if energy_axis < 0 or momentum_axis < 0 or energy_axis >= data.ndim or momentum_axis >= data.ndim:
        raise ValueError("declared axis index outside wave rank")
    other = [i for i in range(data.ndim) if i not in (momentum_axis, energy_axis)]
    if any(data.shape[i] != 1 for i in other):
        raise ValueError("all non energy/momentum dimensions must be singleton")
    perm = [momentum_axis, energy_axis] + other
    plane = np.transpose(data, perm)
    if other:
        plane = plane.reshape(data.shape[momentum_axis], data.shape[energy_axis])
    if plane.ndim != 2:
        raise ValueError("wave did not reduce to a 2D momentum-energy plane")
    return plane


def _strictly_increasing_axis(axis, plane, which):
    if np.all(np.diff(axis) > 0):
        return axis, plane
    if np.all(np.diff(axis) < 0):
        if which == "momentum":
            return axis[::-1], plane[::-1, :]
        return axis[::-1], plane[:, ::-1]
    raise ValueError(f"{which} axis must be strictly monotonic")


def assemble_observer(*, arrays, energy_axes, momentum_axes, sigmas,
                      source_digests, photon_energy_ev, temperature_k,
                      polarimeter_response_model, spin_channels_calibrated):
    if not spin_channels_calibrated:
        raise ValueError("spin channels must be explicitly calibrated")
    polarimeter = str(polarimeter_response_model).strip()
    if not polarimeter:
        raise ValueError("polarimeter_response_model must be declared")
    if not np.isfinite(photon_energy_ev) or not np.isfinite(temperature_k) or temperature_k <= 0:
        raise ValueError("invalid photon energy or temperature")
    n = len(arrays)
    if n < 1 or not all(len(x) == n for x in (energy_axes, momentum_axes, sigmas, source_digests)):
        raise ValueError("channel collections must have equal nonzero length")

    ref_e = np.asarray(energy_axes[0], float)
    ref_k = np.asarray(momentum_axes[0], float)
    if ref_e.ndim != 1 or ref_k.ndim != 1 or not (np.all(np.diff(ref_e) > 0) and np.all(np.diff(ref_k) > 0)):
        raise ValueError("reference axes must be strictly increasing 1D arrays")

    intensity = []
    sigma_out = []
    for i in range(n):
        a = np.asarray(arrays[i], float)
        s = np.asarray(sigmas[i], float)
        e = np.asarray(energy_axes[i], float)
        k = np.asarray(momentum_axes[i], float)
        if a.shape != (ref_k.size, ref_e.size) or s.shape != a.shape:
            raise ValueError("channel array/sigma shapes do not match reference axes")
        if not (np.allclose(e, ref_e, rtol=0, atol=1e-10) and np.allclose(k, ref_k, rtol=0, atol=1e-10)):
            raise ValueError("all calibrated channels must share identical physical axes")
        if not (np.isfinite(a).all() and np.isfinite(s).all() and np.all(s > 0)):
            raise ValueError("non-finite intensity or non-positive uncertainty")
        intensity.append(a)
        sigma_out.append(s)

    return {
        "energy_ev": ref_e,
        "momentum_inv_a": ref_k,
        "intensity": np.asarray(intensity, float),
        "sigma_intensity": np.asarray(sigma_out, float),
        "source_sha256": _combined_digest(source_digests),
        "photon_energy_ev": float(photon_energy_ev),
        "temperature_k": float(temperature_k),
        "spin_channels_calibrated": True,
        "polarimeter_response_model": polarimeter,
    }


def build(manifest_path, output_path, receipt_path=None):
    manifest_path = Path(manifest_path)
    output_path = Path(output_path)
    m = json.loads(manifest_path.read_text())
    required = {
        "photon_energy_ev", "temperature_k", "spin_channels_calibrated",
        "polarimeter_response_model", "waves",
    }
    missing = required - set(m)
    if missing:
        raise ValueError(f"manifest missing fields: {sorted(missing)}")
    if m["spin_channels_calibrated"] is not True:
        raise ValueError("manifest must explicitly declare spin_channels_calibrated=true")
    waves = m["waves"]
    if not isinstance(waves, list) or not waves:
        raise ValueError("manifest waves must be a non-empty list")

    arrays, energies, momenta, sigmas, digests, labels = [], [], [], [], [], []
    base = manifest_path.parent
    for spec in waves:
        for key in (
            "path", "spin_label", "energy_axis", "momentum_axis",
            "energy_scale_to_ev", "energy_offset_ev",
            "momentum_scale_to_inv_a", "momentum_offset_inv_a",
            "uncertainty_model",
        ):
            if key not in spec:
                raise ValueError(f"wave spec missing {key}")
        label = str(spec["spin_label"]).strip()
        if not label:
            raise ValueError("spin_label must be non-empty")
        path = Path(spec["path"])
        if not path.is_absolute():
            path = base / path
        data, sf_a, sf_b = _load_ibw(path)
        eaxis_i = int(spec["energy_axis"])
        kaxis_i = int(spec["momentum_axis"])
        plane = _orient_plane(data, eaxis_i, kaxis_i)
        e = _axis(sf_a, sf_b, eaxis_i, data.shape[eaxis_i])
        k = _axis(sf_a, sf_b, kaxis_i, data.shape[kaxis_i])
        e = e * float(spec["energy_scale_to_ev"]) + float(spec["energy_offset_ev"])
        k = k * float(spec["momentum_scale_to_inv_a"]) + float(spec["momentum_offset_inv_a"])

        # Explicit reversal flags are allowed, but monotonic decreasing axes are
        # also canonicalized to increasing order. No other regridding occurs.
        if bool(spec.get("reverse_energy", False)):
            e, plane = e[::-1], plane[:, ::-1]
        if bool(spec.get("reverse_momentum", False)):
            k, plane = k[::-1], plane[::-1, :]
        k, plane = _strictly_increasing_axis(k, plane, "momentum")
        e, plane = _strictly_increasing_axis(e, plane, "energy")

        model = str(spec["uncertainty_model"])
        if model == "poisson_sqrt_counts":
            if np.any(plane < 0):
                raise ValueError("poisson_sqrt_counts requires non-negative intensity")
            sigma = np.sqrt(np.maximum(plane, 1.0))
        elif model == "constant":
            value = float(spec.get("sigma_intensity_constant", 0.0))
            if not np.isfinite(value) or value <= 0:
                raise ValueError("constant uncertainty requires positive sigma_intensity_constant")
            sigma = np.full_like(plane, value, dtype=float)
        else:
            raise ValueError(f"unsupported uncertainty_model: {model}")

        arrays.append(plane)
        energies.append(e)
        momenta.append(k)
        sigmas.append(sigma)
        digests.append(_sha256(path))
        labels.append(label)

    out = assemble_observer(
        arrays=arrays,
        energy_axes=energies,
        momentum_axes=momenta,
        sigmas=sigmas,
        source_digests=digests,
        photon_energy_ev=float(m["photon_energy_ev"]),
        temperature_k=float(m["temperature_k"]),
        polarimeter_response_model=m["polarimeter_response_model"],
        spin_channels_calibrated=True,
    )
    np.savez_compressed(output_path, **{k: np.asarray(v) for k, v in out.items()})

    receipt = {
        "manifest_sha256": hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
        "source_wave_sha256": digests,
        "spin_labels": labels,
        "spin_channels": len(labels),
        "shape": list(out["intensity"].shape),
        "photon_energy_ev": out["photon_energy_ev"],
        "temperature_k": out["temperature_k"],
        "polarimeter_response_model": out["polarimeter_response_model"],
        "output_npz": str(output_path),
        "epistemic_boundary": (
            "observer coordinates/channels/uncertainties are exactly those declared in the manifest; "
            "scientific validity depends on same-object raw-data and calibration provenance"
        ),
    }
    if receipt_path:
        Path(receipt_path).write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("calibration_manifest_json")
    p.add_argument("output_npz")
    p.add_argument("--receipt")
    a = p.parse_args()
    print(json.dumps(build(a.calibration_manifest_json, a.output_npz, a.receipt), indent=2))
