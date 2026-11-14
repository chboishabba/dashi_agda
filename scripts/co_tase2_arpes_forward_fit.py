"""Fail-closed Co1/4TaSe2 spectral-function -> ARPES forward-fit consumer.

This module does NOT construct a material Hamiltonian or infer raw ARPES
calibration.  It consumes two independently prepared NPZ artifacts.

material_spectral.npz requires:
  energy_ev, momentum_inv_a, spectral[Ns,Nk,Ne], temperature_k,
  source_sha256, soc_included, exchange_included,
  matrix_element_model, kz_broadening_model.

calibrated_arpes.npz requires:
  energy_ev, momentum_inv_a, intensity[Ns,Nk,Ne], sigma_intensity,
  source_sha256, photon_energy_ev, temperature_k, spin_channels_calibrated,
  polarimeter_response_model.

Forward shape:
  A(k,w,s) * f_T(w) -> declared instrument/model treatment
                    -> Gaussian energy/momentum response
                    -> scale_s * signal + constant background_s.

Resolution widths are REQUIRED command-line inputs and explicitly interpreted
as Gaussian FWHM.  This is deliberate: Sprague et al. report 20 meV energy and
0.1 degree angular resolution, and separately an ~0.08 inverse-A instrumental
Gaussian MDC peak width.  The script must not silently identify the latter with
a momentum-resolution FWHM or convert angular resolution without the required
photoelectron geometry/kinetic-energy calibration.

Only per-channel non-negative scale and constant background are optimized on a
reproducible train/holdout split.  Matrix elements, kz broadening and
polarimeter response must be DECLARED; a caller may explicitly choose a named
identity/no-correction model, but omission is rejected.  This is a
consumer/validator, not evidence that the repository has paid the material-H
or raw-ARPES leaves.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.ndimage import gaussian_filter
from scipy.optimize import least_squares

KB_EV_PER_K = 8.617333262145e-5


def _scalar(d, key):
    x = np.asarray(d[key])
    if x.size != 1:
        raise ValueError(f"{key} must be scalar")
    return x.reshape(()).item()


def _text_scalar(d, key):
    x = _scalar(d, key)
    if isinstance(x, bytes):
        return x.decode()
    return str(x)


def _declared_text(d, key):
    value = _text_scalar(d, key).strip()
    if not value:
        raise ValueError(f"{key} must be explicitly declared")
    return value


def _valid_digest(value):
    return len(value) == 64 and all(c in "0123456789abcdefABCDEF" for c in value)


def _load_material(path: Path):
    with np.load(path, allow_pickle=False) as d:
        required = {
            "energy_ev", "momentum_inv_a", "spectral", "temperature_k",
            "source_sha256", "soc_included", "exchange_included",
            "matrix_element_model", "kz_broadening_model",
        }
        missing = required - set(d.files)
        if missing:
            raise ValueError(f"material spectral artifact missing {sorted(missing)}")
        e = np.asarray(d["energy_ev"], float)
        k = np.asarray(d["momentum_inv_a"], float)
        a = np.asarray(d["spectral"], float)
        t = float(_scalar(d, "temperature_k"))
        src = _text_scalar(d, "source_sha256")
        soc = bool(_scalar(d, "soc_included"))
        exch = bool(_scalar(d, "exchange_included"))
        matrix_model = _declared_text(d, "matrix_element_model")
        kz_model = _declared_text(d, "kz_broadening_model")
    if e.ndim != 1 or k.ndim != 1 or a.ndim != 3 or a.shape[1:] != (k.size, e.size):
        raise ValueError("material spectral coordinates/shapes inconsistent")
    if not (np.all(np.diff(e) > 0) and np.all(np.diff(k) > 0)):
        raise ValueError("material energy/momentum axes must be strictly increasing")
    if not np.isfinite(a).all() or np.any(a < 0) or t <= 0:
        raise ValueError("invalid material spectral values/temperature")
    if not (soc and exch):
        raise ValueError("material artifact must explicitly include SOC and exchange")
    if not _valid_digest(src):
        raise ValueError("material source_sha256 must be a hexadecimal SHA256 digest")
    return e, k, a, t, src, matrix_model, kz_model


def _load_observed(path: Path):
    with np.load(path, allow_pickle=False) as d:
        required = {
            "energy_ev", "momentum_inv_a", "intensity", "sigma_intensity",
            "source_sha256", "photon_energy_ev", "temperature_k",
            "spin_channels_calibrated", "polarimeter_response_model",
        }
        missing = required - set(d.files)
        if missing:
            raise ValueError(f"calibrated ARPES artifact missing {sorted(missing)}")
        e = np.asarray(d["energy_ev"], float)
        k = np.asarray(d["momentum_inv_a"], float)
        y = np.asarray(d["intensity"], float)
        s = np.asarray(d["sigma_intensity"], float)
        src = _text_scalar(d, "source_sha256")
        hv = float(_scalar(d, "photon_energy_ev"))
        t = float(_scalar(d, "temperature_k"))
        calibrated = bool(_scalar(d, "spin_channels_calibrated"))
        polarimeter_model = _declared_text(d, "polarimeter_response_model")
    if e.ndim != 1 or k.ndim != 1 or y.ndim != 3 or y.shape[1:] != (k.size, e.size):
        raise ValueError("ARPES coordinates/shapes inconsistent")
    if s.shape != y.shape:
        raise ValueError("sigma_intensity shape must equal intensity shape")
    if not (np.all(np.diff(e) > 0) and np.all(np.diff(k) > 0)):
        raise ValueError("ARPES energy/momentum axes must be strictly increasing")
    if not (np.isfinite(y).all() and np.isfinite(s).all() and np.all(s > 0)):
        raise ValueError("invalid ARPES intensities/uncertainties")
    if not calibrated:
        raise ValueError("spin channels must be explicitly calibrated")
    if not _valid_digest(src) or not np.isfinite(hv) or t <= 0:
        raise ValueError("invalid ARPES provenance/photon-energy/temperature")
    return e, k, y, s, hv, t, src, polarimeter_model


def _interp_spectral(e_src, k_src, a_src, e_dst, k_dst):
    tmp = np.empty((a_src.shape[0], k_src.size, e_dst.size), float)
    for c in range(a_src.shape[0]):
        for i in range(k_src.size):
            tmp[c, i] = np.interp(e_dst, e_src, a_src[c, i], left=0.0, right=0.0)
    out = np.empty((a_src.shape[0], k_dst.size, e_dst.size), float)
    for c in range(a_src.shape[0]):
        for j in range(e_dst.size):
            out[c, :, j] = np.interp(k_dst, k_src, tmp[c, :, j], left=0.0, right=0.0)
    return out


def forward_signal(e, k, spectral, temperature_k,
                   energy_resolution_mev_fwhm,
                   momentum_resolution_inv_a_fwhm):
    if energy_resolution_mev_fwhm <= 0 or momentum_resolution_inv_a_fwhm <= 0:
        raise ValueError("explicit Gaussian FWHM resolutions must be positive")
    fermi = 1.0 / (
        np.exp(np.clip(e / (KB_EV_PER_K * temperature_k), -100, 100)) + 1.0
    )
    signal = spectral * fermi[None, None, :]
    de = float(np.median(np.diff(e)))
    dk = float(np.median(np.diff(k)))
    sigma_e_pix = (energy_resolution_mev_fwhm / 1000.0) / (2.354820045 * de)
    sigma_k_pix = momentum_resolution_inv_a_fwhm / (2.354820045 * dk)
    return gaussian_filter(
        signal, sigma=(0.0, sigma_k_pix, sigma_e_pix), mode="nearest"
    )


def fit(material_path, observed_path, energy_resolution_mev_fwhm,
        momentum_resolution_inv_a_fwhm, seed=194268):
    material_path, observed_path = Path(material_path), Path(observed_path)
    em, km, a, tm, material_src, matrix_model, kz_model = _load_material(material_path)
    eo, ko, y, sigma, hv, to, arpes_src, polarimeter_model = _load_observed(observed_path)
    if a.shape[0] != y.shape[0]:
        raise ValueError("material and ARPES spin-channel counts differ")
    if abs(tm - to) > 2.0:
        raise ValueError("material and ARPES temperatures differ by >2 K")
    a_on_obs = _interp_spectral(em, km, a, eo, ko)
    pred0 = forward_signal(
        eo, ko, a_on_obs, to,
        energy_resolution_mev_fwhm,
        momentum_resolution_inv_a_fwhm,
    )

    nchan = y.shape[0]
    flat_n = y.size
    rng = np.random.default_rng(seed)
    order = rng.permutation(flat_n)
    cut = max(1, int(0.8 * flat_n))
    train, test = order[:cut], order[cut:]

    def model(p):
        scales = np.exp(p[:nchan])
        offsets = p[nchan:]
        return scales[:, None, None] * pred0 + offsets[:, None, None]

    def resid(p, idx):
        return (((model(p) - y) / sigma).ravel())[idx]

    x0 = np.concatenate([np.zeros(nchan), np.zeros(nchan)])
    opt = least_squares(lambda p: resid(p, train), x0)
    r = ((model(opt.x) - y) / sigma).ravel()
    scales = np.exp(opt.x[:nchan])
    offsets = opt.x[nchan:]

    def wrmse(idx):
        return float(np.sqrt(np.mean(r[idx] ** 2))) if len(idx) else None

    return {
        "material_file_sha256": hashlib.sha256(material_path.read_bytes()).hexdigest(),
        "material_source_sha256": material_src,
        "arpes_file_sha256": hashlib.sha256(observed_path.read_bytes()).hexdigest(),
        "arpes_source_sha256": arpes_src,
        "matrix_element_model": matrix_model,
        "kz_broadening_model": kz_model,
        "polarimeter_response_model": polarimeter_model,
        "photon_energy_ev": hv,
        "temperature_k": to,
        "energy_resolution_mev_fwhm": energy_resolution_mev_fwhm,
        "momentum_resolution_inv_a_fwhm": momentum_resolution_inv_a_fwhm,
        "spin_channels": nchan,
        "train_points": int(len(train)),
        "holdout_points": int(len(test)),
        "nuisance_scale": scales.tolist(),
        "nuisance_background": offsets.tolist(),
        "train_weighted_rmse": wrmse(train),
        "holdout_weighted_rmse": wrmse(test),
        "epistemic_boundary": (
            "consumer requires explicit material spectral + calibrated raw-ARPES artifacts "
            "and declared matrix-element/kz/polarimeter models; a successful fit is not "
            "equivalent to unique microscopic identification"
        ),
    }


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("material_spectral_npz")
    p.add_argument("calibrated_arpes_npz")
    p.add_argument("--energy-resolution-mev-fwhm", type=float, required=True)
    p.add_argument("--momentum-resolution-inv-a-fwhm", type=float, required=True)
    p.add_argument("--receipt")
    a = p.parse_args()
    out = fit(
        a.material_spectral_npz,
        a.calibrated_arpes_npz,
        a.energy_resolution_mev_fwhm,
        a.momentum_resolution_inv_a_fwhm,
    )
    if a.receipt:
        Path(a.receipt).write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))
