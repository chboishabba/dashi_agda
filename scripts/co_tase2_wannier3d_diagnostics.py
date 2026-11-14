"""3D post-Wannier diagnostics for a literal Co1/4TaSe2 material Hamiltonian.

This consumer does not construct a material Hamiltonian. It consumes an
independently generated Wannier90 real-space Hamiltonian and explicit spin
operators in the SAME basis. It provides:
  * band energies on a 3D fractional-k grid;
  * <Sx>, <Sy>, <Sz> per band;
  * analytic dH/dk from Wannier hoppings;
  * band-resolved Berry curvature (Kubo formula);
  * adjacent-band gap minima / Weyl candidates;
  * optional Berry-flux chirality around supplied candidate centres;
  * optional gauge-verified linear SOC continuation between two same-basis
    Wannier Hamiltonians at explicitly supplied probe points.

All topological outputs are computed results conditional on the supplied
Hamiltonian and basis metadata, not source observations.
"""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path
import numpy as np

try:
    import co_tase2_wannier90_spectral as w90
except ImportError:
    w90 = None

TWO_PI = 2.0 * np.pi


def h_and_derivs_fractional(k_frac, r_vectors, h_blocks, degeneracy):
    k = np.asarray(k_frac, float)
    rv = np.asarray(r_vectors, float)
    deg = np.asarray(degeneracy, float)
    phase = np.exp(2j * np.pi * (rv @ k)) / deg
    h = np.tensordot(phase, h_blocks, axes=(0, 0))
    derivs = []
    for axis in range(3):
        dphase = (2j * np.pi * rv[:, axis]) * phase
        derivs.append(np.tensordot(dphase, h_blocks, axes=(0, 0)))
    defect = float(np.max(np.abs(h - h.conj().T)))
    if defect > 1e-7:
        raise ValueError(f"non-Hermitian H(k), max defect={defect:g}")
    return h, derivs


def operator_expectations(evecs, operators):
    """Return expectations with shape (band, operator)."""
    u = np.asarray(evecs, complex)
    ops = [np.asarray(op, complex) for op in operators]
    n = u.shape[0]
    if u.shape != (n, n):
        raise ValueError("eigenvector matrix must be square")
    out = np.empty((n, len(ops)), float)
    for j, op in enumerate(ops):
        if op.shape != (n, n):
            raise ValueError("operator basis dimension mismatch")
        if np.max(np.abs(op - op.conj().T)) > 1e-9:
            raise ValueError("spin/observable operator must be Hermitian")
        transformed = u.conj().T @ op @ u
        out[:, j] = np.real(np.diag(transformed))
    return out


def berry_curvature_band(evals, evecs, derivs, band_index, gap_floor=1e-10):
    """Berry-curvature vector (Omega_yz, Omega_zx, Omega_xy).

    Derivatives may be with respect to fractional or Cartesian k; the returned
    curvature is in the corresponding coordinate convention.
    """
    e = np.asarray(evals, float)
    u = np.asarray(evecs, complex)
    d = [np.asarray(x, complex) for x in derivs]
    n = int(band_index)
    if not (0 <= n < len(e)):
        raise IndexError("band_index out of range")
    mats = [u.conj().T @ x @ u for x in d]
    pairs = ((1, 2), (2, 0), (0, 1))
    omega = np.zeros(3, float)
    for comp, (a, b) in enumerate(pairs):
        acc = 0.0
        for m in range(len(e)):
            if m == n:
                continue
            de = e[m] - e[n]
            if abs(de) <= gap_floor:
                raise ValueError("Berry curvature undefined at/too near degeneracy")
            acc += 2.0 * np.imag(mats[a][n, m] * mats[b][m, n]) / (de * de)
        omega[comp] = acc
    return omega


def berry_flux_cube(h_and_d_callback, center, half_width, band_index, face_n=21):
    """Midpoint integrate Berry flux through an axis-aligned cube."""
    c = np.asarray(center, float)
    h = float(half_width)
    n = int(face_n)
    if c.shape != (3,) or h <= 0 or n < 3:
        raise ValueError("invalid cube integration parameters")
    ds = 2.0 * h / n
    coords = -h + (np.arange(n) + 0.5) * ds
    flux = 0.0
    for axis in range(3):
        other = [i for i in range(3) if i != axis]
        for sign in (-1.0, 1.0):
            for a in coords:
                for b in coords:
                    k = c.copy()
                    k[axis] += sign * h
                    k[other[0]] += a
                    k[other[1]] += b
                    hh, dd = h_and_d_callback(k)
                    ev, uv = np.linalg.eigh(hh)
                    omega = berry_curvature_band(ev, uv, dd, band_index)
                    flux += sign * omega[axis] * ds * ds
    return float(flux)


def interpolate_same_basis_h(h_no_soc, h_soc, lam):
    """Linear continuation H(lambda)=H0+lambda(H1-H0) in one verified basis."""
    l = float(lam)
    if not (0.0 <= l <= 1.0):
        raise ValueError("SOC interpolation lambda must lie in [0,1]")
    h0 = np.asarray(h_no_soc, complex)
    h1 = np.asarray(h_soc, complex)
    if h0.shape != h1.shape or h0.ndim != 2 or h0.shape[0] != h0.shape[1]:
        raise ValueError("SOC endpoint Hamiltonians must be square and same shape")
    out = h0 + l * (h1 - h0)
    if np.max(np.abs(out - out.conj().T)) > 1e-9:
        raise ValueError("interpolated Hamiltonian is non-Hermitian")
    return out


def _load_spin_ops(path, num_wann):
    z = np.load(path)
    ops = []
    for key in ("Sx", "Sy", "Sz"):
        if key not in z:
            raise ValueError(f"spin operator artifact missing {key}")
        op = np.asarray(z[key], complex)
        if op.shape != (num_wann, num_wann):
            raise ValueError(f"{key} shape mismatch")
        if np.max(np.abs(op - op.conj().T)) > 1e-9:
            raise ValueError(f"{key} must be Hermitian")
        ops.append(op)
    return ops


def _grid_from_spec(spec):
    shape = [int(x) for x in spec.get("grid_shape", [11, 11, 11])]
    if len(shape) != 3 or any(x < 2 for x in shape):
        raise ValueError("grid_shape must contain three integers >=2")
    bounds = np.asarray(spec.get("fractional_bounds",
                                 [[-0.5, 0.5], [-0.5, 0.5], [-0.5, 0.5]]),
                        float)
    if bounds.shape != (3, 2) or np.any(bounds[:, 0] >= bounds[:, 1]):
        raise ValueError("fractional_bounds must be 3x2 increasing")
    axes = [np.linspace(bounds[i,0], bounds[i,1], shape[i], endpoint=False)
            for i in range(3)]
    return shape, bounds, axes


def diagnose(hr_path, metadata_path, spin_ops_path, grid_spec_path,
             output_path, receipt_path=None, no_soc_hr_path=None):
    if w90 is None:
        raise RuntimeError("co_tase2_wannier90_spectral must be importable")
    hr_path, metadata_path = Path(hr_path), Path(metadata_path)
    spin_ops_path, grid_spec_path = Path(spin_ops_path), Path(grid_spec_path)
    meta = json.loads(metadata_path.read_text())
    if meta.get("soc_included") is not True or meta.get("exchange_included") is not True:
        raise ValueError("literal material artifact must declare SOC and exchange")
    source_identity = str(meta.get("source_identity","")).strip()
    if not source_identity:
        raise ValueError("source_identity required")
    num_wann, rv, hb, deg = w90._load_hr(hr_path)
    ops = _load_spin_ops(spin_ops_path, num_wann)
    spec = json.loads(grid_spec_path.read_text())
    shape, bounds, axes = _grid_from_spec(spec)

    nk = int(np.prod(shape))
    energies = np.empty((*shape, num_wann), float)
    spins = np.empty((*shape, num_wann, 3), float)
    berry = np.empty((*shape, num_wann, 3), float)
    berry[:] = np.nan
    gap_floor = float(spec.get("berry_gap_floor_ev", 1e-6))
    candidates = []

    for ix,kx in enumerate(axes[0]):
      for iy,ky in enumerate(axes[1]):
       for iz,kz in enumerate(axes[2]):
        k = np.array([kx,ky,kz])
        h, d = h_and_derivs_fractional(k, rv, hb, deg)
        ev, uv = np.linalg.eigh(h)
        energies[ix,iy,iz] = ev
        spins[ix,iy,iz] = operator_expectations(uv, ops)
        for n in range(num_wann):
            sep = np.min(np.abs(ev[np.arange(num_wann)!=n]-ev[n])) if num_wann>1 else np.inf
            if sep > gap_floor:
                berry[ix,iy,iz,n] = berry_curvature_band(ev,uv,d,n,gap_floor=gap_floor)
        for n in range(num_wann-1):
            gap = float(ev[n+1]-ev[n])
            candidates.append((gap, n, k.tolist(), float(0.5*(ev[n+1]+ev[n]))))

    candidates.sort(key=lambda x:x[0])
    keep = int(spec.get("candidate_count", min(24,len(candidates))))
    cand = [{"direct_gap_ev":g,"lower_band":n,"k_fractional":k,"mid_energy_ev":em}
            for g,n,k,em in candidates[:keep]]

    flux_requests = spec.get("berry_flux_requests", [])
    flux_results = []
    callback = lambda kk: h_and_derivs_fractional(kk,rv,hb,deg)
    for req in flux_requests:
        center = np.asarray(req["center_fractional"],float)
        band = int(req["band_index"])
        half = float(req.get("half_width_fractional",0.02))
        face_n = int(req.get("face_n",15))
        flux = berry_flux_cube(callback,center,half,band,face_n)
        flux_results.append({
            "center_fractional":center.tolist(),
            "band_index":band,
            "half_width_fractional":half,
            "face_n":face_n,
            "berry_flux":flux,
            "chirality_estimate":flux/TWO_PI,
        })

    soc_continuation = []
    if no_soc_hr_path is not None:
        if meta.get("no_soc_same_basis_gauge_verified") is not True:
            raise ValueError(
                "no-SOC continuation requires no_soc_same_basis_gauge_verified=true"
            )
        nw0, rv0, hb0, deg0 = w90._load_hr(Path(no_soc_hr_path))
        if nw0 != num_wann or not np.array_equal(rv0, rv) or not np.array_equal(deg0, deg):
            raise ValueError("SOC/no-SOC Wannier artifacts do not share the same R/degen basis")
        lambdas = [float(x) for x in spec.get("soc_lambdas", [0.0, 0.25, 0.5, 0.75, 1.0])]
        probes = np.asarray(spec.get("soc_probe_points_fractional", []), float)
        if probes.ndim != 2 or probes.shape[1] != 3 or probes.shape[0] < 1:
            raise ValueError("SOC continuation requires soc_probe_points_fractional")
        for k in probes:
            h0, _ = h_and_derivs_fractional(k, rv0, hb0, deg0)
            h1, _ = h_and_derivs_fractional(k, rv, hb, deg)
            row = {"k_fractional": k.tolist(), "lambda": []}
            for lam in lambdas:
                hl = interpolate_same_basis_h(h0, h1, lam)
                ev, uv = np.linalg.eigh(hl)
                sp = operator_expectations(uv, ops)
                gaps = np.diff(ev)
                row["lambda"].append({
                    "lambda_soc": lam,
                    "eigenvalues_ev": ev.tolist(),
                    "spin_expectation": sp.tolist(),
                    "adjacent_gaps_ev": gaps.tolist(),
                })
            soc_continuation.append(row)

    provenance = {}
    for label,path in [("hr",hr_path),("metadata",metadata_path),
                       ("spin_ops",spin_ops_path),("grid_spec",grid_spec_path)]:
        provenance[label+"_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()

    np.savez_compressed(output_path,
        kx_fractional=axes[0], ky_fractional=axes[1], kz_fractional=axes[2],
        energies_ev=energies, spin_expectation=spins, berry_curvature_fractional=berry)

    receipt = {
        "source_identity": source_identity,
        "num_wann": num_wann,
        "grid_shape": shape,
        "grid_points": nk,
        "adjacent_gap_candidates": cand,
        "berry_flux_results": flux_results,
        "soc_continuation": soc_continuation,
        "provenance": provenance,
        "output_npz": str(output_path),
        "epistemic_boundary": (
            "computed conditional diagnostics of the supplied same-object Wannier Hamiltonian; "
            "not source observations and not evidence that the supplied Hamiltonian is itself valid"
        )
    }
    if receipt_path:
        Path(receipt_path).write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt


if __name__ == "__main__":
    p=argparse.ArgumentParser()
    p.add_argument("wannier90_hr_dat")
    p.add_argument("metadata_json")
    p.add_argument("spin_operators_npz")
    p.add_argument("grid_spec_json")
    p.add_argument("output_npz")
    p.add_argument("--receipt")
    p.add_argument("--no-soc-hr")
    a=p.parse_args()
    print(json.dumps(diagnose(a.wannier90_hr_dat,a.metadata_json,a.spin_operators_npz,
                              a.grid_spec_json,a.output_npz,a.receipt,a.no_soc_hr),indent=2))
