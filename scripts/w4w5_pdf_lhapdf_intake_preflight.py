#!/usr/bin/env python3
"""Inspect W4/W5 LHAPDF/PDF intake readiness and emit a fail-closed artifact.

The preflight distinguishes three states that the W4/W5 lane must not collapse:

* a real LHAPDF runtime route;
* a repo-local equivalent-table CT18 candidate parse;
* an accepted provider authority packet.

Only the first or third can unlock the downstream runners.  The second is
checksum-bound candidate evidence and remains non-promoting.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import importlib.util
import json
import math
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any


ARTIFACT_SCHEMA = "dashi-w4w5-pdf-lhapdf-intake-preflight-v1"
TARGET_T45 = 0.8804486068
DY_LIGHT_FLAVORS = ((2, 4.0 / 9.0), (1, 1.0 / 9.0), (3, 1.0 / 9.0))
FLAVORS_FOR_W4 = (-2, -1, 1, 2)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def command_probe(name: str) -> dict[str, Any]:
    found = shutil.which(name)
    return {"name": name, "found": found is not None, "path": found}


def import_probe(name: str) -> dict[str, Any]:
    spec = importlib.util.find_spec(name)
    return {"module": name, "found": spec is not None, "origin": None if spec is None else spec.origin}


def lhapdf_pdfset_probe(repo_root: Path, pdf_set: str = "CT18NLO") -> dict[str, Any]:
    """Check whether the installed LHAPDF CLI can resolve the repo-local PDF set."""
    lhapdf = shutil.which("lhapdf")
    data_path = f"/usr/share/lhapdf/LHAPDF:{repo_root / 'scripts' / 'data' / 'pdf'}"
    if lhapdf is None:
        return {
            "pdf_set": pdf_set,
            "command": "lhapdf show",
            "found": False,
            "data_path": data_path,
            "returncode": None,
            "stdout": "",
            "stderr": "lhapdf command not found",
        }

    env = os.environ.copy()
    env["LHAPDF_DATA_PATH"] = data_path
    try:
        proc = subprocess.run(
            [lhapdf, "show", pdf_set],
            check=False,
            capture_output=True,
            env=env,
            text=True,
            timeout=20,
        )
    except Exception as exc:  # pragma: no cover - defensive environment guard
        return {
            "pdf_set": pdf_set,
            "command": "lhapdf show",
            "found": False,
            "data_path": data_path,
            "returncode": None,
            "stdout": "",
            "stderr": f"{type(exc).__name__}: {exc}",
        }

    return {
        "pdf_set": pdf_set,
        "command": "lhapdf show",
        "found": proc.returncode == 0,
        "data_path": data_path,
        "returncode": proc.returncode,
        "stdout": proc.stdout.strip(),
        "stderr": proc.stderr.strip(),
    }


def file_digest(path: Path) -> dict[str, Any]:
    return {
        "path": str(path),
        "present": path.exists(),
        "sha256": sha256_file(path) if path.exists() and path.is_file() else None,
        "size_bytes": path.stat().st_size if path.exists() and path.is_file() else None,
    }


def find_msht20_candidates(repo_root: Path) -> list[str]:
    roots = [
        repo_root / "scripts" / "data" / "pdf",
        Path.home() / ".local" / "share" / "LHAPDF",
        Path("/usr/local/share/LHAPDF"),
        Path("/usr/share/LHAPDF"),
    ]
    candidates: list[str] = []
    for root in roots:
        if not root.exists():
            continue
        for path in root.glob("MSHT20*"):
            candidates.append(str(path))
    return sorted(set(candidates))


def read_candidate_packet(path: Path | None) -> dict[str, Any]:
    if path is None:
        return {"present": False, "path": None}
    if not path.exists():
        return {"present": False, "path": str(path)}

    packet = json.loads(path.read_text(encoding="utf-8"))
    w4_shape = packet.get("W4_luminosity_shape")
    return {
        "present": True,
        "path": str(path),
        "sha256": sha256_file(path),
        "accepted_dy_luminosity_convention_status": packet.get(
            "accepted_dy_luminosity_convention_status"
        ),
        "accepted_dy_luminosity_first_missing": packet.get(
            "accepted_dy_luminosity_first_missing"
        ),
        "pdf_set": packet.get("pdf_set"),
        "set_index": packet.get("set_index"),
        "member": packet.get("member"),
        "grid_sha256": packet.get("grid_sha256"),
        "info_sha256": packet.get("info_sha256"),
        "archive_sha256": packet.get("archive_sha256"),
        "w4_candidate_bin_count": len(w4_shape) if isinstance(w4_shape, list) else None,
        "w5_target": packet.get("W5_required_correction_factor", TARGET_T45),
        "w5_fixed_x_ratio": packet.get("W5_correction_factor"),
        "w5_fixed_x_abs_gap": packet.get("W5_abs_gap"),
        "w5_t45_over_z_ratio": packet.get("W5_matching_target_luminosity_ratio"),
        "w5_t45_over_z_abs_gap": packet.get("W5_matching_target_luminosity_abs_gap"),
        "w5_t45_over_t43_ratio": packet.get("W5_t43_denominator_hypothesis_ratio"),
        "w5_t45_over_t43_abs_gap": packet.get("W5_t43_denominator_hypothesis_abs_gap"),
    }


def compute_bin_integrated_luminosity(
    pdf: Any,
    mass_gev: float,
    *,
    sqrt_s: float = 13_000.0,
    eta_cut: float = 2.4,
    n_x: int = 200,
) -> float:
    tau = (mass_gev / sqrt_s) ** 2
    sqrt_tau = tau**0.5
    x_lo = max(sqrt_tau * math.exp(-eta_cut), 1.0e-7)
    x_hi = min(sqrt_tau * math.exp(eta_cut), 0.999)
    if not x_lo < x_hi:
        return 0.0
    if n_x < 2:
        raise ValueError("n_x must be at least 2")

    log_lo = math.log(x_lo)
    log_hi = math.log(x_hi)
    step = (log_hi - log_lo) / (n_x - 1)
    total = 0.0
    for idx in range(n_x):
        log_x = log_lo + step * idx
        x1 = math.exp(log_x)
        x2 = tau / x1
        if x2 <= 0.0 or x2 >= 1.0:
            continue

        luminosity = 0.0
        for pid, charge_weight in DY_LIGHT_FLAVORS:
            q1 = pdf.xfxQ(pid, x1, mass_gev) / x1
            qb1 = pdf.xfxQ(-pid, x1, mass_gev) / x1
            q2 = pdf.xfxQ(pid, x2, mass_gev) / x2
            qb2 = pdf.xfxQ(-pid, x2, mass_gev) / x2
            luminosity += charge_weight * (q1 * qb2 + qb1 * q2)

        endpoint_weight = 0.5 if idx in (0, n_x - 1) else 1.0
        total += endpoint_weight * luminosity

    return total * step


def compute_mass_window_luminosity(
    pdf: Any,
    mass_low: float,
    mass_high: float,
    *,
    n_m: int = 80,
    sqrt_s: float = 13_000.0,
    eta_cut: float = 2.4,
    n_x: int = 200,
) -> float:
    if n_m < 2:
        raise ValueError("n_m must be at least 2")
    step = (mass_high - mass_low) / (n_m - 1)
    total = 0.0
    for idx in range(n_m):
        mass = mass_low + step * idx
        endpoint_weight = 0.5 if idx in (0, n_m - 1) else 1.0
        total += endpoint_weight * compute_bin_integrated_luminosity(
            pdf,
            mass,
            sqrt_s=sqrt_s,
            eta_cut=eta_cut,
            n_x=n_x,
        )
    return total * step


def build_lhapdf_candidate(pdf_set: str = "CT18NLO", member: int = 0) -> dict[str, Any]:
    try:
        import lhapdf  # type: ignore[import-not-found]
    except ImportError as exc:
        return {
            "present": False,
            "status": "not_emitted_lhapdf_python_binding_unavailable",
            "error": str(exc),
        }

    pdf = lhapdf.mkPDF(pdf_set, member)
    x = 0.01
    q_t43 = 61.64
    q_t45 = 134.24
    q_z = 91.2
    w5_num = pdf.xfxQ(2, x, q_t45)
    w5_den = pdf.xfxQ(2, x, q_t43)
    lum_t43_center = compute_bin_integrated_luminosity(pdf, q_t43)
    lum_t45_center = compute_bin_integrated_luminosity(pdf, q_t45)
    lum_t43_window = compute_mass_window_luminosity(pdf, 50.0, 76.0)
    lum_z_window = compute_mass_window_luminosity(pdf, 76.0, 106.0)
    lum_t45_window = compute_mass_window_luminosity(pdf, 106.0, 170.0)
    phi_bins = [0.004, 0.008, 0.015, 0.025, 0.04, 0.07, 0.12, 0.2, 0.35, 0.6, 1.0, 1.7, 3.0]
    w4_shape = [
        {
            "phi": phi,
            "x": max(phi * q_z / 13_000.0, 1.0e-5),
            "luminosity_proxy": sum(
                pdf.xfxQ(flavor, max(phi * q_z / 13_000.0, 1.0e-5), q_z)
                for flavor in FLAVORS_FOR_W4
            ),
        }
        for phi in phi_bins
    ]

    fixed_x_ratio = w5_num / w5_den
    center_ratio = lum_t45_center / lum_t43_center
    window_ratio = lum_t45_window / lum_t43_window
    t45_over_z_ratio = lum_t45_window / lum_z_window
    return {
        "present": True,
        "status": "non_promoting_lhapdf_backed_candidate",
        "accepted_dy_luminosity_convention_status": "candidate_local_ct18nlo_lhapdf_convention_not_accepted",
        "accepted_dy_luminosity_first_missing": "missingAcceptedDYLuminosityConventionAuthority",
        "promotion": {
            "w4": False,
            "w5": False,
            "pdf_carrier": False,
            "accepted_dy_convention": False,
        },
        "pdf_set": pdf_set,
        "member": member,
        "lhapdf_version": getattr(lhapdf, "version", lambda: None)(),
        "lhapdf_data_path": os.environ.get("LHAPDF_DATA_PATH"),
        "W5_required_correction_factor": TARGET_T45,
        "W5_numerator_xfxQ": w5_num,
        "W5_denominator_xfxQ": w5_den,
        "W5_correction_factor": fixed_x_ratio,
        "W5_abs_gap": abs(fixed_x_ratio - TARGET_T45),
        "W5_center_luminosity_ratio": center_ratio,
        "W5_center_luminosity_abs_gap": abs(center_ratio - TARGET_T45),
        "W5_window_luminosity_ratio": window_ratio,
        "W5_window_luminosity_abs_gap": abs(window_ratio - TARGET_T45),
        "W5_matching_target_luminosity_ratio": t45_over_z_ratio,
        "W5_matching_target_luminosity_abs_gap": abs(t45_over_z_ratio - TARGET_T45),
        "W4_luminosity_shape": w4_shape,
        "W4W5_luminosities": {
            "t43_center": lum_t43_center,
            "t45_center": lum_t45_center,
            "t43_window": lum_t43_window,
            "z_peak_window": lum_z_window,
            "t45_window": lum_t45_window,
            "z_over_t43_window": lum_z_window / lum_t43_window,
            "t45_over_z_window": t45_over_z_ratio,
        },
        "convention": {
            "kind": "LHAPDF-backed rapidity-window Drell-Yan light-quark luminosity",
            "formula": "integral dlog(x1) sum_q e_q^2 [q(x1,Q) qbar(tau/x1,Q) + qbar(x1,Q) q(tau/x1,Q)] with tau = M^2/s",
            "scale_choice": "Q = dilepton mass for each center/window integration point",
            "sqrt_s": 13_000.0,
            "eta_cut": 2.4,
            "n_x": 200,
            "n_m": 80,
            "mass_windows": {
                "t43_below_z": [50.0, 76.0],
                "z_peak": [76.0, 106.0],
                "t45_above_z": [106.0, 170.0],
            },
        },
    }


def build_preflight(
    repo_root: Path,
    candidate_packet: Path | None,
    *,
    emit_lhapdf_candidate: bool = False,
) -> dict[str, Any]:
    lhapdf_command = command_probe("lhapdf")
    lhapdf_config = command_probe("lhapdf-config")
    python_lhapdf = import_probe("lhapdf")
    ct18_lhapdf = lhapdf_pdfset_probe(repo_root, "CT18NLO")
    msht20_candidates = find_msht20_candidates(repo_root)

    ct18_dir = repo_root / "scripts" / "data" / "pdf" / "CT18NLO"
    member_grids = sorted(ct18_dir.glob("CT18NLO_*.dat")) if ct18_dir.exists() else []
    real_lhapdf_runtime_available = (
        lhapdf_command["found"] or lhapdf_config["found"] or python_lhapdf["found"]
    )
    real_lhapdf_run_possible = real_lhapdf_runtime_available and ct18_lhapdf["found"]
    if real_lhapdf_run_possible:
        runtime_reason = (
            "LHAPDF runtime is present and resolves repo-local CT18NLO when "
            "LHAPDF_DATA_PATH is set to the recorded system-index-plus-repo path. "
            "W4/W5 remain non-promoting until accepted DY/PDF convention authority "
            "and provider provenance are supplied."
        )
        status = "blocked_missing_accepted_provider_authority"
    elif real_lhapdf_runtime_available:
        runtime_reason = (
            "LHAPDF runtime is present, but the target PDF set was not resolved by "
            "the recorded data-path probe; W4/W5 remain fail-closed."
        )
        status = "blocked_lhapdf_pdfset_unresolved_or_missing_accepted_provider_authority"
    else:
        runtime_reason = (
            "No LHAPDF executable, lhapdf-config, or Python lhapdf binding is "
            "available in this environment; CT18NLO can only be consumed by the "
            "repo-local lhagrid1 table parser."
        )
        status = "blocked_no_real_lhapdf_runtime_or_accepted_provider_authority"

    return {
        "artifact_schema": ARTIFACT_SCHEMA,
        "worker": "Euler the 2nd / W4W5-PDF-shared-intake",
        "date": "2026-05-13",
        "status": status,
        "promotion": {
            "w4": False,
            "w5": False,
            "pdf_carrier": False,
            "accepted_dy_convention": False,
        },
        "environment": {
            "python_executable": sys.executable,
            "python_version": sys.version.replace("\n", " "),
            "commands": {
                "lhapdf": lhapdf_command,
                "lhapdf_config": lhapdf_config,
            },
            "python_modules": {
                "lhapdf": python_lhapdf,
            },
        },
        "runtime_decision": {
            "real_lhapdf_runtime_available": real_lhapdf_runtime_available,
            "real_lhapdf_run_possible": real_lhapdf_run_possible,
            "reason": runtime_reason,
            "ct18_lhapdf_probe": ct18_lhapdf,
        },
        "local_pdf_inventory": {
            "ct18nlo": {
                "directory": str(ct18_dir),
                "directory_present": ct18_dir.exists(),
                "member_grid_count": len(member_grids),
                "archive": file_digest(repo_root / "scripts" / "data" / "pdf" / "CT18NLO.tar.gz"),
                "info": file_digest(ct18_dir / "CT18NLO.info"),
                "central_member_grid": file_digest(ct18_dir / "CT18NLO_0000.dat"),
            },
            "msht20": {
                "candidates": msht20_candidates,
                "local_grid_present": bool(msht20_candidates),
            },
        },
        "candidate_ct18_equivalent_table_run": read_candidate_packet(candidate_packet),
        "lhapdf_backed_candidate_run": build_lhapdf_candidate()
        if emit_lhapdf_candidate
        else {
            "present": False,
            "status": "not_requested",
        },
        "provider_authority": {
            "accepted_or_replacement_packet_present": False,
            "first_missing": "missingAcceptedDYLuminosityConventionAuthority",
            "required_before_w4_w5_runners": [
                "accepted PDF set/version/member/error prescription",
                "accepted LHAPDF id or equivalent table identifier",
                "accepted grid/table checksums",
                "accepted factorization-scale convention",
                "accepted rapidity/eta integration convention",
                "accepted mass-bin integration rule for 50-76, 76-106, and 106-170 GeV",
                "accepted flavour weights and heavy-flavour policy",
                "provider luminosities for W5 L43/L45 and W4 per-bin ell_i",
                "efficiency/acceptance model, systematic budget, normalization-preservation law, and conversion law",
                "provider command/API, inputs, checksums, timestamp, and no-manual-overfit attestation",
            ],
        },
        "w4_w5_correction_output_status": {
            "w4_z_peak": (
                "not emitted: W4 adequacy runner requires accepted DY authority and "
                "accepted per-bin luminosity vector"
            ),
            "w5_t45": (
                "not emitted: W5 t45 runner requires accepted/replacement provider "
                "packet with L_M45_Y45 and L_M43_Y43"
            ),
        },
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--candidate-packet", type=Path)
    parser.add_argument(
        "--emit-lhapdf-candidate",
        action="store_true",
        help="Emit a non-promoting numeric candidate using the LHAPDF Python binding.",
    )
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = build_preflight(
        args.repo_root.resolve(),
        args.candidate_packet,
        emit_lhapdf_candidate=args.emit_lhapdf_candidate,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
