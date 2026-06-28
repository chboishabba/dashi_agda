#!/usr/bin/env python3
"""Parity smoke for the Schur/helical Vulkan scout path.

This is intentionally small and non-authoritative. It loads a shell-scoped
Schur checkpoint, exercises the restricted-sector matvec backend on the cached
Schur split, and then runs the helical coupling certificate overlay with the
same backend selection.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np

from ns_triad_kn_cross_shell_schur_symbolic_audit import (
    _load_schur_checkpoint,
    _make_restricted_backend,
    _q_helical_coupling_certificate_diagnostics,
)


SCRIPT_NAME = "scripts/ns_triad_kn_vulkan_schur_parity_smoke.py"
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_vulkan_schur_parity_smoke.json"
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--backend", choices=("cpu", "torch-gpu-scout", "vulkan-scout"), default="vulkan-scout")
    parser.add_argument("--gpu-checks", type=int, default=2)
    parser.add_argument("--row-chunk", type=int, default=192)
    parser.add_argument("--helical-max-dense-dim", type=int, default=2048)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_ready(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): _json_ready(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [_json_ready(v) for v in value]
    if isinstance(value, np.ndarray):
        return value.tolist()
    if isinstance(value, np.generic):
        return value.item()
    return value


def main() -> int:
    args = _parse_args()
    cached = _load_schur_checkpoint(args.checkpoint)
    M_CC = np.asarray(cached["M_CC"], dtype=np.float64)
    correction = np.asarray(cached["correction"], dtype=np.float64)
    shell_levels = np.asarray(cached["c_shell_levels"], dtype=np.float64)
    mode_keys = [tuple(int(v) for v in row) for row in cached["c_mode_keys"]]
    n = int(M_CC.shape[0])
    full_mask = np.ones(n, dtype=bool)

    restricted_backend = _make_restricted_backend(
        M_CC=M_CC,
        correction=correction,
        row_chunk=int(args.row_chunk),
        backend=args.backend,
        gpu_checks=int(args.gpu_checks),
    )
    restricted_diag: dict[str, Any]
    try:
        restricted_diag = {
            "backend": restricted_backend.name,
            **restricted_backend.info,
        }
    finally:
        restricted_backend.close()

    helical_diag = _q_helical_coupling_certificate_diagnostics(
        M_CC=M_CC,
        correction=correction,
        mode_keys=mode_keys,
        max_dense_dim=int(args.helical_max_dense_dim),
        matvec_backend=args.backend,
        gpu_checks=int(args.gpu_checks),
    )

    payload = {
        "script": SCRIPT_NAME,
        "checkpoint": str(args.checkpoint),
        "backend": args.backend,
        "status": "ok",
        "restricted_sector": {
            "sector_dimension": int(np.sum(full_mask)),
            "gpu_backend_status": restricted_diag.get("gpu_backend_status"),
            "gpu_domination_scout_installed": restricted_diag.get("gpu_domination_scout_installed"),
            "gpu_domination_scout_matches_cpu": restricted_diag.get("gpu_domination_scout_matches_cpu"),
            "gpu_cpu_parity_observed": restricted_diag.get("gpu_cpu_parity_observed"),
            "gpu_kn_authority": restricted_diag.get("gpu_kn_authority"),
            "gpu_backend_name": restricted_diag.get("gpu_backend_name"),
        },
        "helical_certificate": {
            "status": helical_diag.get("status"),
            "gpuSchurMatvecInstalled": helical_diag.get("gpuSchurMatvecInstalled"),
            "gpuCpuParityObserved": helical_diag.get("gpuCpuParityObserved"),
            "gpuHelicalCouplingScout": helical_diag.get("gpuHelicalCouplingScout"),
            "gpuKnAuthority": helical_diag.get("gpuKnAuthority"),
            "gpuBackendStatus": helical_diag.get("gpuBackendStatus"),
            "gpuBackendName": helical_diag.get("gpuBackendName"),
            "relative_bound_below_one_observed": helical_diag.get("relative_bound_below_one_observed"),
            "relative_bound_kappa": helical_diag.get("relative_bound_kappa"),
            "perturbation_lower_bound": helical_diag.get("perturbation_lower_bound"),
        },
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(_json_ready(payload), indent=2 if args.pretty else None),
        encoding="utf-8",
    )
    print(json.dumps(_json_ready(payload), indent=2 if args.pretty else None))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
