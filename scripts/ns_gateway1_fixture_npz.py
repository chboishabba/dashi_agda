#!/usr/bin/env python3
"""Generate deterministic NS-GW-1 Taylor-Green velocity NPZ fixtures."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np


DOMAIN_LENGTH = 2.0 * np.pi
SOURCE = "ns_gateway1_fixture_npz:taylor_green_incompressible"


def _validate_n(value: int) -> int:
    try:
        n = int(value)
    except (TypeError, ValueError) as exc:
        raise ValueError("N must be a positive integer") from exc
    if n <= 0:
        raise ValueError("N must be a positive integer")
    return n


def _validate_amplitude(value: float) -> float:
    amplitude = float(value)
    if not np.isfinite(amplitude):
        raise ValueError("amplitude must be finite")
    return amplitude


def _velocity_arrays(n: int, amplitude: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    x = np.linspace(0.0, DOMAIN_LENGTH, n, endpoint=False, dtype=np.float64)
    X, Y, Z = np.meshgrid(x, x, x, indexing="ij")
    u = amplitude * np.sin(X) * np.cos(Y) * np.cos(Z)
    v = -amplitude * np.cos(X) * np.sin(Y) * np.cos(Z)
    w = np.zeros_like(u)
    return u, v, w


def _output_path(path: str | Path) -> Path:
    output = Path(path)
    if output.suffix != ".npz":
        raise ValueError("output path must have .npz suffix")
    output.parent.mkdir(parents=True, exist_ok=True)
    return output


def make_fixture(
    N: int = 32,
    amplitude: float = 1.0,
    output: str | Path | None = None,
) -> str | dict[str, Any]:
    """Create a deterministic NS-GW-1 velocity fixture.

    If ``output`` is supplied, writes an NPZ containing ``u``, ``v``, ``w``,
    ``N``, ``amplitude``, and ``source``, then returns the output path string.
    If ``output`` is ``None``, returns a dict with the arrays and metadata.
    """

    n = _validate_n(N)
    amp = _validate_amplitude(amplitude)
    u, v, w = _velocity_arrays(n, amp)

    fixture: dict[str, Any] = {
        "u": u,
        "v": v,
        "w": w,
        "N": n,
        "domain_length": DOMAIN_LENGTH,
        "grid_spacing": DOMAIN_LENGTH / n,
        "amplitude": amp,
        "source": SOURCE,
    }
    if output is None:
        return fixture

    path = _output_path(output)
    np.savez(
        path,
        u=u,
        v=v,
        w=w,
        N=np.array(n, dtype=np.int64),
        domain_length=np.array(DOMAIN_LENGTH, dtype=np.float64),
        grid_spacing=np.array(DOMAIN_LENGTH / n, dtype=np.float64),
        amplitude=np.array(amp, dtype=np.float64),
        source=np.array(SOURCE),
    )
    return str(path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--N", type=int, required=True, help="positive cubic grid size")
    parser.add_argument("--amplitude", type=float, required=True, help="finite Taylor-Green amplitude")
    parser.add_argument("--output", type=Path, required=True, help="output .npz path")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    output = make_fixture(N=args.N, amplitude=args.amplitude, output=args.output)
    manifest = {
        "output": output,
        "N": int(args.N),
        "amplitude": float(args.amplitude),
        "source": SOURCE,
        "promotion_allowed": False,
    }
    print(json.dumps(manifest, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
