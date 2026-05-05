#!/usr/bin/env python3
"""Extract the DASHI W4/W5 CT18 PDF packet from a local LHAPDF grid.

This intentionally avoids requiring the LHAPDF Python bindings.  It reads the
LHAPDF6 ``lhagrid1`` central-member table and performs log-log bilinear
interpolation over x and Q for the stored x*f(x,Q) values.
"""

from __future__ import annotations

import argparse
import bisect
import hashlib
import json
import math
from pathlib import Path


FLAVORS_FOR_W4 = (-2, -1, 1, 2)
DY_LIGHT_FLAVORS = ((2, 4.0 / 9.0), (1, 1.0 / 9.0), (3, 1.0 / 9.0))


def _floats(line: str) -> list[float]:
    return [float(part) for part in line.split()]


def parse_lhagrid1(path: Path) -> dict:
    lines = path.read_text().splitlines()
    try:
        start = lines.index("---") + 1
    except ValueError as exc:
        raise ValueError(f"{path} has no lhagrid1 data separator") from exc

    x_grid = _floats(lines[start])
    q_grid = _floats(lines[start + 1])
    flavors = [int(part) for part in lines[start + 2].split()]
    rows = []
    for line in lines[start + 3 :]:
        if line.strip() == "---":
            break
        if line.strip():
            rows.append(_floats(line))

    expected = len(x_grid) * len(q_grid)
    if len(rows) != expected:
        raise ValueError(
            f"expected {expected} PDF rows ({len(x_grid)} x {len(q_grid)}), got {len(rows)}"
        )

    return {"x": x_grid, "q": q_grid, "flavors": flavors, "rows": rows}


def bracket(grid: list[float], value: float) -> tuple[int, int, float]:
    if value <= grid[0]:
        return 0, 0, 0.0
    if value >= grid[-1]:
        last = len(grid) - 1
        return last, last, 0.0
    hi = bisect.bisect_right(grid, value)
    lo = hi - 1
    log_lo = math.log(grid[lo])
    log_hi = math.log(grid[hi])
    t = (math.log(value) - log_lo) / (log_hi - log_lo)
    return lo, hi, t


def row(table: dict, ix: int, iq: int) -> list[float]:
    return table["rows"][ix * len(table["q"]) + iq]


def xfxq(table: dict, flavor: int, x: float, q: float) -> float:
    flavor_index = table["flavors"].index(flavor)
    x0, x1, tx = bracket(table["x"], x)
    q0, q1, tq = bracket(table["q"], q)

    def val(ix: int, iq: int) -> float:
        return row(table, ix, iq)[flavor_index]

    v00 = val(x0, q0)
    v10 = val(x1, q0)
    v01 = val(x0, q1)
    v11 = val(x1, q1)

    vx0 = v00 * (1.0 - tx) + v10 * tx
    vx1 = v01 * (1.0 - tx) + v11 * tx
    return vx0 * (1.0 - tq) + vx1 * tq


def luminosity_proxy(table: dict, x: float, q: float) -> float:
    return sum(xfxq(table, flavor, x, q) for flavor in FLAVORS_FOR_W4)


def compute_bin_integrated_luminosity(
    table: dict,
    mass_gev: float,
    *,
    sqrt_s: float = 13_000.0,
    eta_cut: float = 2.4,
    n_x: int = 200,
) -> float:
    """Rapidity-window DY luminosity using the local CT18 grid.

    This integrates dL/dtau over x on a log grid:
        int dx/x sum_q e_q^2 [q(x) qbar(tau/x) + qbar(x) q(tau/x)].
    The LHAPDF grid stores x*f(x,Q), so each point is divided by x before
    forming the luminosity. The eta window is intentionally recorded in the
    output because it is now part of the convention under audit.
    """

    tau = (mass_gev / sqrt_s) ** 2
    sqrt_tau = math.sqrt(tau)
    x_lo = max(sqrt_tau * math.exp(-eta_cut), table["x"][0])
    x_hi = min(sqrt_tau * math.exp(eta_cut), 0.999, table["x"][-1])
    if not x_lo < x_hi:
        return 0.0

    log_lo = math.log(x_lo)
    log_hi = math.log(x_hi)
    if n_x < 2:
        raise ValueError("n_x must be at least 2")

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
            q1 = xfxq(table, pid, x1, mass_gev) / x1
            qb1 = xfxq(table, -pid, x1, mass_gev) / x1
            q2 = xfxq(table, pid, x2, mass_gev) / x2
            qb2 = xfxq(table, -pid, x2, mass_gev) / x2
            luminosity += charge_weight * (q1 * qb2 + qb1 * q2)

        endpoint_weight = 0.5 if idx in (0, n_x - 1) else 1.0
        total += endpoint_weight * luminosity

    return total * step


def compute_mass_window_luminosity(
    table: dict,
    mass_low: float,
    mass_high: float,
    *,
    n_m: int = 80,
    sqrt_s: float = 13_000.0,
    eta_cut: float = 2.4,
    n_x: int = 200,
) -> float:
    """Integrate the rapidity-window luminosity over a mass window."""

    if n_m < 2:
        raise ValueError("n_m must be at least 2")
    step = (mass_high - mass_low) / (n_m - 1)
    total = 0.0
    for idx in range(n_m):
        mass = mass_low + step * idx
        endpoint_weight = 0.5 if idx in (0, n_m - 1) else 1.0
        total += endpoint_weight * compute_bin_integrated_luminosity(
            table,
            mass,
            sqrt_s=sqrt_s,
            eta_cut=eta_cut,
            n_x=n_x,
        )
    return total * step


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--grid",
        default="scripts/data/pdf/CT18NLO/CT18NLO_0000.dat",
        type=Path,
        help="central-member LHAPDF grid",
    )
    parser.add_argument(
        "--archive",
        default="scripts/data/pdf/CT18NLO.tar.gz",
        type=Path,
        help="downloaded CT18NLO archive, used for provenance digest",
    )
    parser.add_argument("--output", default="/tmp/ct18_dashi_pdf_packet.json", type=Path)
    parser.add_argument("--sqrt-s", default=13_000.0, type=float)
    parser.add_argument("--eta-cut", default=2.4, type=float)
    parser.add_argument("--n-x", default=200, type=int)
    parser.add_argument("--n-m", default=80, type=int)
    args = parser.parse_args()

    table = parse_lhagrid1(args.grid)
    x = 0.01
    q_t43 = 61.64
    q_t45 = 134.24
    w5_num = xfxq(table, 2, x, q_t45)
    w5_den = xfxq(table, 2, x, q_t43)
    w5_ratio = w5_num / w5_den
    required = 0.8804486068
    lum_t43_center = compute_bin_integrated_luminosity(
        table, q_t43, sqrt_s=args.sqrt_s, eta_cut=args.eta_cut, n_x=args.n_x
    )
    lum_t45_center = compute_bin_integrated_luminosity(
        table, q_t45, sqrt_s=args.sqrt_s, eta_cut=args.eta_cut, n_x=args.n_x
    )
    lum_t43_window = compute_mass_window_luminosity(
        table, 50.0, 76.0, sqrt_s=args.sqrt_s, eta_cut=args.eta_cut, n_x=args.n_x, n_m=args.n_m
    )
    lum_z_window = compute_mass_window_luminosity(
        table, 76.0, 106.0, sqrt_s=args.sqrt_s, eta_cut=args.eta_cut, n_x=args.n_x, n_m=args.n_m
    )
    lum_t45_window = compute_mass_window_luminosity(
        table, 106.0, 170.0, sqrt_s=args.sqrt_s, eta_cut=args.eta_cut, n_x=args.n_x, n_m=args.n_m
    )
    w5_center_luminosity_ratio = lum_t45_center / lum_t43_center
    w5_window_luminosity_ratio = lum_t45_window / lum_t43_window

    phi_bins = [0.004, 0.008, 0.015, 0.025, 0.04, 0.07, 0.12, 0.2, 0.35, 0.6, 1.0, 1.7, 3.0]
    q_z = 91.2
    w4_shape = [
        {
            "phi": phi,
            "x": max(phi * q_z / 13000.0, 1.0e-5),
            "luminosity_proxy": luminosity_proxy(table, max(phi * q_z / 13000.0, 1.0e-5), q_z),
        }
        for phi in phi_bins
    ]

    packet = {
        "pdf_set": "CT18NLO",
        "set_index": 14400,
        "member": 0,
        "format": "lhagrid1",
        "archive": str(args.archive),
        "archive_sha256": sha256(args.archive) if args.archive.exists() else None,
        "grid": str(args.grid),
        "grid_sha256": sha256(args.grid),
        "x": x,
        "Q_t43": q_t43,
        "Q_t45": q_t45,
        "W5_flavor": 2,
        "W5_numerator_xfxQ": w5_num,
        "W5_denominator_xfxQ": w5_den,
        "W5_correction_factor": w5_ratio,
        "W5_required_correction_factor": required,
        "W5_abs_gap": abs(w5_ratio - required),
        "W5_center_luminosity_ratio": w5_center_luminosity_ratio,
        "W5_center_luminosity_abs_gap": abs(w5_center_luminosity_ratio - required),
        "W5_window_luminosity_ratio": w5_window_luminosity_ratio,
        "W5_window_luminosity_abs_gap": abs(w5_window_luminosity_ratio - required),
        "W4W5_luminosity_convention": {
            "kind": "rapidity-window Drell-Yan light-quark luminosity",
            "sqrt_s": args.sqrt_s,
            "eta_cut": args.eta_cut,
            "n_x": args.n_x,
            "n_m": args.n_m,
            "flavors": [{"pid": pid, "charge_weight": weight} for pid, weight in DY_LIGHT_FLAVORS],
            "mass_windows": {
                "t43_below_z": [50.0, 76.0],
                "z_peak": [76.0, 106.0],
                "t45_above_z": [106.0, 170.0],
            },
        },
        "W4W5_luminosities": {
            "t43_center": lum_t43_center,
            "t45_center": lum_t45_center,
            "t43_window": lum_t43_window,
            "z_peak_window": lum_z_window,
            "t45_window": lum_t45_window,
            "z_over_t43_window": lum_z_window / lum_t43_window,
            "t45_over_z_window": lum_t45_window / lum_z_window,
        },
        "W4_Q_Z": q_z,
        "W4_luminosity_shape": w4_shape,
        "interpolation": "log-x/log-Q bilinear over LHAPDF6 lhagrid1 x*f(x,Q) values",
    }
    args.output.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n")
    print(json.dumps(packet, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
