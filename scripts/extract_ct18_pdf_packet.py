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
    args = parser.parse_args()

    table = parse_lhagrid1(args.grid)
    x = 0.01
    q_t43 = 61.64
    q_t45 = 134.24
    w5_num = xfxq(table, 2, x, q_t45)
    w5_den = xfxq(table, 2, x, q_t43)
    w5_ratio = w5_num / w5_den
    required = 0.8804486068

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
        "W4_Q_Z": q_z,
        "W4_luminosity_shape": w4_shape,
        "interpolation": "log-x/log-Q bilinear over LHAPDF6 lhagrid1 x*f(x,Q) values",
    }
    args.output.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n")
    print(json.dumps(packet, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
