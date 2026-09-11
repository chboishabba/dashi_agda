#!/usr/bin/env python3
"""Render a provenance-preserving black-space trajectory as SVG.

Two deterministic demo modes are provided:
  birdsong  - an explicitly synthetic acoustic-feature trajectory;
  fly       - an explicitly synthetic linked sensorimotor trajectory.

The renderer is deliberately downstream-only.  It never treats visual
proximity, recurrence, or a generated SVG as biological/acoustic authority.
Real producers can instead provide CSV rows with:

    t,x,y,z,channel,provenance

The script emits both an SVG and a JSON receipt containing the exact input
hash, render parameters, point count, channels, and non-promotion boundary.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import html
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Sequence


@dataclass(frozen=True)
class Point:
    t: float
    x: float
    y: float
    z: float
    channel: str
    provenance: str


def synthetic_birdsong(samples: int = 240) -> List[Point]:
    """Synthetic feature-manifold fixture; not a field recording."""
    rows: List[Point] = []
    for i in range(samples):
        t = i / 60.0
        phrase = (i // 60) % 4
        phase = 2.0 * math.pi * (i % 60) / 60.0
        # Three declared synthetic feature coordinates.  They resemble the
        # repeated loops / jumps common in state-space birdsong renderings but
        # are not claimed to be MFCC/PCA/UMAP output.
        x = math.cos(phase) * (1.0 + 0.15 * phrase)
        y = math.sin(phase * (1.0 + 0.08 * phrase))
        z = 0.45 * math.sin(3.0 * phase) + 0.38 * phrase
        rows.append(
            Point(
                t=t,
                x=x,
                y=y,
                z=z,
                channel="acoustic-feature-state",
                provenance="synthetic-birdsong-demo",
            )
        )
    return rows


def synthetic_fly(samples_per_stage: int = 70) -> List[Point]:
    """Synthetic linked fly sensorimotor fixture; not measured MaleCNS data."""
    channels = [
        "neural",
        "motor",
        "effector",
        "body",
        "behaviour",
        "sensory-return",
    ]
    rows: List[Point] = []
    for cidx, channel in enumerate(channels):
        lag = 0.18 * cidx
        for i in range(samples_per_stage):
            t = i / 35.0 + lag
            phase = 2.0 * math.pi * i / samples_per_stage
            radius = 0.8 + 0.08 * cidx
            x = radius * math.cos(phase + 0.22 * cidx)
            y = radius * math.sin(phase + 0.22 * cidx)
            z = 0.5 * math.sin(2.0 * phase + 0.35 * cidx) + 0.42 * cidx
            rows.append(
                Point(
                    t=t,
                    x=x,
                    y=y,
                    z=z,
                    channel=channel,
                    provenance="synthetic-fly-sensorimotor-demo",
                )
            )
    return rows


def load_csv(path: Path) -> List[Point]:
    points: List[Point] = []
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        required = {"t", "x", "y", "z", "channel"}
        missing = required.difference(reader.fieldnames or [])
        if missing:
            raise ValueError(f"CSV missing columns: {sorted(missing)}")
        for row in reader:
            points.append(
                Point(
                    t=float(row["t"]),
                    x=float(row["x"]),
                    y=float(row["y"]),
                    z=float(row["z"]),
                    channel=row["channel"],
                    provenance=row.get("provenance", "external-csv"),
                )
            )
    return points


def normalise(points: Sequence[Point]) -> List[Point]:
    if not points:
        raise ValueError("no points")
    xs = [p.x for p in points]
    ys = [p.y for p in points]
    zs = [p.z for p in points]
    cx = 0.5 * (min(xs) + max(xs))
    cy = 0.5 * (min(ys) + max(ys))
    cz = 0.5 * (min(zs) + max(zs))
    span = max(max(xs) - min(xs), max(ys) - min(ys), max(zs) - min(zs), 1e-9)
    return [
        Point(p.t, (p.x - cx) / span, (p.y - cy) / span, (p.z - cz) / span, p.channel, p.provenance)
        for p in points
    ]


def project(p: Point, width: int, height: int) -> tuple[float, float]:
    # Fixed isometric projection.  It is a rendering choice, not a scientific
    # coordinate transform.
    px = p.x - 0.55 * p.z
    py = p.y + 0.35 * p.z
    scale = 0.78 * min(width, height)
    return width / 2.0 + scale * px, height / 2.0 - scale * py


def channel_hue(channel: str) -> int:
    digest = hashlib.sha256(channel.encode("utf-8")).digest()
    return int.from_bytes(digest[:2], "big") % 360


def svg(points: Sequence[Point], width: int, height: int, title: str) -> str:
    points = normalise(points)
    channels = sorted({p.channel for p in points})
    by_channel = {c: [p for p in points if p.channel == c] for c in channels}
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="#050505"/>',
        f'<text x="24" y="34" fill="#eeeeee" font-family="monospace" font-size="18">{html.escape(title)}</text>',
        '<text x="24" y="56" fill="#999999" font-family="monospace" font-size="11">rendered observer; geometry is not biological/acoustic authority</text>',
    ]
    for channel in channels:
        seq = by_channel[channel]
        hue = channel_hue(channel)
        coords = [project(p, width, height) for p in seq]
        poly = " ".join(f"{x:.2f},{y:.2f}" for x, y in coords)
        parts.append(
            f'<polyline points="{poly}" fill="none" stroke="hsl({hue} 72% 62%)" stroke-width="1.35" stroke-opacity="0.72"/>'
        )
        stride = max(1, len(seq) // 45)
        for p, (x, y) in list(zip(seq, coords))[::stride]:
            tooltip = html.escape(
                f"t={p.t:.6g}; channel={p.channel}; provenance={p.provenance}; source=({p.x:.6g},{p.y:.6g},{p.z:.6g})"
            )
            parts.append(
                f'<circle cx="{x:.2f}" cy="{y:.2f}" r="2.1" fill="hsl({hue} 80% 68%)"><title>{tooltip}</title></circle>'
            )
    parts.append("</svg>")
    return "\n".join(parts) + "\n"


def canonical_bytes(points: Iterable[Point]) -> bytes:
    rows = [
        {
            "t": p.t,
            "x": p.x,
            "y": p.y,
            "z": p.z,
            "channel": p.channel,
            "provenance": p.provenance,
        }
        for p in points
    ]
    return json.dumps(rows, sort_keys=True, separators=(",", ":")).encode("utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--demo", choices=("birdsong", "fly"))
    source.add_argument("--csv", type=Path)
    parser.add_argument("--out", type=Path, required=True, help="SVG output path")
    parser.add_argument("--receipt", type=Path, help="JSON receipt path; defaults beside SVG")
    parser.add_argument("--width", type=int, default=1100)
    parser.add_argument("--height", type=int, default=760)
    args = parser.parse_args()

    if args.demo == "birdsong":
        points = synthetic_birdsong()
        mode = "synthetic-birdsong-demo"
    elif args.demo == "fly":
        points = synthetic_fly()
        mode = "synthetic-fly-sensorimotor-demo"
    else:
        points = load_csv(args.csv)
        mode = "external-csv"

    payload = canonical_bytes(points)
    digest = hashlib.sha256(payload).hexdigest()
    title = f"DASHI state-space trajectory — {mode}"

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(svg(points, args.width, args.height, title), encoding="utf-8")

    receipt_path = args.receipt or args.out.with_suffix(".json")
    receipt = {
        "schema": "dashi-state-space-render-receipt-v1",
        "mode": mode,
        "point_count": len(points),
        "channels": sorted({p.channel for p in points}),
        "canonical_input_sha256": digest,
        "svg_path": str(args.out),
        "width": args.width,
        "height": args.height,
        "boundary": {
            "rendered_trajectory_is_scientific_authority": False,
            "visual_proximity_implies_physical_or_anatomical_proximity": False,
            "visual_recurrence_implies_same_generator": False,
            "provenance_embedded_in_point_tooltips": True,
        },
    }
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
