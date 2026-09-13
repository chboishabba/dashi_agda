#!/usr/bin/env python3
"""Formulaic j/KleinInvariantJ raster producer and comparison harness.

This script deliberately reuses ``cm_j_alpha_scan.py`` for the finite E4/E6
q-series implementation.  It does not create a second j evaluator.

The source-calibration distinction is explicit:

* ``standard-j`` uses the existing repo evaluator, normalized by j(i) ~= 1728.
* ``mathematica-klein-j`` divides that value by 1728, matching the Wolfram
  ``KleinInvariantJ`` normalization used by the Homann source family.

The default colour model is PHASE-ONLY.  It is useful for structural comparison
of argument/colour-wheel/pants seams, but it is NOT the exact Homann 2007 colour
function.  ``--claim-source-exact`` therefore fails closed unless an exact
Homann colour-model receipt and viewport calibration are explicitly supplied.

Output is a binary PPM so the core producer has no Pillow dependency.  If
Pillow is installed and ``--compare`` names an image, RGB metrics are emitted.
"""

from __future__ import annotations

import argparse
import colorsys
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from cm_j_alpha_scan import j_invariant


NORMALIZATION_STANDARD = "standard-j"
NORMALIZATION_MATHEMATICA = "mathematica-klein-j"
COLOR_PHASE_ONLY = "phase-only"
COLOR_HOMANN_EXACT = "homann-exact"


@dataclass(frozen=True)
class RasterConfig:
    width: int
    height: int
    xmin: float
    xmax: float
    ymin: float
    ymax: float
    terms: int
    normalization: str
    color_model: str


def normalized_j(tau: complex, terms: int, normalization: str) -> complex:
    value = j_invariant(tau, terms)
    if normalization == NORMALIZATION_STANDARD:
        return value
    if normalization == NORMALIZATION_MATHEMATICA:
        return value / 1728.0
    raise ValueError(f"unknown normalization: {normalization}")


def phase01(value: complex) -> float:
    """Map principal argument to one full hue turn [0,1)."""
    return (math.atan2(value.imag, value.real) / (2.0 * math.pi)) % 1.0


def phase_only_rgb(value: complex) -> tuple[int, int, int]:
    """Diagnostic only: constant saturation/value, hue = argument."""
    h = phase01(value)
    r, g, b = colorsys.hsv_to_rgb(h, 1.0, 1.0)
    return round(255 * r), round(255 * g), round(255 * b)


def render_rgb(value: complex, color_model: str) -> tuple[int, int, int]:
    if color_model == COLOR_PHASE_ONLY:
        return phase_only_rgb(value)
    if color_model == COLOR_HOMANN_EXACT:
        raise RuntimeError(
            "homann-exact is not yet admitted: exact Homann Mathematica colour "
            "function transcription is still an open source-calibration receipt"
        )
    raise ValueError(f"unknown color model: {color_model}")


def pixel_to_tau(config: RasterConfig, x: int, y: int) -> complex:
    """Affine pixel-centre chart; this is a parameter, not a source viewport claim."""
    re = config.xmin + (x + 0.5) * (config.xmax - config.xmin) / config.width
    # raster row zero is the top, so imaginary coordinate descends with y
    im = config.ymax - (y + 0.5) * (config.ymax - config.ymin) / config.height
    return complex(re, im)


def render(config: RasterConfig) -> bytearray:
    pixels = bytearray()
    for y in range(config.height):
        for x in range(config.width):
            tau = pixel_to_tau(config, x, y)
            try:
                value = normalized_j(tau, config.terms, config.normalization)
                rgb = render_rgb(value, config.color_model)
            except (ZeroDivisionError, OverflowError, ValueError):
                rgb = (0, 0, 0)
            pixels.extend(rgb)
    return pixels


def write_ppm(path: Path, config: RasterConfig, pixels: bytes) -> None:
    header = f"P6\n{config.width} {config.height}\n255\n".encode("ascii")
    path.write_bytes(header + pixels)


def compare_with_image(path: Path, config: RasterConfig, pixels: bytes) -> dict[str, float | int]:
    try:
        from PIL import Image
    except ImportError as exc:  # pragma: no cover - optional runtime dependency
        raise RuntimeError("comparison requires Pillow; raster generation does not") from exc

    source = Image.open(path).convert("RGB")
    if source.size != (config.width, config.height):
        raise RuntimeError(
            f"source size {source.size} != generated size {(config.width, config.height)}; "
            "resampling is intentionally not implicit"
        )

    source_bytes = source.tobytes()
    n = len(pixels)
    abs_sum = 0
    sq_sum = 0
    exact_pixels = 0
    max_abs = 0
    for i in range(0, n, 3):
        same = True
        for channel in range(3):
            d = int(pixels[i + channel]) - int(source_bytes[i + channel])
            ad = abs(d)
            abs_sum += ad
            sq_sum += d * d
            max_abs = max(max_abs, ad)
            if d:
                same = False
        if same:
            exact_pixels += 1

    pixel_count = config.width * config.height
    channel_count = pixel_count * 3
    return {
        "pixel_count": pixel_count,
        "mean_absolute_channel_error": abs_sum / channel_count,
        "rgb_rmse": math.sqrt(sq_sum / channel_count),
        "max_absolute_channel_error": max_abs,
        "exact_rgb_pixel_fraction": exact_pixels / pixel_count,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--width", type=int, default=947)
    parser.add_argument("--height", type=int, default=704)
    parser.add_argument("--xmin", type=float, default=-2.0)
    parser.add_argument("--xmax", type=float, default=2.0)
    parser.add_argument("--ymin", type=float, default=0.05)
    parser.add_argument("--ymax", type=float, default=3.0)
    parser.add_argument("--terms", type=int, default=80)
    parser.add_argument(
        "--normalization",
        choices=(NORMALIZATION_STANDARD, NORMALIZATION_MATHEMATICA),
        default=NORMALIZATION_MATHEMATICA,
    )
    parser.add_argument(
        "--color-model",
        choices=(COLOR_PHASE_ONLY, COLOR_HOMANN_EXACT),
        default=COLOR_PHASE_ONLY,
    )
    parser.add_argument("--compare", type=Path)
    parser.add_argument("--metadata", type=Path)
    parser.add_argument("--viewport-calibrated", action="store_true")
    parser.add_argument("--homann-color-transcribed", action="store_true")
    parser.add_argument("--claim-source-exact", action="store_true")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.width <= 0 or args.height <= 0:
        raise SystemExit("width and height must be positive")
    if args.terms <= 0:
        raise SystemExit("terms must be positive")
    if not (args.xmin < args.xmax and args.ymin < args.ymax):
        raise SystemExit("invalid viewport ordering")

    if args.claim_source_exact:
        blockers = []
        if not args.viewport_calibrated:
            blockers.append("source viewport is not calibrated")
        if not args.homann_color_transcribed:
            blockers.append("exact Homann colour function is not transcribed")
        if args.color_model != COLOR_HOMANN_EXACT:
            blockers.append("active colour model is not homann-exact")
        if blockers:
            raise SystemExit("source-exact claim blocked: " + "; ".join(blockers))

    config = RasterConfig(
        width=args.width,
        height=args.height,
        xmin=args.xmin,
        xmax=args.xmax,
        ymin=args.ymin,
        ymax=args.ymax,
        terms=args.terms,
        normalization=args.normalization,
        color_model=args.color_model,
    )

    pixels = render(config)
    write_ppm(args.output, config, pixels)

    metadata: dict[str, object] = {
        "status": "diagnostic_not_source_exact",
        "formula_owner": "scripts/cm_j_alpha_scan.py:j_invariant",
        "standard_formula": "1728*E4^3/(E4^3-E6^2)",
        "normalization": args.normalization,
        "normalization_factor_from_standard_j": (
            1.0 if args.normalization == NORMALIZATION_STANDARD else 1.0 / 1728.0
        ),
        "terms": args.terms,
        "raster": {
            "width": args.width,
            "height": args.height,
            "xmin": args.xmin,
            "xmax": args.xmax,
            "ymin": args.ymin,
            "ymax": args.ymax,
            "pixel_chart": "affine pixel-centre; row zero maps to ymax",
            "viewport_source_calibrated": bool(args.viewport_calibrated),
        },
        "color_model": args.color_model,
        "homann_color_function_transcribed": bool(args.homann_color_transcribed),
        "source_exact_claim": bool(args.claim_source_exact),
        "known_blockers": [
            "exact Homann Mathematica colour function transcription",
            "source image complex-plane viewport calibration",
            "finite q-series pixel error budget",
            "JPEG/postprocessing model if exact RGB equality is demanded",
        ],
    }

    if args.compare:
        metadata["comparison"] = compare_with_image(args.compare, config, pixels)

    metadata_path = args.metadata or args.output.with_suffix(args.output.suffix + ".json")
    metadata_path.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n")
    print(json.dumps(metadata, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
