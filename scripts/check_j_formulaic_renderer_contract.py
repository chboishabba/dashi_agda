#!/usr/bin/env python3
"""Focused executable audit for the formulaic j/Base369 renderer.

This follows the repository's recent least-privilege checker pattern:

  existing atomic evaluator -> normalization/geometry checks -> renderer contract

It deliberately does not claim to reconstruct Jan Homann's historical RGB
colour function.  It checks only coordinates the current repository actually
owns: the E4/E6 j evaluator, positive 1728 normalization, the order-three
seam/orbit scale law, the canonical DASHI viewport, and deterministic phase
rasterization.
"""

from __future__ import annotations

import hashlib
import json
import math

from cm_j_alpha_scan import j_invariant
from j_invariant_formulaic_raster_compare import (
    COLOR_PHASE_ONLY,
    NORMALIZATION_MATHEMATICA,
    NORMALIZATION_STANDARD,
    RasterConfig,
    normalized_j,
    phase01,
    pixel_to_tau,
    render,
)

WIDTH = 947
HEIGHT = 704
XMIN = -1.5
XMAX = 1.2
YMIN = 0.0
YMAX = 1.95
TERMS = 80
EXPECTED_VISIBLE_SCALES = (1, 3, 7, 13, 21, 31, 43, 57)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def circular_phase_distance(a: float, b: float) -> float:
    d = abs(a - b) % 1.0
    return min(d, 1.0 - d)


def seam_scale(k: int) -> int:
    return k * k + k + 1


def left_order_three_orbit(k: int) -> complex:
    """Mirrored order-three family used by the annotated left-hand seam."""
    d = seam_scale(k)
    return complex(
        -(2 * k + 1) / (2.0 * d),
        math.sqrt(3.0) / (2.0 * d),
    )


def nearest_pixel(config: RasterConfig, z: complex) -> tuple[int, int]:
    px = round((z.real - config.xmin) * config.width / (config.xmax - config.xmin) - 0.5)
    py = round((config.ymax - z.imag) * config.height / (config.ymax - config.ymin) - 0.5)
    return px, py


def main() -> None:
    # Classical numerical anchors of the one existing evaluator.
    j_i = j_invariant(1j, TERMS)
    rho = complex(0.5, math.sqrt(3.0) / 2.0)
    j_rho = j_invariant(rho, TERMS)
    require(abs(j_i - 1728.0) < 1.0e-8, f"j(i) anchor drifted: {j_i!r}")
    require(abs(j_rho) < 1.0e-6, f"j(rho) anchor drifted: {j_rho!r}")

    # Standard j and Mathematica KleinInvariantJ differ by one positive scalar;
    # therefore their phase must be the same away from zero.
    phase_checks = []
    for tau in (complex(-0.37, 0.83), complex(0.21, 1.40), complex(0.63, 0.72)):
        standard = normalized_j(tau, TERMS, NORMALIZATION_STANDARD)
        mathematica = normalized_j(tau, TERMS, NORMALIZATION_MATHEMATICA)
        require(abs(standard - 1728.0 * mathematica) <= 1.0e-10 * max(1.0, abs(standard)),
                f"1728 normalization mismatch at {tau!r}")
        pd = circular_phase_distance(phase01(standard), phase01(mathematica))
        require(pd < 1.0e-12, f"positive normalization changed phase at {tau!r}: {pd}")
        phase_checks.append({"tau": [tau.real, tau.imag], "phase_distance_turns": pd})

    # Exact integer scale code for the visible annotated family.
    scales = tuple(seam_scale(k) for k in range(8))
    require(scales == EXPECTED_VISIBLE_SCALES, f"visible scale regression: {scales}")
    require(len(set(scales)) == len(scales), "visible scale code lost injectivity")

    config = RasterConfig(
        width=WIDTH,
        height=HEIGHT,
        xmin=XMIN,
        xmax=XMAX,
        ymin=YMIN,
        ymax=YMAX,
        terms=TERMS,
        normalization=NORMALIZATION_MATHEMATICA,
        color_model=COLOR_PHASE_ONLY,
    )

    # Every k=0..7 order-three point used by the visual regression lies in this
    # chart.  Mapping to the nearest pixel and back must stay inside one half-cell
    # in each coordinate (plus floating-point slack).
    dx = (XMAX - XMIN) / WIDTH
    dy = (YMAX - YMIN) / HEIGHT
    orbit_rows = []
    for k in range(8):
        z = left_order_three_orbit(k)
        require(XMIN <= z.real <= XMAX and YMIN <= z.imag <= YMAX,
                f"visible orbit point escaped canonical viewport: k={k}, z={z!r}")
        px, py = nearest_pixel(config, z)
        require(0 <= px < WIDTH and 0 <= py < HEIGHT,
                f"nearest pixel escaped raster: k={k}, pixel={(px, py)}")
        zr = pixel_to_tau(config, px, py)
        ex = abs(zr.real - z.real)
        ey = abs(zr.imag - z.imag)
        require(ex <= dx / 2.0 + 1.0e-15, f"x calibration exceeded half pixel for k={k}: {ex}")
        require(ey <= dy / 2.0 + 1.0e-15, f"y calibration exceeded half pixel for k={k}: {ey}")
        orbit_rows.append({
            "k": k,
            "D_k": seam_scale(k),
            "analytic": [z.real, z.imag],
            "pixel": [px, py],
            "decoded_pixel_centre": [zr.real, zr.imag],
            "absolute_error": [ex, ey],
        })

    # Small 3^3 diagnostic raster: same producer called twice must be byte-identical.
    # This is a determinism regression, not a claim that 27 pixels encode all jFine.
    tiny = RasterConfig(
        width=27,
        height=27,
        xmin=XMIN,
        xmax=XMAX,
        ymin=max(YMIN, 0.02),
        ymax=YMAX,
        terms=TERMS,
        normalization=NORMALIZATION_MATHEMATICA,
        color_model=COLOR_PHASE_ONLY,
    )
    first = bytes(render(tiny))
    second = bytes(render(tiny))
    require(first == second, "phase raster producer is nondeterministic")
    digest = hashlib.sha256(first).hexdigest()

    report = {
        "status": "pass",
        "claim_strength": "runtime_parity_not_source_exact_rgb",
        "evaluator": "scripts/cm_j_alpha_scan.py:j_invariant",
        "anchors": {
            "j_i": [j_i.real, j_i.imag],
            "j_rho_abs": abs(j_rho),
        },
        "normalization": {
            "standard_j_equals_1728_times_mathematica_klein_j": True,
            "phase_invariant_under_positive_1728_scale": True,
            "checks": phase_checks,
        },
        "canonical_viewport": {
            "width": WIDTH,
            "height": HEIGHT,
            "xmin": XMIN,
            "xmax": XMAX,
            "ymin": YMIN,
            "ymax": YMAX,
            "authority": "DASHI regression / annotated-axis receipt, not historical notebook proof",
        },
        "visible_order_three_orbit": orbit_rows,
        "visible_scales": list(scales),
        "tiny_27x27_phase_raster_sha256": digest,
        "source_exact_rgb": False,
        "remaining_source_rgb_blocker": "exact historical Homann Mathematica colour/tone function",
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
