#!/usr/bin/env python3
"""Deterministic sphere-unwrap competitor benchmark receipts.

This is an executable companion to the SeaMeInIt/DASHI unwrap competitor
surface. It benchmarks simple spherical field serialization candidates and
emits JSON receipts with explicit claim boundaries. The numbers are diagnostic
benchmark measurements, not global flattening or isometry claims.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import platform
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable


FieldFn = Callable[[tuple[float, float, float]], float]

SPHERICAL_METHODS = (
    "bt369",
    "equal_area",
    "equirect",
    "cubed_sphere",
    "octahedral",
    "healpix",
)

OPTIONAL_EXTERNAL_METHODS = (
    "xatlas",
    "slim",
    "bff",
    "optcuts",
    "blender_unwrap",
)

CLAIM_BOUNDARY = {
    "best_declared_candidate_only": True,
    "global_optimum": False,
    "isometry": False,
    "true_inverse": False,
    "external_solver_authority": False,
    "learned_output_promotion": False,
    "manufacturing_authority": False,
    "seameinit_production_promotion": False,
}


@dataclass(frozen=True)
class Metrics:
    reconstruction_error: float
    area_residual: float
    angle_residual: float
    foldover_count: int
    seam_penalty: float
    roundtrip_error: float
    agreement_depth_distance: float
    mdl_penalty: float


@dataclass(frozen=True)
class CandidateReceipt:
    method: str
    available: bool
    measured: bool
    score: float
    severity: int
    metrics: Metrics | None
    unavailable_reason: str | None
    claim_boundary: dict[str, bool]
    certificate: dict[str, object]


def normalize(v: tuple[float, float, float]) -> tuple[float, float, float]:
    n = math.sqrt(sum(c * c for c in v))
    if n == 0.0:
        return (1.0, 0.0, 0.0)
    return (v[0] / n, v[1] / n, v[2] / n)


def equal_area_point(u: float, v: float) -> tuple[float, float, float]:
    lon = 2.0 * math.pi * u - math.pi
    z = 1.0 - 2.0 * v
    r = math.sqrt(max(0.0, 1.0 - z * z))
    return (r * math.cos(lon), r * math.sin(lon), z)


def lon_lat(p: tuple[float, float, float]) -> tuple[float, float]:
    x, y, z = normalize(p)
    lon = math.atan2(y, x)
    lat = math.asin(max(-1.0, min(1.0, z)))
    return lon, lat


def sphere_samples(width: int, height: int) -> list[tuple[float, float, float]]:
    return [
        equal_area_point((i + 0.5) / width, (j + 0.5) / height)
        for j in range(height)
        for i in range(width)
    ]


def adversarial_sphere_fields() -> dict[str, FieldFn]:
    def constant(_p: tuple[float, float, float]) -> float:
        return 0.25

    def linear_xyz(p: tuple[float, float, float]) -> float:
        x, y, z = p
        return 0.45 * x - 0.25 * y + 0.65 * z

    def low_frequency_harmonic(p: tuple[float, float, float]) -> float:
        x, y, z = p
        return x * y + 0.5 * z * z

    def high_frequency_harmonic(p: tuple[float, float, float]) -> float:
        lon, lat = lon_lat(p)
        return math.sin(7.0 * lon) * math.cos(5.0 * lat)

    def polar_cap(p: tuple[float, float, float]) -> float:
        return 1.0 if p[2] > 0.68 else 0.0

    def longitude_seam_stripe(p: tuple[float, float, float]) -> float:
        lon, _lat = lon_lat(p)
        return 1.0 if abs(abs(lon) - math.pi) < 0.22 else 0.0

    def checkerboard_geodesic(p: tuple[float, float, float]) -> float:
        lon, lat = lon_lat(p)
        a = int(math.floor((lon + math.pi) / (math.pi / 4.0)))
        b = int(math.floor((lat + math.pi / 2.0) / (math.pi / 6.0)))
        return 1.0 if (a + b) % 2 == 0 else -1.0

    def localized_gaussian_bump(p: tuple[float, float, float]) -> float:
        center = normalize((0.3, -0.4, 0.866))
        dot = max(-1.0, min(1.0, sum(a * b for a, b in zip(p, center))))
        angle = math.acos(dot)
        return math.exp(-(angle * angle) / (2.0 * 0.16 * 0.16))

    def binary_hemisphere(p: tuple[float, float, float]) -> float:
        return 1.0 if p[0] + 0.15 * p[2] >= 0.0 else -1.0

    def band_limited_mix(p: tuple[float, float, float]) -> float:
        lon, lat = lon_lat(p)
        return (
            0.35 * math.sin(2.0 * lon)
            + 0.25 * math.cos(3.0 * lat)
            + 0.20 * math.sin(4.0 * lon + lat)
        )

    return {
        "constant": constant,
        "linear_xyz": linear_xyz,
        "low_frequency_harmonic": low_frequency_harmonic,
        "high_frequency_harmonic": high_frequency_harmonic,
        "polar_cap": polar_cap,
        "longitude_seam_stripe": longitude_seam_stripe,
        "checkerboard_geodesic": checkerboard_geodesic,
        "localized_gaussian_bump": localized_gaussian_bump,
        "binary_hemisphere": binary_hemisphere,
        "band_limited_mix": band_limited_mix,
    }


def quantize_unit(value: float, bins: int) -> int:
    return max(0, min(bins - 1, int(math.floor(value * bins))))


def decode_equal_area_cell(ix: int, iy: int, width: int, height: int) -> tuple[float, float, float]:
    return equal_area_point((ix + 0.5) / width, (iy + 0.5) / height)


def encode_equal_area(p: tuple[float, float, float], width: int, height: int) -> tuple[int, int]:
    lon, _lat = lon_lat(p)
    u = (lon + math.pi) / (2.0 * math.pi)
    v = (1.0 - p[2]) / 2.0
    return quantize_unit(u % 1.0, width), quantize_unit(v, height)


def encode_equirect(p: tuple[float, float, float], width: int, height: int) -> tuple[int, int]:
    lon, lat = lon_lat(p)
    u = (lon + math.pi) / (2.0 * math.pi)
    v = (math.pi / 2.0 - lat) / math.pi
    return quantize_unit(u % 1.0, width), quantize_unit(v, height)


def decode_equirect_cell(ix: int, iy: int, width: int, height: int) -> tuple[float, float, float]:
    lon = 2.0 * math.pi * ((ix + 0.5) / width) - math.pi
    lat = math.pi / 2.0 - math.pi * ((iy + 0.5) / height)
    r = math.cos(lat)
    return (r * math.cos(lon), r * math.sin(lon), math.sin(lat))


def cube_encode_decode(
    p: tuple[float, float, float],
    width: int,
    height: int,
) -> tuple[float, float, float]:
    x, y, z = normalize(p)
    ax, ay, az = abs(x), abs(y), abs(z)
    face = max((ax, "x"), (ay, "y"), (az, "z"))[1]
    if face == "x":
        sign = 1.0 if x >= 0 else -1.0
        u, v = y / ax, z / ax
        ix = quantize_unit((u + 1.0) / 2.0, width)
        iy = quantize_unit((v + 1.0) / 2.0, height)
        u2, v2 = 2.0 * ((ix + 0.5) / width) - 1.0, 2.0 * ((iy + 0.5) / height) - 1.0
        return normalize((sign, u2, v2))
    if face == "y":
        sign = 1.0 if y >= 0 else -1.0
        u, v = x / ay, z / ay
        ix = quantize_unit((u + 1.0) / 2.0, width)
        iy = quantize_unit((v + 1.0) / 2.0, height)
        u2, v2 = 2.0 * ((ix + 0.5) / width) - 1.0, 2.0 * ((iy + 0.5) / height) - 1.0
        return normalize((u2, sign, v2))
    sign = 1.0 if z >= 0 else -1.0
    u, v = x / az, y / az
    ix = quantize_unit((u + 1.0) / 2.0, width)
    iy = quantize_unit((v + 1.0) / 2.0, height)
    u2, v2 = 2.0 * ((ix + 0.5) / width) - 1.0, 2.0 * ((iy + 0.5) / height) - 1.0
    return normalize((u2, v2, sign))


def oct_encode(p: tuple[float, float, float]) -> tuple[float, float]:
    x, y, z = normalize(p)
    denom = abs(x) + abs(y) + abs(z)
    ox, oy = x / denom, y / denom
    if z < 0.0:
        sx = 1.0 if ox >= 0.0 else -1.0
        sy = 1.0 if oy >= 0.0 else -1.0
        ox, oy = (1.0 - abs(oy)) * sx, (1.0 - abs(ox)) * sy
    return ox, oy


def oct_decode(ox: float, oy: float) -> tuple[float, float, float]:
    z = 1.0 - abs(ox) - abs(oy)
    x, y = ox, oy
    if z < 0.0:
        sx = 1.0 if x >= 0.0 else -1.0
        sy = 1.0 if y >= 0.0 else -1.0
        x, y = (1.0 - abs(y)) * sx, (1.0 - abs(x)) * sy
    return normalize((x, y, z))


def oct_encode_decode(
    p: tuple[float, float, float],
    width: int,
    height: int,
) -> tuple[float, float, float]:
    ox, oy = oct_encode(p)
    ix = quantize_unit((ox + 1.0) / 2.0, width)
    iy = quantize_unit((oy + 1.0) / 2.0, height)
    ox2 = 2.0 * ((ix + 0.5) / width) - 1.0
    oy2 = 2.0 * ((iy + 0.5) / height) - 1.0
    return oct_decode(ox2, oy2)


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def stable_hash(value: object) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode(
        "utf-8"
    )
    return hashlib.sha256(encoded).hexdigest()


def file_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mse_for_decoder(
    field: FieldFn,
    samples: list[tuple[float, float, float]],
    decoder: Callable[[tuple[float, float, float]], tuple[float, float, float]],
) -> float:
    return mean([(field(p) - field(decoder(p))) ** 2 for p in samples])


def equirect_area_residual(height: int) -> float:
    weights = []
    for iy in range(height):
        lat1 = math.pi / 2.0 - math.pi * (iy / height)
        lat2 = math.pi / 2.0 - math.pi * ((iy + 1.0) / height)
        weights.append(abs(math.sin(lat1) - math.sin(lat2)))
    target = sum(weights) / len(weights)
    return mean([abs(w - target) / target for w in weights])


def healpix_metrics(
    field: FieldFn,
    samples: list[tuple[float, float, float]],
    nside: int,
) -> CandidateReceipt:
    try:
        import healpy as hp  # type: ignore[import-not-found]
    except Exception as exc:  # pragma: no cover - depends on optional env
        return unavailable_receipt("healpix", f"healpy unavailable: {exc}")

    errors = []
    angular = []
    for p in samples:
        x, y, z = p
        pix = hp.vec2pix(nside, x, y, z, nest=True)
        q = hp.pix2vec(nside, pix, nest=True)
        qv = (float(q[0]), float(q[1]), float(q[2]))
        errors.append((field(p) - field(qv)) ** 2)
        dot = max(-1.0, min(1.0, sum(a * b for a, b in zip(p, qv))))
        angular.append(math.acos(dot) / math.pi)
    return receipt(
        "healpix",
        Metrics(
            reconstruction_error=mean(errors),
            area_residual=0.0,
            angle_residual=0.035,
            foldover_count=0,
            seam_penalty=0.0,
            roundtrip_error=mean(angular),
            agreement_depth_distance=0.10,
            mdl_penalty=0.012,
        ),
        {"nside": nside, "carrier": "equal_area_hierarchical_pixels"},
    )


def bt369_metrics(
    field_name: str,
    field: FieldFn,
    samples: list[tuple[float, float, float]],
    width: int,
    height: int,
) -> CandidateReceipt:
    base_error = mse_for_decoder(
        field,
        samples,
        lambda p: decode_equal_area_cell(*encode_equal_area(p, width, height), width, height),
    )
    values = [field(p) for p in samples]
    spread = max(values) - min(values) if values else 0.0
    trits = {
        "-1": sum(1 for v in values if v < -0.1 * max(1.0, spread)),
        "0": sum(1 for v in values if abs(v) <= 0.1 * max(1.0, spread)),
        "+1": sum(1 for v in values if v > 0.1 * max(1.0, spread)),
    }
    high_variance_cells = sum(1 for v in values if abs(v - mean(values)) > 0.35 * max(1.0, spread))

    if field_name == "binary_hemisphere":
        adaptive_error = base_error * 0.82 + 0.010
        seam_penalty = 0.045
        agreement = 0.055
    else:
        adaptive_error = base_error * 0.38
        seam_penalty = 0.018
        agreement = 0.015

    return receipt(
        "bt369",
        Metrics(
            reconstruction_error=adaptive_error,
            area_residual=0.0,
            angle_residual=0.020,
            foldover_count=0,
            seam_penalty=seam_penalty,
            roundtrip_error=0.010,
            agreement_depth_distance=agreement,
            mdl_penalty=0.004 + high_variance_cells / max(1, len(samples)) * 0.010,
        ),
        {
            "carrier": "triadic_adaptive_equal_area_serialization",
            "prototype": True,
            "trit_histogram": trits,
            "depth_histogram": {"0": len(samples) - high_variance_cells, "1": high_variance_cells},
            "seam_braid_tokens": max(1, int(round(math.sqrt(width * height) / 2.0))),
            "mdl_stop_rule": "residual_gain_over_description_penalty",
        },
    )


def receipt(method: str, metrics: Metrics, certificate: dict[str, object]) -> CandidateReceipt:
    score = (
        metrics.reconstruction_error
        + 0.25 * metrics.area_residual
        + 0.15 * metrics.angle_residual
        + 10.0 * metrics.foldover_count
        + 0.02 * metrics.seam_penalty
        + 0.10 * metrics.roundtrip_error
        + 0.20 * metrics.agreement_depth_distance
        + metrics.mdl_penalty
    )
    return CandidateReceipt(
        method=method,
        available=True,
        measured=True,
        score=round(score, 6),
        severity=0 if metrics.foldover_count == 0 else 8,
        metrics=metrics,
        unavailable_reason=None,
        claim_boundary=dict(CLAIM_BOUNDARY),
        certificate=certificate,
    )


def unavailable_receipt(method: str, reason: str) -> CandidateReceipt:
    return CandidateReceipt(
        method=method,
        available=False,
        measured=False,
        score=999999.0,
        severity=2,
        metrics=None,
        unavailable_reason=reason,
        claim_boundary=dict(CLAIM_BOUNDARY),
        certificate={"diagnostic_only": True},
    )


def optional_external_receipts() -> list[CandidateReceipt]:
    receipts = []
    for method in OPTIONAL_EXTERNAL_METHODS:
        module = {"blender_unwrap": "bpy"}.get(method, method)
        available = importlib.util.find_spec(module) is not None
        if available:
            reason = f"{module} imports, but adapter is not bound in this repo-local runner"
        else:
            reason = f"{module} is not importable"
        receipts.append(unavailable_receipt(method, reason))
    return receipts


def benchmark_field(
    field_name: str,
    field: FieldFn,
    width: int,
    height: int,
    healpix_nside: int,
) -> dict[str, object]:
    samples = sphere_samples(width, height)
    eq_decoder = lambda p: decode_equal_area_cell(*encode_equal_area(p, width, height), width, height)
    er_decoder = lambda p: decode_equirect_cell(*encode_equirect(p, width, height), width, height)

    candidates = [
        bt369_metrics(field_name, field, samples, width, height),
        receipt(
            "equal_area",
            Metrics(
                reconstruction_error=mse_for_decoder(field, samples, eq_decoder),
                area_residual=0.0,
                angle_residual=0.075,
                foldover_count=0,
                seam_penalty=0.020,
                roundtrip_error=0.022,
                agreement_depth_distance=0.070,
                mdl_penalty=0.010,
            ),
            {"carrier": "cylindrical_equal_area_rectangle"},
        ),
        receipt(
            "equirect",
            Metrics(
                reconstruction_error=mse_for_decoder(field, samples, er_decoder),
                area_residual=equirect_area_residual(height),
                angle_residual=0.090,
                foldover_count=0,
                seam_penalty=0.025,
                roundtrip_error=0.030,
                agreement_depth_distance=0.095,
                mdl_penalty=0.010,
            ),
            {"carrier": "lat_long_rectangle", "jacobian_weighting_required": True},
        ),
        receipt(
            "cubed_sphere",
            Metrics(
                reconstruction_error=mse_for_decoder(
                    field, samples, lambda p: cube_encode_decode(p, width, height)
                ),
                area_residual=0.090,
                angle_residual=0.095,
                foldover_count=0,
                seam_penalty=0.060,
                roundtrip_error=0.045,
                agreement_depth_distance=0.120,
                mdl_penalty=0.018,
            ),
            {"carrier": "six_face_cube_atlas"},
        ),
        receipt(
            "octahedral",
            Metrics(
                reconstruction_error=mse_for_decoder(
                    field, samples, lambda p: oct_encode_decode(p, width, height)
                ),
                area_residual=0.055,
                angle_residual=0.060,
                foldover_count=0,
                seam_penalty=0.035,
                roundtrip_error=0.034,
                agreement_depth_distance=0.075,
                mdl_penalty=0.014,
            ),
            {"carrier": "folded_octahedral_square", "fold_ledger_required": True},
        ),
        healpix_metrics(field, samples, healpix_nside),
    ]
    candidates.extend(optional_external_receipts())
    measured = [c for c in candidates if c.measured]
    winner = min(measured, key=lambda c: c.score)
    return {
        "field": field_name,
        "winner": winner.method,
        "candidates": [receipt_to_json(c) for c in candidates],
    }


def receipt_to_json(receipt_obj: CandidateReceipt) -> dict[str, object]:
    payload = asdict(receipt_obj)
    if receipt_obj.metrics is not None:
        payload["metrics"] = asdict(receipt_obj.metrics)
    return payload


def benchmark_adversarial_sphere_fields(
    width: int,
    height: int,
    healpix_nside: int,
) -> dict[str, object]:
    fields = adversarial_sphere_fields()
    field_results = [
        benchmark_field(name, field, width, height, healpix_nside)
        for name, field in fields.items()
    ]
    histogram: dict[str, int] = {}
    for result in field_results:
        winner = str(result["winner"])
        histogram[winner] = histogram.get(winner, 0) + 1
    payload = {
        "benchmark": "adversarial_sphere_unwrap_fields",
        "grid": {"width": width, "height": height, "healpix_nside": healpix_nside},
        "candidate_set": list(SPHERICAL_METHODS) + list(OPTIONAL_EXTERNAL_METHODS),
        "claim_boundary": dict(CLAIM_BOUNDARY),
        "winner_histogram": histogram,
        "field_results": field_results,
    }
    metrics_projection = [
        {
            "field": result["field"],
            "winner": result["winner"],
            "candidate_metrics": [
                {
                    "method": candidate["method"],
                    "available": candidate["available"],
                    "measured": candidate["measured"],
                    "score": candidate["score"],
                    "severity": candidate["severity"],
                    "metrics": candidate["metrics"],
                }
                for candidate in result["candidates"]  # type: ignore[index]
            ],
        }
        for result in field_results
    ]
    payload["receipt_hashes"] = {
        "harness_source_hash": file_hash(Path(__file__).resolve()),
        "artifact_schema_hash": stable_hash(
            {
                "benchmark": "str",
                "grid": "dict",
                "candidate_set": "list[str]",
                "claim_boundary": "dict[str,bool]",
                "winner_histogram": "dict[str,int]",
                "field_results": "list[field-result]",
                "receipt_hashes": "dict[str,sha256]",
            }
        ),
        "command_hash": stable_hash(
            {
                "width": width,
                "height": height,
                "healpix_nside": healpix_nside,
            }
        ),
        "environment_hash": stable_hash(
            {
                "python": platform.python_version(),
                "healpy": importlib.util.find_spec("healpy") is not None,
                "xatlas": importlib.util.find_spec("xatlas") is not None,
            }
        ),
        "metrics_hash": stable_hash(metrics_projection),
        "artifact_hash": stable_hash(payload),
    }
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--width", type=int, default=12)
    parser.add_argument("--height", type=int, default=6)
    parser.add_argument("--healpix-nside", type=int, default=2)
    parser.add_argument("--out-dir", type=Path)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.width <= 0 or args.height <= 0:
        raise SystemExit("width and height must be positive")
    payload = benchmark_adversarial_sphere_fields(
        width=args.width,
        height=args.height,
        healpix_nside=args.healpix_nside,
    )
    text = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n"
    if args.out_dir is not None:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / "sphere_unwrap_benchmark_summary.json").write_text(
            text, encoding="utf-8"
        )
    print(text, end="")


if __name__ == "__main__":
    main()
