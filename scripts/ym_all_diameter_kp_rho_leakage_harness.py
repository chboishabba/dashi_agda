#!/usr/bin/env python3
"""YM all-diameter KP/rho/leakage diagnostic harness.

This is a fail-closed evidence harness for the p=7 Yang-Mills carrier lane.
It computes the geometric all-diameter KP majorant

    r = p * C0_eff * exp(a - beta*c_min)
    KP_inf = r / (1-r)

and related rho/leakage diagnostics from either local CSV inputs or
deterministic smoke rows.  Numeric success is not a Yang-Mills theorem: the
proof gate remains closed unless explicit certificate columns are present.
All Clay/YM promotion fields are therefore written false.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


PROMOTION_STATUS = "NO_PROMOTION_DIAGNOSTIC_ONLY"
FAIL_CLOSED_STATUS = "NO_PROMOTION_FAIL_CLOSED"
DEFAULT_BETAS = (6.0, 7.69, 10.13, 12.97, 13.64, 13.70, 16.70, 20.0)
CERT_COLUMNS = (
    "actual_activity_certified",
    "all_diameter_certified",
    "uniform_constants_certified",
    "overlap_compatibility_certified",
    "tail_closure_certified",
)


@dataclass(frozen=True)
class HarnessRow:
    row_id: int
    mode: str
    source_note: str
    beta: float
    beta_phys: float
    p: int
    c_min: float
    a: float
    C0: float
    leakage_multiplier: float
    C0_eff: float
    diameter_prefix: int
    r_geom: float
    kp_prefix_sum: float
    kp_all_diameter_sum: float
    kp_tail_after_prefix: float
    kp_converges: int
    kp_sum_lt_1: int
    beta_required_convergence: float
    beta_required_strict: float
    beta_gap_convergence: float
    beta_gap_strict: float
    strict_log_margin: float
    rho_geom: float
    rho_target: float
    rho_target_pass: int
    ca_q: float
    ca_pq: float
    ca_sum: float
    ca_converges: int
    ca_sum_lt_1: int
    numeric_kp_pass: int
    leakage_pass: int
    actual_activity_certified: int
    all_diameter_certified: int
    uniform_constants_certified: int
    overlap_compatibility_certified: int
    tail_closure_certified: int
    proof_gate_pass: int
    promotion_status: str
    fail_closed_reason: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--input-csv", type=Path, default=None)
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--betas", type=float, nargs="*", default=list(DEFAULT_BETAS))
    parser.add_argument("--p", type=int, default=7)
    parser.add_argument("--c-min", type=float, default=0.242)
    parser.add_argument("--a", type=float, default=0.5)
    parser.add_argument("--c0", type=float, default=1.0)
    parser.add_argument("--rho-target", type=float, default=0.90)
    parser.add_argument("--diameter-prefix", type=int, default=3)
    parser.add_argument(
        "--fail-on-open",
        action="store_true",
        help="exit nonzero when no row passes both numeric and proof gates",
    )
    return parser.parse_args()


def _get(row: dict[str, str], aliases: tuple[str, ...], default: Any = None) -> Any:
    lowered = {key.lower(): value for key, value in row.items()}
    for alias in aliases:
        if alias in row and row[alias] not in ("", None):
            return row[alias]
        value = lowered.get(alias.lower())
        if value not in ("", None):
            return value
    return default


def _float(row: dict[str, str], aliases: tuple[str, ...], default: float) -> float:
    raw = _get(row, aliases, default)
    try:
        value = float(raw)
    except (TypeError, ValueError):
        return float(default)
    return value


def _int(row: dict[str, str], aliases: tuple[str, ...], default: int) -> int:
    raw = _get(row, aliases, default)
    try:
        return int(float(raw))
    except (TypeError, ValueError):
        return int(default)


def _bool(row: dict[str, str], aliases: tuple[str, ...], default: bool = False) -> bool:
    raw = _get(row, aliases, None)
    if raw is None:
        return default
    if isinstance(raw, bool):
        return raw
    return str(raw).strip().lower() in {"1", "true", "yes", "y", "pass", "certified"}


def _finite(*values: float) -> bool:
    return all(math.isfinite(value) for value in values)


def _safe_exp(value: float) -> float:
    try:
        return math.exp(value)
    except OverflowError:
        return math.inf


def _geom_prefix(r: float, diameter_prefix: int) -> float:
    if not math.isfinite(r):
        return math.inf
    return sum(r**d for d in range(1, diameter_prefix + 1))


def _row_kind(path: Path | None) -> str:
    if path is None:
        return "synthetic_smoke"
    name = path.name.lower()
    if "monster" in name:
        return "leakage_stress"
    if "c0" in name or "threshold" in name:
        return "c0_threshold"
    if "d3" in name or "enumerator" in name:
        return "diameter_sample"
    return "kp_sample"


def _input_rows(args: argparse.Namespace) -> tuple[list[dict[str, str]], str]:
    if args.input_csv is not None:
        with args.input_csv.open(newline="", encoding="utf-8") as handle:
            return list(csv.DictReader(handle)), f"csv:{args.input_csv}"
    rows = []
    for beta in args.betas:
        rows.append(
            {
                "beta": str(beta),
                "p": str(args.p),
                "c_min": str(args.c_min),
                "a": str(args.a),
                "C0": str(args.c0),
                "promotion_status": "NO_PROMOTION",
                "source_note": "synthetic_smoke_formula",
            }
        )
    return rows, "synthetic_smoke"


def _compute_row(
    row_id: int,
    raw: dict[str, str],
    *,
    mode: str,
    args: argparse.Namespace,
    source_kind: str,
) -> HarnessRow:
    inferred_p = 7 if source_kind in {"kp_sample", "diameter_sample"} else args.p
    beta = _float(raw, ("beta", "beta_eff", "beta_carrier"), args.betas[0] if args.betas else 6.0)
    p = _int(raw, ("p", "prime", "branching_prime", "p_branching"), inferred_p)
    c_min = _float(raw, ("c_min", "cmin", "cMin", "c_min_bt"), args.c_min)
    a = _float(raw, ("a", "entropy_a", "activity_offset"), args.a)
    C0 = _float(raw, ("C0", "c0", "entropy_constant", "activity_multiplier"), args.c0)
    leakage_multiplier = _float(raw, ("leakage_multiplier",), 1.0)
    beta_phys = _float(raw, ("beta_phys", "beta_physical"), 6.0)
    diameter_prefix = _int(raw, ("diameter_prefix",), args.diameter_prefix)
    source_note = str(_get(raw, ("source_note", "source", "note"), mode))

    C0_eff = C0 * leakage_multiplier
    if C0_eff > 0.0 and p > 0 and c_min > 0.0:
        r = p * C0_eff * _safe_exp(a - beta * c_min)
        ca_q = C0_eff * _safe_exp(a - beta * c_min)
    else:
        r = math.inf
        ca_q = math.inf

    kp_prefix_sum = _geom_prefix(r, max(1, diameter_prefix))
    if 0.0 <= r < 1.0:
        kp_all = r / (1.0 - r)
        kp_tail = r ** (max(1, diameter_prefix) + 1) / (1.0 - r)
    else:
        kp_all = math.inf
        kp_tail = math.inf

    ca_pq = p * ca_q if math.isfinite(ca_q) else math.inf
    ca_sum = ca_q / ((1.0 - ca_pq) ** 2) if 0.0 <= ca_pq < 1.0 else math.inf

    if C0_eff > 0.0 and p > 0 and c_min > 0.0:
        beta_req_conv = (a + math.log(p * C0_eff)) / c_min
        beta_req_strict = (a + math.log(2.0 * p * C0_eff)) / c_min
        strict_margin = beta * c_min - a - math.log(2.0 * p * C0_eff)
    else:
        beta_req_conv = math.inf
        beta_req_strict = math.inf
        strict_margin = -math.inf

    beta_gap_conv = beta_req_conv - beta_phys if math.isfinite(beta_req_conv) else math.inf
    beta_gap_strict = beta_req_strict - beta_phys if math.isfinite(beta_req_strict) else math.inf

    proof_flags = {name: _bool(raw, (name,), False) for name in CERT_COLUMNS}
    kp_converges = 0 <= r < 1.0
    kp_sum_lt_1 = kp_all < 1.0
    rho_target_pass = r <= args.rho_target
    numeric_pass = (
        _finite(beta, float(p), c_min, a, C0_eff, r, kp_all, kp_tail, strict_margin)
        and p >= 2
        and c_min > 0.0
        and diameter_prefix >= 1
        and kp_converges
        and kp_sum_lt_1
        and rho_target_pass
        and strict_margin > 0.0
    )
    leakage_pass = math.isfinite(kp_tail) and kp_tail >= 0.0
    proof_gate_pass = numeric_pass and leakage_pass and all(proof_flags.values())

    reasons: list[str] = []
    if not numeric_pass:
        reasons.append("numeric_kp_or_rho_gate_open")
    if not leakage_pass:
        reasons.append("leakage_tail_not_finite")
    missing = [name for name, value in proof_flags.items() if not value]
    if missing:
        reasons.append("missing_certificates:" + "|".join(missing))
    if str(_get(raw, ("promotion_status", "promotion", "status"), "NO_PROMOTION")).upper() not in {
        "NO_PROMOTION",
        "NO_PROMOTION_DIAGNOSTIC_ONLY",
        "NO_PROMOTION_FAIL_CLOSED",
    }:
        reasons.append("input_promotion_status_not_authoritative")

    return HarnessRow(
        row_id=row_id,
        mode=source_kind,
        source_note=source_note,
        beta=beta,
        beta_phys=beta_phys,
        p=p,
        c_min=c_min,
        a=a,
        C0=C0,
        leakage_multiplier=leakage_multiplier,
        C0_eff=C0_eff,
        diameter_prefix=diameter_prefix,
        r_geom=r,
        kp_prefix_sum=kp_prefix_sum,
        kp_all_diameter_sum=kp_all,
        kp_tail_after_prefix=kp_tail,
        kp_converges=int(kp_converges),
        kp_sum_lt_1=int(kp_sum_lt_1),
        beta_required_convergence=beta_req_conv,
        beta_required_strict=beta_req_strict,
        beta_gap_convergence=beta_gap_conv,
        beta_gap_strict=beta_gap_strict,
        strict_log_margin=strict_margin,
        rho_geom=r,
        rho_target=args.rho_target,
        rho_target_pass=int(rho_target_pass),
        ca_q=ca_q,
        ca_pq=ca_pq,
        ca_sum=ca_sum,
        ca_converges=int(0.0 <= ca_pq < 1.0),
        ca_sum_lt_1=int(ca_sum < 1.0),
        numeric_kp_pass=int(numeric_pass),
        leakage_pass=int(leakage_pass),
        actual_activity_certified=int(proof_flags["actual_activity_certified"]),
        all_diameter_certified=int(proof_flags["all_diameter_certified"]),
        uniform_constants_certified=int(proof_flags["uniform_constants_certified"]),
        overlap_compatibility_certified=int(proof_flags["overlap_compatibility_certified"]),
        tail_closure_certified=int(proof_flags["tail_closure_certified"]),
        proof_gate_pass=int(proof_gate_pass),
        promotion_status=PROMOTION_STATUS,
        fail_closed_reason=";".join(reasons) if reasons else "carrier_kp_proof_gate_passed_no_clay_promotion",
    )


def _jsonable(value: Any) -> Any:
    if isinstance(value, float) and not math.isfinite(value):
        if math.isnan(value):
            return "nan"
        return "inf" if value > 0 else "-inf"
    return value


def _write_csv(path: Path, rows: list[HarnessRow]) -> None:
    fieldnames = list(HarnessRow.__dataclass_fields__.keys())
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(asdict(row))


def main() -> int:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    raw_rows, source = _input_rows(args)
    source_kind = _row_kind(args.input_csv)
    rows = [
        _compute_row(index, raw, mode=source, args=args, source_kind=source_kind)
        for index, raw in enumerate(raw_rows)
    ]

    table_path = args.out_dir / "ym_all_diameter_kp_rho_leakage_table.csv"
    checks_path = args.out_dir / "ym_all_diameter_kp_rho_leakage_checks.json"
    manifest_path = args.out_dir / "ym_all_diameter_kp_rho_leakage_manifest.json"
    _write_csv(table_path, rows)

    numeric_rows = sum(row.numeric_kp_pass for row in rows)
    proof_rows = sum(row.proof_gate_pass for row in rows)
    checks = {
        "pass": bool(proof_rows > 0),
        "numeric_rows_passing": int(numeric_rows),
        "proof_rows_passing": int(proof_rows),
        "rows": len(rows),
        "sup_r_geom": _jsonable(max((row.r_geom for row in rows), default=math.inf)),
        "inf_strict_log_margin": _jsonable(min((row.strict_log_margin for row in rows), default=-math.inf)),
        "promotion_status": FAIL_CLOSED_STATUS,
        "carrier_kp_numeric_diagnostic_pass_available": bool(numeric_rows > 0),
        "carrier_kp_proof_gate_pass_available": bool(proof_rows > 0),
        "continuum_yang_mills_promoted": False,
        "clay_yang_mills_promoted": False,
        "boundary": "Numeric KP/rho/leakage diagnostics are not all-diameter Wilson activity, Balaban continuum transfer, OS/Wightman reconstruction, mass gap, or Clay YM.",
    }
    manifest = {
        "script": Path(__file__).name,
        "source": source,
        "source_kind": source_kind,
        "outputs": {
            "table": str(table_path),
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "defaults": {
            "p": args.p,
            "c_min": args.c_min,
            "a": args.a,
            "C0": args.c0,
            "rho_target": args.rho_target,
            "diameter_prefix": args.diameter_prefix,
        },
        "certificate_columns": list(CERT_COLUMNS),
        "promotion_status": FAIL_CLOSED_STATUS,
    }
    checks_path.write_text(json.dumps(checks, indent=2, default=_jsonable), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    print(
        f"wrote {table_path}, {checks_path}, {manifest_path}; "
        f"numeric_rows={numeric_rows} proof_rows={proof_rows} "
        f"promotion={FAIL_CLOSED_STATUS}"
    )
    if args.fail_on_open and proof_rows == 0:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
