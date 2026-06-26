#!/usr/bin/env python3
"""Option-B Balaban constant diagnostic.

This script computes a small, explicit arithmetic surface for Option-B
constant bookkeeping.  It is diagnostic only: it checks finite numeric
ceilings and a user-supplied symbolic KP threshold expression, but it does not
prove Balaban transfer, KP convergence, continuum Yang-Mills, a mass gap, or
any theorem-promotion claim.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from fractions import Fraction
from typing import Any, Sequence


CLAIM_SCOPE = "diagnostic_only"
KP_FORMULA = "2 * L^24 * E0 * C1 * C2 * eps4^-1 * eps6^-1 * M^q"
DEFAULT_BETAS = (6.0, 16.7)


@dataclass(frozen=True)
class CasimirRow:
    group: str
    nc: int
    representation: str
    casimir_fraction: str
    casimir_value: float
    b0_value: float
    b0_source: str
    b0_ceiling_formula: str
    b0_ceiling_value: float
    b0_margin: float
    b0_ceiling_pass: bool


@dataclass(frozen=True)
class WeakCouplingRow:
    group: str
    nc: int
    beta: float
    g_squared_formula: str
    g_squared: float
    weak_coupling_indicator: str
    weak_coupling_indicator_pass: bool


@dataclass(frozen=True)
class KPDiagnostic:
    formula: str
    e0: float
    c1: float
    c2: float
    l_value: float
    m_value: float
    q: float
    eps4: float
    eps6: float
    epsilon_product: float
    prefactor_without_q: float
    kp_activity: float
    kp_max: float
    kp_margin: float
    m_power_threshold: float
    epsilon_product_threshold: float
    kp_threshold_pass: bool
    finite_arithmetic: bool


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--format",
        choices=("json", "md"),
        default="json",
        help="Output format. Defaults to JSON.",
    )
    parser.add_argument(
        "--beta",
        type=float,
        nargs="+",
        default=list(DEFAULT_BETAS),
        help="Beta values for g^2(beta)=2*Nc/beta estimates.",
    )
    parser.add_argument(
        "--b0-su2",
        type=float,
        default=None,
        help="Optional SU(2) B0 diagnostic constant; defaults to sqrt(C_F).",
    )
    parser.add_argument(
        "--b0-su3",
        type=float,
        default=None,
        help="Optional SU(3) B0 diagnostic constant; defaults to sqrt(C_F).",
    )
    parser.add_argument("--E0", type=float, required=True, help="KP E0 constant.")
    parser.add_argument("--C1", type=float, required=True, help="KP C1 constant.")
    parser.add_argument("--C2", type=float, required=True, help="KP C2 constant.")
    parser.add_argument("--L", type=float, required=True, help="KP L constant.")
    parser.add_argument("--M", type=float, required=True, help="KP exponent M.")
    parser.add_argument("--q", type=float, required=True, help="KP q activity ratio.")
    parser.add_argument("--eps4", type=float, required=True, help="KP eps4 leakage.")
    parser.add_argument("--eps6", type=float, required=True, help="KP eps6 leakage.")
    parser.add_argument(
        "--kp-max",
        type=float,
        required=True,
        help="Maximum allowed diagnostic KP activity.",
    )
    return parser.parse_args(argv)


def require_finite(name: str, value: float) -> None:
    if not math.isfinite(value):
        raise ValueError(f"{name} must be finite")


def require_positive(name: str, value: float) -> None:
    require_finite(name, value)
    if value <= 0.0:
        raise ValueError(f"{name} must be positive")


def require_nonnegative(name: str, value: float) -> None:
    require_finite(name, value)
    if value < 0.0:
        raise ValueError(f"{name} must be non-negative")


def validate_args(args: argparse.Namespace) -> None:
    for beta in args.beta:
        require_positive("--beta", beta)
    if len(set(args.beta)) != len(args.beta):
        raise ValueError("--beta values must be unique")
    if args.b0_su2 is not None:
        require_nonnegative("--b0-su2", args.b0_su2)
    if args.b0_su3 is not None:
        require_nonnegative("--b0-su3", args.b0_su3)
    require_nonnegative("--E0", args.E0)
    require_nonnegative("--C1", args.C1)
    require_nonnegative("--C2", args.C2)
    require_positive("--L", args.L)
    require_nonnegative("--M", args.M)
    require_nonnegative("--q", args.q)
    require_positive("--eps4", args.eps4)
    require_positive("--eps6", args.eps6)
    require_positive("--kp-max", args.kp_max)


def fundamental_casimir(nc: int) -> Fraction:
    return Fraction(nc * nc - 1, 2 * nc)


def b0_value(nc: int, override: float | None) -> tuple[float, str]:
    if override is not None:
        return override, "user_supplied"
    casimir = fundamental_casimir(nc)
    return math.sqrt(float(casimir)), "sqrt_fundamental_casimir_default"


def casimir_rows(args: argparse.Namespace) -> list[CasimirRow]:
    su2_casimir = fundamental_casimir(2)
    su2_b0, su2_source = b0_value(2, args.b0_su2)
    su2_ceiling = math.sqrt(2.0)

    su3_casimir = fundamental_casimir(3)
    su3_b0, su3_source = b0_value(3, args.b0_su3)
    su3_ceiling = math.sqrt(3.0) * su2_b0

    return [
        CasimirRow(
            group="SU(2)",
            nc=2,
            representation="fundamental",
            casimir_fraction=f"{su2_casimir.numerator}/{su2_casimir.denominator}",
            casimir_value=float(su2_casimir),
            b0_value=su2_b0,
            b0_source=su2_source,
            b0_ceiling_formula="sqrt(2)",
            b0_ceiling_value=su2_ceiling,
            b0_margin=su2_ceiling - su2_b0,
            b0_ceiling_pass=su2_b0 <= su2_ceiling,
        ),
        CasimirRow(
            group="SU(3)",
            nc=3,
            representation="fundamental",
            casimir_fraction=f"{su3_casimir.numerator}/{su3_casimir.denominator}",
            casimir_value=float(su3_casimir),
            b0_value=su3_b0,
            b0_source=su3_source,
            b0_ceiling_formula="sqrt(3) * B0_SU2",
            b0_ceiling_value=su3_ceiling,
            b0_margin=su3_ceiling - su3_b0,
            b0_ceiling_pass=su3_b0 <= su3_ceiling,
        ),
    ]


def weak_coupling_rows(args: argparse.Namespace) -> list[WeakCouplingRow]:
    rows: list[WeakCouplingRow] = []
    for nc in (2, 3):
        for beta in sorted(args.beta):
            g_squared = 2.0 * float(nc) / beta
            rows.append(
                WeakCouplingRow(
                    group=f"SU({nc})",
                    nc=nc,
                    beta=beta,
                    g_squared_formula="2*Nc/beta",
                    g_squared=g_squared,
                    weak_coupling_indicator="g_squared < 1",
                    weak_coupling_indicator_pass=g_squared < 1.0,
                )
            )
    return rows


def safe_power(base: float, exponent: float) -> float:
    if base == 0.0 and exponent == 0.0:
        return 1.0
    try:
        return base**exponent
    except OverflowError:
        return math.inf


def kp_diagnostic(args: argparse.Namespace) -> KPDiagnostic:
    l_to_24 = safe_power(args.L, 24.0)
    m_to_q = safe_power(args.M, args.q)
    epsilon_product = args.eps4 * args.eps6
    prefactor_without_q = 2.0 * l_to_24 * args.E0 * args.C1 * args.C2 / epsilon_product
    kp_activity = prefactor_without_q * m_to_q
    finite_arithmetic = all(
        math.isfinite(value)
        for value in (l_to_24, m_to_q, epsilon_product, prefactor_without_q, kp_activity)
    )

    if prefactor_without_q > 0.0 and math.isfinite(prefactor_without_q):
        m_power_threshold = args.kp_max / prefactor_without_q
    elif prefactor_without_q == 0.0:
        m_power_threshold = math.inf
    else:
        m_power_threshold = math.nan

    denominator = 2.0 * l_to_24 * args.E0 * args.C1 * args.C2 * m_to_q
    if denominator > 0.0 and math.isfinite(denominator):
        epsilon_product_threshold = denominator / args.kp_max
    elif denominator == 0.0:
        epsilon_product_threshold = math.inf
    else:
        epsilon_product_threshold = math.nan

    return KPDiagnostic(
        formula=KP_FORMULA,
        e0=args.E0,
        c1=args.C1,
        c2=args.C2,
        l_value=args.L,
        m_value=args.M,
        q=args.q,
        eps4=args.eps4,
        eps6=args.eps6,
        epsilon_product=epsilon_product,
        prefactor_without_q=prefactor_without_q,
        kp_activity=kp_activity,
        kp_max=args.kp_max,
        kp_margin=args.kp_max - kp_activity,
        m_power_threshold=m_power_threshold,
        epsilon_product_threshold=epsilon_product_threshold,
        kp_threshold_pass=finite_arithmetic and kp_activity <= args.kp_max,
        finite_arithmetic=finite_arithmetic,
    )


def build_payload(args: argparse.Namespace) -> dict[str, Any]:
    casimirs = casimir_rows(args)
    weak_rows = weak_coupling_rows(args)
    kp = kp_diagnostic(args)
    return {
        "contract": "ym_balaban_constant_diagnostic",
        "claim_scope": CLAIM_SCOPE,
        "promotion_allowed": False,
        "theorem_promotion": {
            "balaban_transfer_promoted": False,
            "kp_theorem_promoted": False,
            "continuum_yang_mills_promoted": False,
            "mass_gap_promoted": False,
            "clay_yang_mills_promoted": False,
        },
        "casimir_formula": "C_F(SU(N)) = (N^2 - 1)/(2N)",
        "casimir_checks": [asdict(row) for row in casimirs],
        "b0_ceiling_contract": {
            "su2": "B0_SU2 <= sqrt(2)",
            "su3": "B0_SU3 <= sqrt(3) * B0_SU2",
            "b0_default": "sqrt(C_F) unless --b0-su2/--b0-su3 is supplied",
            "all_b0_ceilings_pass": all(row.b0_ceiling_pass for row in casimirs),
        },
        "weak_coupling_estimates": [asdict(row) for row in weak_rows],
        "kp_threshold_check": asdict(kp),
        "summary": {
            "all_numeric_arithmetic_finite": (
                all(math.isfinite(row.b0_value) for row in casimirs)
                and all(math.isfinite(row.g_squared) for row in weak_rows)
                and kp.finite_arithmetic
            ),
            "all_b0_ceilings_pass": all(row.b0_ceiling_pass for row in casimirs),
            "kp_threshold_pass": kp.kp_threshold_pass,
            "weak_coupling_rows_passing": sum(
                1 for row in weak_rows if row.weak_coupling_indicator_pass
            ),
            "weak_coupling_rows_total": len(weak_rows),
            "diagnostic_pass": (
                all(row.b0_ceiling_pass for row in casimirs)
                and kp.kp_threshold_pass
            ),
            "interpretation": (
                "finite_arithmetic_diagnostic_only_no_theorem_promotion"
            ),
        },
    }


def render_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# YM Balaban Option-B Constant Diagnostic",
        "",
        f"- claim_scope: `{payload['claim_scope']}`",
        f"- promotion_allowed: `{str(payload['promotion_allowed']).lower()}`",
        "- theorem_promotion: all false",
        "",
        "## Casimir and B0 Checks",
        "",
        "| group | C_F | B0 | ceiling | margin | pass |",
        "| --- | ---: | ---: | ---: | ---: | --- |",
    ]
    for row in payload["casimir_checks"]:
        lines.append(
            "| {group} | {casimir_value:.12g} ({casimir_fraction}) | "
            "{b0_value:.12g} | {b0_ceiling_value:.12g} | {b0_margin:.12g} | "
            "{b0_ceiling_pass} |".format(**row)
        )

    lines.extend(
        [
            "",
            "## Weak-Coupling Estimate",
            "",
            "| group | beta | g^2(beta) | g^2 < 1 |",
            "| --- | ---: | ---: | --- |",
        ]
    )
    for row in payload["weak_coupling_estimates"]:
        lines.append(
            "| {group} | {beta:.12g} | {g_squared:.12g} | "
            "{weak_coupling_indicator_pass} |".format(**row)
        )

    kp = payload["kp_threshold_check"]
    lines.extend(
        [
            "",
            "## KP Threshold",
            "",
            f"- formula: `{kp['formula']}`",
            f"- activity: `{kp['kp_activity']:.12g}`",
            f"- kp_max: `{kp['kp_max']:.12g}`",
            f"- margin: `{kp['kp_margin']:.12g}`",
            f"- m_power_threshold: `{kp['m_power_threshold']:.12g}`",
            f"- epsilon_product_threshold: `{kp['epsilon_product_threshold']:.12g}`",
            f"- pass: `{kp['kp_threshold_pass']}`",
            "",
            "## Summary",
            "",
        ]
    )
    for key, value in payload["summary"].items():
        lines.append(f"- {key}: `{value}`")
    lines.append("")
    return "\n".join(lines)


def main(argv: Sequence[str] | None = None) -> int:
    try:
        args = parse_args(argv)
        validate_args(args)
        payload = build_payload(args)
    except ValueError as exc:
        raise SystemExit(f"argument error: {exc}") from exc

    if args.format == "md":
        print(render_markdown(payload))
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
