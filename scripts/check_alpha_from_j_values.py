#!/usr/bin/env python3
"""Check simple alpha normalizations from CM j-value differences.

The calculation is intentionally narrow: it tests explicit arithmetic
normalizations of the three supplied CM j-values against the current carrier
alpha diagnostics.  A numerical near-hit is recorded as a heuristic match only;
it is not a derivation of alpha from modular geometry.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path


getcontext().prec = 50

REPO_ROOT = Path(__file__).resolve().parents[1]
REPORT_PATH = REPO_ROOT / "Docs" / "AlphaFromJNumericalCheck.md"

ALPHA_TARGETS = {
    "alpha1": Decimal("0.041240"),
    "alpha2": Decimal("0.085720"),
}
MATCH_TOLERANCE = Decimal("0.001000")

MASS_DIAGNOSTIC_INPUTS = {
    "mu_mev": Decimal("2.16"),
    "mc_mev": Decimal("1270"),
    "md_mev": Decimal("2.16"),
    "delta_md_mev": Decimal("2.5"),
    "ms_mev": Decimal("93.5"),
    "pdg_vus": Decimal("0.2243"),
    "pdg_vus_uncertainty": Decimal("0.0008"),
}

J_VALUES = {
    "j(i)": 1728,
    "j(rho)": 0,
    "j((1+i*sqrt(7))/2)": -3375,
}


@dataclass(frozen=True)
class Difference:
    label: str
    left: str
    right: str
    signed: int
    absolute: int


@dataclass(frozen=True)
class NormalizationResult:
    name: str
    source: str
    exact: str
    decimal: Decimal
    target_name: str
    target: Decimal
    abs_error: Decimal
    match: bool


@dataclass(frozen=True)
class CabibboMassDiagnostic:
    alpha1_from_mu_mc: Decimal
    alpha1_target_ratio: Decimal
    target_alpha1_over_mass_alpha1: Decimal
    md_over_ms: Decimal
    sqrt_md_over_ms: Decimal
    pdg_vus: Decimal
    pdg_vus_uncertainty: Decimal
    vus_abs_error: Decimal
    vus_relative_error: Decimal
    vus_sigma_offset: Decimal


def dec(frac: Fraction) -> Decimal:
    return Decimal(frac.numerator) / Decimal(frac.denominator)


def fmt_decimal(value: Decimal, digits: int = 12) -> str:
    quant = Decimal(1).scaleb(-digits)
    return str(value.quantize(quant))


def cm_differences() -> list[Difference]:
    labels = list(J_VALUES)
    out: list[Difference] = []
    for i, left in enumerate(labels):
        for right in labels[i + 1 :]:
            signed = J_VALUES[left] - J_VALUES[right]
            out.append(
                Difference(
                    label=f"{left} - {right}",
                    left=left,
                    right=right,
                    signed=signed,
                    absolute=abs(signed),
                )
            )
    return out


def normalization_fractions(diff: Difference) -> list[tuple[str, Fraction]]:
    d = diff.absolute
    return [
        ("1/|Delta j|", Fraction(1, d)),
        ("72/|Delta j|", Fraction(72, d)),
        ("144/|Delta j|", Fraction(144, d)),
        ("|Delta j|/1728^2", Fraction(d, 1728 * 1728)),
        ("|Delta j|/3375^2", Fraction(d, 3375 * 3375)),
        ("|Delta j|/5103^2", Fraction(d, 5103 * 5103)),
    ]


def sqrt_normalization(diff: Difference) -> tuple[str, Decimal, str]:
    d = Decimal(diff.absolute)
    value = Decimal(1) / d.sqrt()
    return ("1/sqrt(|Delta j|)", value, f"1/sqrt({diff.absolute})")


def compare(name: str, source: str, exact: str, value: Decimal) -> list[NormalizationResult]:
    rows: list[NormalizationResult] = []
    for target_name, target in ALPHA_TARGETS.items():
        abs_error = abs(value - target)
        rows.append(
            NormalizationResult(
                name=name,
                source=source,
                exact=exact,
                decimal=value,
                target_name=target_name,
                target=target,
                abs_error=abs_error,
                match=abs_error <= MATCH_TOLERANCE,
            )
        )
    return rows


def all_results(differences: list[Difference]) -> list[NormalizationResult]:
    rows: list[NormalizationResult] = []
    for diff in differences:
        for name, frac in normalization_fractions(diff):
            rows.extend(compare(name, diff.label, f"{frac.numerator}/{frac.denominator}", dec(frac)))
        sqrt_name, sqrt_value, sqrt_exact = sqrt_normalization(diff)
        rows.extend(compare(sqrt_name, diff.label, sqrt_exact, sqrt_value))
    return rows


def cabibbo_mass_diagnostic() -> CabibboMassDiagnostic:
    inputs = MASS_DIAGNOSTIC_INPUTS
    alpha1_from_mu_mc = (inputs["mu_mev"] / inputs["mc_mev"]).sqrt()
    md_over_ms = (inputs["md_mev"] + inputs["delta_md_mev"]) / inputs["ms_mev"]
    sqrt_md_over_ms = md_over_ms.sqrt()
    vus_abs_error = abs(sqrt_md_over_ms - inputs["pdg_vus"])
    return CabibboMassDiagnostic(
        alpha1_from_mu_mc=alpha1_from_mu_mc,
        alpha1_target_ratio=alpha1_from_mu_mc / ALPHA_TARGETS["alpha1"],
        target_alpha1_over_mass_alpha1=ALPHA_TARGETS["alpha1"] / alpha1_from_mu_mc,
        md_over_ms=md_over_ms,
        sqrt_md_over_ms=sqrt_md_over_ms,
        pdg_vus=inputs["pdg_vus"],
        pdg_vus_uncertainty=inputs["pdg_vus_uncertainty"],
        vus_abs_error=vus_abs_error,
        vus_relative_error=vus_abs_error / inputs["pdg_vus"],
        vus_sigma_offset=vus_abs_error / inputs["pdg_vus_uncertainty"],
    )


def markdown_report(differences: list[Difference], rows: list[NormalizationResult]) -> str:
    any_alpha1 = any(row.target_name == "alpha1" and row.match for row in rows)
    any_alpha2 = any(row.target_name == "alpha2" and row.match for row in rows)
    both_targets = any_alpha1 and any_alpha2
    alpha1_near_hit = Decimal(1) / Decimal(24)
    alpha1_abs_discrepancy = abs(alpha1_near_hit - ALPHA_TARGETS["alpha1"])
    alpha1_relative_discrepancy = alpha1_abs_discrepancy / alpha1_near_hit
    alpha1_correction_factor = ALPHA_TARGETS["alpha1"] / alpha1_near_hit
    cabibbo = cabibbo_mass_diagnostic()
    lines = [
        "# Alpha From CM j-Values Numerical Check",
        "",
        "Status: generated by `scripts/check_alpha_from_j_values.py`; numerical check only; non-promoting.",
        "",
        "## Inputs",
        "",
        "| CM point | j-value |",
        "|---|---:|",
    ]
    for label, value in J_VALUES.items():
        lines.append(f"| `{label}` | `{value}` |")

    lines.extend(
        [
            "",
            "Targets:",
            "",
            f"- `alpha1 = {ALPHA_TARGETS['alpha1']}`",
            f"- `alpha2 = {ALPHA_TARGETS['alpha2']}`",
            f"- match tolerance: `{MATCH_TOLERANCE}` absolute error",
            "",
            "## Exact Differences",
            "",
            "| Difference | signed | absolute |",
            "|---|---:|---:|",
        ]
    )
    for diff in differences:
        lines.append(f"| `{diff.label}` | `{diff.signed}` | `{diff.absolute}` |")

    lines.extend(
        [
            "",
            "## Normalization Tests",
            "",
            "| Source | normalization | exact | decimal | target | abs error | match |",
            "|---|---|---:|---:|---:|---:|---|",
        ]
    )
    for row in rows:
        lines.append(
            "| "
            f"`{row.source}` | `{row.name}` | `{row.exact}` | "
            f"`{fmt_decimal(row.decimal)}` | `{row.target_name}={row.target}` | "
            f"`{fmt_decimal(row.abs_error)}` | `{str(row.match).lower()}` |"
        )

    lines.extend(
        [
            "",
            "## Conclusion",
            "",
            f"- alpha1 heuristic match found: `{str(any_alpha1).lower()}`",
            f"- alpha2 heuristic match found: `{str(any_alpha2).lower()}`",
            f"- simultaneous alpha1/alpha2 derivation found: `{str(both_targets).lower()}`",
            "",
            "The only near-hit in this tested family is the simple modular-weight normalization "
            "`72 / |j(i)-j(rho)| = 1/24 = 0.041666666667`, which is within the configured "
            "absolute tolerance of the alpha1 diagnostic.  No tested normalization gives alpha2 "
            "within tolerance, and the alpha1 near-hit is not a formal bridge from modular "
            "geometry to the carrier alpha diagnostics.",
            "",
            "The factor `72 = 3 * 24` is modularly meaningful: `3` is the elliptic "
            "stabilizer order at `rho` in `PSL_2(Z)`, and `24` is the weight of the "
            "discriminant `Delta = eta^24`.  This records a real signal, but not a "
            "derivation.",
            "",
            "For the alpha1 near-hit, the discrepancy is",
            "",
            "```text",
            f"|1/24 - alpha1| = {fmt_decimal(alpha1_abs_discrepancy, 12)}",
            f"|1/24 - alpha1| / (1/24) = {fmt_decimal(alpha1_relative_discrepancy, 8)}",
            f"                               ~= {fmt_decimal(alpha1_relative_discrepancy * Decimal(100), 4)}%",
            "```",
            "",
            f"The correction factor `alpha1 / (1/24) = {fmt_decimal(alpha1_correction_factor, 5)}` "
            "is not identified as a Gamma/pi/algebraic constant in this check.  The next "
            "admissible check is a discriminant/Petersson normalization probe of the form",
            "",
            "```text",
            "alpha1 ?= c0 / |j(tau_p2)-j(tau_p3)| * |Delta(tau_p2)/Delta(tau_p3)|^(1/12)",
            "```",
            "",
            "where `c0` would have to be fixed by an independently defined carrier prime-lane "
            "metric normalization.",
            "",
            "## Cabibbo Mass-Ratio Diagnostic",
            "",
            "This separate diagnostic records the common first-generation mass-ratio path:",
            "",
            "```text",
            f"alpha1_mass = sqrt(2.16 / 1270) = {fmt_decimal(cabibbo.alpha1_from_mu_mc, 12)}",
            f"alpha1_mass / alpha1_target = {fmt_decimal(cabibbo.alpha1_target_ratio, 8)}",
            f"alpha1_target / alpha1_mass = {fmt_decimal(cabibbo.target_alpha1_over_mass_alpha1, 8)}",
            "",
            f"md/ms = (2.16 + 2.5) / 93.5 = {fmt_decimal(cabibbo.md_over_ms, 12)}",
            f"sqrt(md/ms) = {fmt_decimal(cabibbo.sqrt_md_over_ms, 12)}",
            f"PDG |Vus| comparison = {cabibbo.pdg_vus} +/- {cabibbo.pdg_vus_uncertainty}",
            f"|sqrt(md/ms) - |Vus|| = {fmt_decimal(cabibbo.vus_abs_error, 12)}",
            f"relative error = {fmt_decimal(cabibbo.vus_relative_error * Decimal(100), 4)}%",
            f"sigma offset against quoted PDG uncertainty = {fmt_decimal(cabibbo.vus_sigma_offset, 2)}",
            "```",
            "",
            "The PDG comparison value is the rounded 2024 kaon-sector Cabibbo-angle "
            "average `|Vus| = 0.22431(85)` from PDG Review of Particle Physics, "
            "`Vud, Vus, the Cabibbo Angle, and CKM Unitarity`, Eq. 67.18.",
            "",
            "The numerical proximity is useful as a diagnostic path: the alpha1 readback "
            "from `sqrt(2.16/1270)` is essentially the recorded `alpha1 = 0.041240`, "
            "and the shifted down/strange ratio gives a Cabibbo-scale value near the "
            "PDG `|Vus|` value.  It is not a derivation, because the additive "
            "`delta_md = 2.5 MeV` and the strange mass input `ms = 93.5 MeV` are not "
            "carrier-derived in this check.",
            "",
            "Therefore this check does not justify promoting an alpha or Cabibbo "
            "derivation.  It records one alpha1 near-hit, no alpha2 near-hit, no "
            "simultaneous CM j-value derivation, and a Cabibbo mass-ratio diagnostic "
            "whose required `delta_md` and `ms` inputs remain external.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    differences = cm_differences()
    rows = all_results(differences)
    cabibbo = cabibbo_mass_diagnostic()
    report = markdown_report(differences, rows)
    REPORT_PATH.write_text(report, encoding="utf-8")

    print("CM j-value differences:")
    for diff in differences:
        print(f"  {diff.label}: signed={diff.signed}, absolute={diff.absolute}")
    print(f"targets: alpha1={ALPHA_TARGETS['alpha1']}, alpha2={ALPHA_TARGETS['alpha2']}")
    print(
        "cabibbo mass diagnostic: "
        f"alpha1_mass={fmt_decimal(cabibbo.alpha1_from_mu_mc)}, "
        f"target_over_mass={fmt_decimal(cabibbo.target_alpha1_over_mass_alpha1, 8)}, "
        f"md_over_ms={fmt_decimal(cabibbo.md_over_ms)}, "
        f"sqrt_md_over_ms={fmt_decimal(cabibbo.sqrt_md_over_ms)}, "
        f"pdg_vus={cabibbo.pdg_vus}+/-{cabibbo.pdg_vus_uncertainty}, "
        f"sigma_offset={fmt_decimal(cabibbo.vus_sigma_offset, 2)}"
    )
    print(f"tolerance: {MATCH_TOLERANCE}")
    for row in rows:
        if row.match:
            print(
                "match: "
                f"target={row.target_name}, source={row.source}, "
                f"normalization={row.name}, exact={row.exact}, "
                f"decimal={fmt_decimal(row.decimal)}, "
                f"abs_error={fmt_decimal(row.abs_error)}"
            )
    print(f"report: {REPORT_PATH.relative_to(REPO_ROOT)}")


if __name__ == "__main__":
    main()
