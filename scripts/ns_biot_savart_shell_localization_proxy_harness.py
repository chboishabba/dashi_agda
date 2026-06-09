#!/usr/bin/env python3
"""NS A6.2 Biot-Savart shell-localization proxy harness.

This pure-stdlib diagnostic stress-tests the bookkeeping target:

    same-shell Biot-Savart strain multiplier
      -> localized diagonal shell model
      + off-shell Calderon-Zygmund tail decay
      + shell-gap separation

Good synthetic profiles have a same-shell multiplier mismatch and off-shell
tail that decay with the shell gap.  Bad profiles retain exactly one persistent
obstruction: a same-shell multiplier defect, a near-shell leakage plateau, a
far-tail plateau, or a low-regularity paraproduct shoulder.

This is diagnostic bookkeeping only.  It proves no Biot-Savart localization
estimate, no A6 theorem, no Navier-Stokes regularity theorem, and no Clay claim.
The emitted payload always has promotion=false.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/ns_biot_savart_shell_localization_proxy_harness.json")
EPS = 1.0e-12

COMPONENTS = (
    "same_shell_multiplier_mismatch",
    "near_shell_commutator_tail",
    "far_shell_cz_tail",
    "paraproduct_shoulder",
)


@dataclass(frozen=True)
class SweepRegime:
    name: str
    sweep: int
    tolerance: float
    bad_floor: float
    localization_gain: float
    smoothness_gain: float
    gap_decay: float
    stable_range: bool


@dataclass(frozen=True)
class ProfileSpec:
    name: str
    family: str
    description: str
    expected_good: bool
    base_scale: float
    same_shell_decay: float
    gap_decay_power: float
    smoothness_power: float
    localization_power: float
    blocker: str | None = None


@dataclass(frozen=True)
class ShellGapRow:
    regime: str
    sweep: int
    profile: str
    family: str
    level: int
    shell_gap: int
    input_shell: int
    output_shell: int
    tolerance: float
    bad_floor: float
    localization_gain: float
    smoothness_gain: float
    gap_decay: float
    component_errors: dict[str, float]
    localization_error: float
    expected_decay_envelope: float
    within_tolerance: bool
    blocking_component: str | None


@dataclass(frozen=True)
class ProfileSummary:
    profile: str
    family: str
    expected_good: bool
    blocker: str | None
    row_count: int
    stable_row_count: int
    max_stable_error: float
    final_stable_error: float
    min_stable_error: float
    worst_stable_regime: str
    worst_stable_gap: int
    stable_pass: bool
    classification: str
    checks: dict[str, bool]


@dataclass(frozen=True)
class ComponentSummary:
    component: str
    max_good_stable_error: float
    min_bad_blocker_stable_error: float
    max_bad_non_blocker_stable_error: float
    blocker_visible_rows: int
    separation_margin: float
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--levels", type=int, default=12)
    parser.add_argument("--sweeps", type=int, default=8)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.levels < 6:
        raise ValueError("--levels must be at least 6")
    if args.sweeps < 5:
        raise ValueError("--sweeps must be at least 5")


def sweep_regimes(count: int) -> list[SweepRegime]:
    center = (count - 1) / 2.0
    regimes: list[SweepRegime] = []
    for sweep in range(count):
        offset = (sweep - center) / max(center, 1.0)
        tolerance = 0.0105 + 0.0014 * math.cos(0.71 * sweep + 0.2)
        bad_floor = 0.038 + 0.0045 * math.sin(0.59 * sweep + 0.4)
        localization_gain = 1.18 + 0.16 * math.cos(0.43 * sweep)
        smoothness_gain = 1.15 + 0.18 * math.sin(0.51 * sweep + 0.3)
        gap_decay = 0.58 + 0.08 * offset
        stable = (
            0.0085 <= tolerance <= 0.0122
            and 0.033 <= bad_floor <= 0.044
            and 1.00 <= localization_gain <= 1.38
            and 1.00 <= smoothness_gain <= 1.36
            and 0.48 <= gap_decay <= 0.69
        )
        regimes.append(
            SweepRegime(
                name=f"sweep_{sweep:02d}",
                sweep=sweep,
                tolerance=tolerance,
                bad_floor=bad_floor,
                localization_gain=localization_gain,
                smoothness_gain=smoothness_gain,
                gap_decay=gap_decay,
                stable_range=stable,
            )
        )
    return regimes


def profile_specs() -> list[ProfileSpec]:
    good = [
        ProfileSpec(
            name="good_smooth_same_shell_localized",
            family="good",
            description="Smooth diagonal symbol with rapidly decaying shell-gap tails.",
            expected_good=True,
            base_scale=0.0061,
            same_shell_decay=0.61,
            gap_decay_power=1.62,
            smoothness_power=1.28,
            localization_power=1.22,
        ),
        ProfileSpec(
            name="good_cz_tail_absorbed",
            family="good",
            description="Off-shell Calderon-Zygmund tail is strongly gap-decaying.",
            expected_good=True,
            base_scale=0.0058,
            same_shell_decay=0.64,
            gap_decay_power=1.86,
            smoothness_power=1.10,
            localization_power=1.38,
        ),
        ProfileSpec(
            name="good_paraproduct_shoulder_absorbed",
            family="good",
            description="Near-diagonal paraproduct shoulder decays after smooth localization.",
            expected_good=True,
            base_scale=0.0055,
            same_shell_decay=0.66,
            gap_decay_power=1.48,
            smoothness_power=1.52,
            localization_power=1.15,
        ),
    ]
    bad = [
        ProfileSpec(
            name=f"bad_{component}_blocker",
            family="bad_blocker",
            description=f"Persistent {component.replace('_', ' ')} obstruction.",
            expected_good=False,
            base_scale=0.0048,
            same_shell_decay=0.70,
            gap_decay_power=1.10,
            smoothness_power=1.05,
            localization_power=1.06,
            blocker=component,
        )
        for component in COMPONENTS
    ]
    return good + bad


def component_weight(component: str) -> float:
    return 0.86 + 0.085 * (COMPONENTS.index(component) + 1)


def deterministic_ripple(
    *, component: str, level: int, gap: int, regime: SweepRegime, spec: ProfileSpec
) -> float:
    component_index = COMPONENTS.index(component) + 1
    family_phase = 0.19 if spec.expected_good else 0.47
    phase = 0.41 * level + 0.67 * gap + 0.31 * regime.sweep + component_index * 0.23
    return 1.0 + 0.028 * math.sin(phase + family_phase)


def base_decay(
    *, component: str, spec: ProfileSpec, regime: SweepRegime, level: int, gap: int
) -> float:
    level_decay = spec.same_shell_decay**level
    gap_decay = math.exp(-spec.gap_decay_power * regime.gap_decay * gap)
    polynomial = (level + 1.0) ** -0.92
    smooth = regime.smoothness_gain ** spec.smoothness_power
    localized = regime.localization_gain ** spec.localization_power

    if component == "same_shell_multiplier_mismatch":
        component_scale = polynomial * level_decay / smooth
    elif component == "near_shell_commutator_tail":
        component_scale = gap_decay / math.sqrt(gap + 1.0) / localized
    elif component == "far_shell_cz_tail":
        component_scale = gap_decay * gap_decay / max(localized * smooth, EPS)
    elif component == "paraproduct_shoulder":
        shoulder = math.exp(-0.5 * spec.gap_decay_power * regime.gap_decay * gap)
        component_scale = shoulder * polynomial / math.sqrt(max(smooth, EPS))
    else:
        raise KeyError(component)

    return (
        spec.base_scale
        * component_weight(component)
        * component_scale
        * deterministic_ripple(component=component, level=level, gap=gap, regime=regime, spec=spec)
    )


def component_errors(
    *, spec: ProfileSpec, regime: SweepRegime, level: int, gap: int
) -> dict[str, float]:
    errors = {
        component: max(0.0, base_decay(component=component, spec=spec, regime=regime, level=level, gap=gap))
        for component in COMPONENTS
    }
    if spec.blocker is not None:
        blocker_index = COMPONENTS.index(spec.blocker) + 1
        floor = regime.bad_floor * (1.0 + 0.026 * math.sin(0.37 * level + 0.71 * gap))
        floor += 0.0045 / math.sqrt(level + blocker_index + 1.0)
        if spec.blocker == "same_shell_multiplier_mismatch":
            floor *= 1.0 + 0.07 / max(regime.smoothness_gain, EPS)
        elif spec.blocker == "near_shell_commutator_tail":
            floor *= 1.0 + 0.05 / max(regime.localization_gain, EPS)
        elif spec.blocker == "far_shell_cz_tail":
            floor *= 1.0 + 0.04 / max(1.0 - regime.gap_decay + 0.6, EPS)
        elif spec.blocker == "paraproduct_shoulder":
            floor *= 1.0 + 0.06 / max(math.sqrt(regime.smoothness_gain), EPS)
        errors[spec.blocker] = max(errors[spec.blocker], floor)
    return errors


def localization_error(errors: dict[str, float]) -> float:
    # A6.2 is a max-budget theorem: any unresolved component can block the
    # same-shell localization estimate, while good components should all decay.
    return max(abs(value) for value in errors.values())


def expected_decay_envelope(spec: ProfileSpec, regime: SweepRegime, level: int, gap: int) -> float:
    shell_part = spec.base_scale * (spec.same_shell_decay**level) / ((level + 1.0) ** 0.92)
    gap_part = spec.base_scale * math.exp(-spec.gap_decay_power * regime.gap_decay * gap)
    return 1.8 * max(shell_part, gap_part)


def build_rows(args: argparse.Namespace) -> tuple[list[ShellGapRow], list[SweepRegime]]:
    validate_args(args)
    regimes = sweep_regimes(args.sweeps)
    rows: list[ShellGapRow] = []
    for regime in regimes:
        for spec in profile_specs():
            for level in range(args.levels):
                for gap in range(args.levels):
                    input_shell = level
                    output_shell = level + gap
                    errors = component_errors(spec=spec, regime=regime, level=level, gap=gap)
                    combined = localization_error(errors)
                    rows.append(
                        ShellGapRow(
                            regime=regime.name,
                            sweep=regime.sweep,
                            profile=spec.name,
                            family=spec.family,
                            level=level,
                            shell_gap=gap,
                            input_shell=input_shell,
                            output_shell=output_shell,
                            tolerance=regime.tolerance,
                            bad_floor=regime.bad_floor,
                            localization_gain=regime.localization_gain,
                            smoothness_gain=regime.smoothness_gain,
                            gap_decay=regime.gap_decay,
                            component_errors=errors,
                            localization_error=combined,
                            expected_decay_envelope=expected_decay_envelope(spec, regime, level, gap),
                            within_tolerance=combined <= regime.tolerance,
                            blocking_component=max(errors, key=errors.get)
                            if combined > regime.tolerance
                            else None,
                        )
                    )
    return rows, regimes


def stable_regime_names(regimes: Sequence[SweepRegime]) -> set[str]:
    return {regime.name for regime in regimes if regime.stable_range}


def summarize_profiles(
    rows: Sequence[ShellGapRow], regimes: Sequence[SweepRegime]
) -> list[ProfileSummary]:
    specs = {spec.name: spec for spec in profile_specs()}
    stable_names = stable_regime_names(regimes)
    if not stable_names:
        raise ValueError("sweep produced no stable regimes")

    summaries: list[ProfileSummary] = []
    for name in sorted(specs):
        spec = specs[name]
        profile_rows = [row for row in rows if row.profile == name]
        stable_rows = [row for row in profile_rows if row.regime in stable_names]
        if not stable_rows:
            raise ValueError(f"profile {name} has no stable rows")
        worst = max(stable_rows, key=lambda row: row.localization_error)
        final_gap = max(row.shell_gap for row in stable_rows)
        final_level = max(row.level for row in stable_rows)
        final_rows = [
            row
            for row in stable_rows
            if row.shell_gap == final_gap and row.level == final_level
        ]
        final_error = max(row.localization_error for row in final_rows)
        stable_pass = all(row.within_tolerance for row in stable_rows)
        expected_observed = stable_pass if spec.expected_good else not stable_pass
        envelope_ok = all(
            row.localization_error <= max(row.tolerance, row.expected_decay_envelope * 2.75)
            for row in stable_rows
            if spec.expected_good
        )
        blocker_dominates = True
        if spec.blocker is not None:
            blocker_dominates = all(
                row.component_errors[spec.blocker]
                >= max(
                    value
                    for component, value in row.component_errors.items()
                    if component != spec.blocker
                )
                for row in stable_rows
            )

        if spec.expected_good and stable_pass:
            classification = "good_shell_localization_decay"
        elif (not spec.expected_good) and not stable_pass and blocker_dominates:
            classification = "bad_shell_localization_obstruction_visible"
        else:
            classification = "unexpected_or_borderline_profile"

        summaries.append(
            ProfileSummary(
                profile=name,
                family=spec.family,
                expected_good=spec.expected_good,
                blocker=spec.blocker,
                row_count=len(profile_rows),
                stable_row_count=len(stable_rows),
                max_stable_error=worst.localization_error,
                final_stable_error=final_error,
                min_stable_error=min(row.localization_error for row in stable_rows),
                worst_stable_regime=worst.regime,
                worst_stable_gap=worst.shell_gap,
                stable_pass=stable_pass,
                classification=classification,
                checks={
                    "expected_stable_outcome_observed": expected_observed,
                    "good_errors_within_stable_tolerance": stable_pass if spec.expected_good else True,
                    "good_decay_envelope_respected": envelope_ok if spec.expected_good else True,
                    "bad_profile_fails_stable_tolerance": (not stable_pass) if not spec.expected_good else True,
                    "declared_blocker_dominates": blocker_dominates,
                    "finite_nonnegative_errors": all(
                        math.isfinite(row.localization_error)
                        and row.localization_error >= 0.0
                        and all(
                            math.isfinite(value) and value >= 0.0
                            for value in row.component_errors.values()
                        )
                        for row in profile_rows
                    ),
                },
            )
        )
    return summaries


def summarize_components(
    rows: Sequence[ShellGapRow], regimes: Sequence[SweepRegime]
) -> list[ComponentSummary]:
    stable_names = stable_regime_names(regimes)
    stable_rows = [row for row in rows if row.regime in stable_names]
    summaries: list[ComponentSummary] = []
    for component in COMPONENTS:
        good_values = [
            row.component_errors[component]
            for row in stable_rows
            if row.family == "good"
        ]
        blocker_values = [
            row.component_errors[component]
            for row in stable_rows
            if row.profile == f"bad_{component}_blocker"
        ]
        non_blocker_bad_values = [
            row.component_errors[component]
            for row in stable_rows
            if row.family == "bad_blocker"
            and row.profile != f"bad_{component}_blocker"
        ]
        max_good = max(good_values)
        min_blocker = min(blocker_values)
        max_non_blocker_bad = max(non_blocker_bad_values)
        blocker_visible = [
            row
            for row in stable_rows
            if row.profile == f"bad_{component}_blocker"
            and row.component_errors[component] > row.tolerance
        ]
        summaries.append(
            ComponentSummary(
                component=component,
                max_good_stable_error=max_good,
                min_bad_blocker_stable_error=min_blocker,
                max_bad_non_blocker_stable_error=max_non_blocker_bad,
                blocker_visible_rows=len(blocker_visible),
                separation_margin=min_blocker - max(max_good, max_non_blocker_bad),
                checks={
                    "good_component_below_stable_tolerance": all(
                        row.component_errors[component] <= row.tolerance
                        for row in stable_rows
                        if row.family == "good"
                    ),
                    "bad_blocker_above_stable_floor": all(
                        row.component_errors[component] >= row.bad_floor
                        for row in stable_rows
                        if row.profile == f"bad_{component}_blocker"
                    ),
                    "blocker_separates_from_non_blockers": min_blocker > max_non_blocker_bad,
                    "blocker_visible_rows_present": bool(blocker_visible),
                    "finite_nonnegative_values": all(
                        math.isfinite(value) and value >= 0.0
                        for value in good_values + blocker_values + non_blocker_bad_values
                    ),
                },
            )
        )
    return summaries


def compact_rows(rows: Sequence[ShellGapRow]) -> list[dict[str, object]]:
    return [
        {
            "regime": row.regime,
            "sweep": row.sweep,
            "profile": row.profile,
            "family": row.family,
            "level": row.level,
            "shell_gap": row.shell_gap,
            "input_shell": row.input_shell,
            "output_shell": row.output_shell,
            "localization_error": row.localization_error,
            "expected_decay_envelope": row.expected_decay_envelope,
            "tolerance": row.tolerance,
            "bad_floor": row.bad_floor,
            "blocking_component": row.blocking_component,
            "within_tolerance": row.within_tolerance,
            "component_errors": row.component_errors,
        }
        for row in rows
    ]


def build_payload(args: argparse.Namespace) -> dict[str, object]:
    rows, regimes = build_rows(args)
    profile_summaries = summarize_profiles(rows, regimes)
    component_summaries = summarize_components(rows, regimes)
    stable = [regime for regime in regimes if regime.stable_range]
    good_profiles = [summary for summary in profile_summaries if summary.expected_good]
    bad_profiles = [summary for summary in profile_summaries if not summary.expected_good]

    validation_flags = {
        "stable_regimes_present": len(stable) >= max(3, args.sweeps // 2),
        "good_profiles_stable_below_tolerance": all(
            summary.stable_pass for summary in good_profiles
        ),
        "bad_profiles_stable_obstructed": all(
            not summary.stable_pass for summary in bad_profiles
        ),
        "expected_profile_outcomes_observed": all(
            summary.checks["expected_stable_outcome_observed"]
            for summary in profile_summaries
        ),
        "component_separation_checks_pass": all(
            all(summary.checks.values()) for summary in component_summaries
        ),
        "profile_local_checks_pass": all(
            all(summary.checks.values()) for summary in profile_summaries
        ),
        "diagnostic_only": True,
        "promotion_false": True,
    }
    ok = all(validation_flags.values())

    return {
        "harness": "ns_biot_savart_shell_localization_proxy",
        "diagnostic_only": True,
        "promotion": False,
        "clay_promoted": False,
        "ok": ok,
        "control": {
            "O": "Worker B NS A6.2 Biot-Savart shell-localization proxy lane.",
            "R": "Model same-shell multiplier localization against off-shell decay over shell gaps.",
            "C": "scripts/ns_biot_savart_shell_localization_proxy_harness.py",
            "S": "Synthetic shell-gap metrics only; no Calderon-Zygmund kernel proof is established.",
            "L": "sweep regimes -> shell-gap rows -> good/bad profile separation -> fail-closed JSON.",
            "P": "Good profiles must decay below tolerance; bad profiles must expose persistent blocker components.",
            "G": "promotion=false always; diagnostics cannot certify NS A6.2 or Clay progress.",
            "F": "Still missing the real Biot-Savart shell localization theorem for Navier-Stokes fields.",
        },
        "parameters": {
            "levels": args.levels,
            "sweeps": args.sweeps,
            "components": list(COMPONENTS),
        },
        "summary": {
            "row_count": len(rows),
            "stable_sweep_count": len(stable),
            "profile_count": len(profile_summaries),
            "good_profile_count": len(good_profiles),
            "bad_profile_count": len(bad_profiles),
            "component_count": len(component_summaries),
            "max_good_stable_error": max(
                summary.max_stable_error for summary in good_profiles
            ),
            "min_bad_stable_error": min(
                summary.min_stable_error for summary in bad_profiles
            ),
            "min_component_separation_margin": min(
                summary.separation_margin for summary in component_summaries
            ),
            "ok": ok,
        },
        "validation_flags": validation_flags,
        "regimes": [asdict(regime) for regime in regimes],
        "profile_summaries": [asdict(summary) for summary in profile_summaries],
        "component_summaries": [asdict(summary) for summary in component_summaries],
        "rows": compact_rows(rows),
        "interpretation": {
            "supports": (
                "Synthetic same-shell localization profiles can be separated from persistent "
                "multiplier, near-shell, far-tail, and paraproduct obstructions over shell gaps."
            ),
            "rejects": (
                "Any profile with a persistent blocker is rejected even if the other components decay."
            ),
            "residual_gap": (
                "A real A6.2 proof still needs Calderon-Zygmund/Biot-Savart kernel localization "
                "for Littlewood-Paley shells of Navier-Stokes fields."
            ),
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    payload = build_payload(args)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        summary = payload["summary"]
        print("NS Biot-Savart shell localization proxy harness")
        print(f"wrote: {args.json_output}")
        print(
            "ok={ok} rows={rows} stable_sweeps={stable} good_max={good:.6g} "
            "bad_min={bad:.6g} margin={margin:.6g} promotion=false".format(
                ok=str(payload["ok"]).lower(),
                rows=summary["row_count"],
                stable=summary["stable_sweep_count"],
                good=summary["max_good_stable_error"],
                bad=summary["min_bad_stable_error"],
                margin=summary["min_component_separation_margin"],
            )
        )
    return 0 if payload["ok"] and not payload["promotion"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
