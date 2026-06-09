#!/usr/bin/env python3
"""NS A4 LRT physical-to-Fourier output coupling proxy harness.

This deterministic pure-stdlib diagnostic models the A4 proof target:

    Lei-Ren-Tian physical vorticity angular richness
      + localized Whitney/frame coherence
      + stationarity-window control
      -> Fourier triadic output directions hit great-circle frames.

Good synthetic profiles satisfy all component checks.  Bad profiles expose
one concrete obstruction: physical-rich but Fourier-collapsed support, missing
Whitney overlap, frame incoherence, or a nonstationary scale window.

This is diagnostic bookkeeping only.  It proves no Lei-Ren-Tian transfer
estimate, no Fourier/physical angular coupling theorem, no Navier-Stokes
regularity theorem, and no Clay claim.  The emitted payload always has
promotion=false.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/ns_lrt_fourier_output_coupling_proxy_harness.json")
EPS = 1.0e-12

COMPONENTS = (
    "lrt_angular_richness",
    "localized_frame_coherence",
    "fourier_output_spread",
    "whitney_overlap",
    "angular_collapse_penalty",
    "stationarity_window",
)


@dataclass(frozen=True)
class Parameters:
    frames: int
    sweeps: int
    richness_floor: float
    coherence_floor: float
    spread_floor: float
    overlap_floor: float
    stationarity_floor: float
    collapse_ceiling: float


@dataclass(frozen=True)
class SweepRegime:
    name: str
    sweep: int
    angular_resolution: float
    localization_radius: float
    whitney_thickness: float
    stationarity_tolerance: float
    stable_range: bool


@dataclass(frozen=True)
class ProfileSpec:
    name: str
    family: str
    description: str
    expected_good: bool
    richness_base: float
    coherence_base: float
    spread_base: float
    overlap_base: float
    collapse_base: float
    stationarity_base: float
    blocker: str | None = None


@dataclass(frozen=True)
class CouplingRow:
    regime: str
    sweep: int
    frame: int
    normal_phase: float
    profile: str
    family: str
    expected_good: bool
    blocker: str | None
    lrt_angular_richness: float
    localized_frame_coherence: float
    fourier_output_spread: float
    whitney_overlap: float
    angular_collapse_penalty: float
    stationarity_window: float
    coupling_margin: float
    passed_proxy_checks: bool
    failure_reasons: list[str]


@dataclass(frozen=True)
class ProfileSummary:
    profile: str
    family: str
    expected_good: bool
    blocker: str | None
    row_count: int
    rows_passing: int
    rows_failing: int
    min_lrt_richness: float
    min_frame_coherence: float
    min_fourier_spread: float
    min_whitney_overlap: float
    max_collapse_penalty: float
    min_stationarity_window: float
    min_coupling_margin: float
    classification_matches_expectation: bool
    failure_reasons: list[str]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frames", type=int, default=14)
    parser.add_argument("--sweeps", type=int, default=8)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.frames < 8:
        raise ValueError("--frames must be at least 8")
    if args.sweeps < 5:
        raise ValueError("--sweeps must be at least 5")


def clamp01(value: float) -> float:
    return max(0.0, min(1.0, value))


def parameters(args: argparse.Namespace) -> Parameters:
    return Parameters(
        frames=args.frames,
        sweeps=args.sweeps,
        richness_floor=0.62,
        coherence_floor=0.58,
        spread_floor=0.56,
        overlap_floor=0.55,
        stationarity_floor=0.57,
        collapse_ceiling=0.34,
    )


def sweep_regimes(count: int) -> list[SweepRegime]:
    regimes: list[SweepRegime] = []
    center = (count - 1) / 2.0
    for sweep in range(count):
        offset = (sweep - center) / max(center, 1.0)
        angular_resolution = 0.045 + 0.006 * math.cos(0.67 * sweep + 0.2)
        localization_radius = 0.118 + 0.012 * math.sin(0.41 * sweep + 0.5)
        whitney_thickness = 0.082 + 0.010 * math.cos(0.53 * sweep - 0.1)
        stationarity_tolerance = 0.033 + 0.005 * (1.0 + offset) / 2.0
        stable_range = (
            0.038 <= angular_resolution <= 0.052
            and 0.104 <= localization_radius <= 0.132
            and 0.071 <= whitney_thickness <= 0.093
            and 0.032 <= stationarity_tolerance <= 0.039
        )
        regimes.append(
            SweepRegime(
                name=f"sweep_{sweep:02d}",
                sweep=sweep,
                angular_resolution=angular_resolution,
                localization_radius=localization_radius,
                whitney_thickness=whitney_thickness,
                stationarity_tolerance=stationarity_tolerance,
                stable_range=stable_range,
            )
        )
    return regimes


def profile_specs() -> list[ProfileSpec]:
    return [
        ProfileSpec(
            name="good_balanced_lrt_fourier_coupling",
            family="good",
            description="Physical LRT richness couples to broad Fourier output support.",
            expected_good=True,
            richness_base=0.75,
            coherence_base=0.72,
            spread_base=0.70,
            overlap_base=0.69,
            collapse_base=0.18,
            stationarity_base=0.73,
        ),
        ProfileSpec(
            name="good_whitney_dense_stationary_frames",
            family="good",
            description="Dense Whitney overlaps and stationary frames keep outputs rich.",
            expected_good=True,
            richness_base=0.72,
            coherence_base=0.70,
            spread_base=0.68,
            overlap_base=0.74,
            collapse_base=0.20,
            stationarity_base=0.76,
        ),
        ProfileSpec(
            name="good_localized_frame_transfer",
            family="good",
            description="Localized frame coherence transfers angular richness with slack.",
            expected_good=True,
            richness_base=0.78,
            coherence_base=0.75,
            spread_base=0.66,
            overlap_base=0.67,
            collapse_base=0.17,
            stationarity_base=0.70,
        ),
        ProfileSpec(
            name="bad_physical_rich_fourier_collapsed",
            family="bad_blocker",
            description="LRT richness is present, but Fourier output directions collapse.",
            expected_good=False,
            richness_base=0.76,
            coherence_base=0.70,
            spread_base=0.31,
            overlap_base=0.67,
            collapse_base=0.58,
            stationarity_base=0.72,
            blocker="physical-rich-but-Fourier-collapsed",
        ),
        ProfileSpec(
            name="bad_no_whitney_overlap",
            family="bad_blocker",
            description="Localized frames fail to overlap the Whitney great-circle cover.",
            expected_good=False,
            richness_base=0.74,
            coherence_base=0.69,
            spread_base=0.66,
            overlap_base=0.29,
            collapse_base=0.22,
            stationarity_base=0.71,
            blocker="no-Whitney-overlap",
        ),
        ProfileSpec(
            name="bad_frame_incoherent",
            family="bad_blocker",
            description="Physical and Fourier frames are incoherent despite broad support.",
            expected_good=False,
            richness_base=0.73,
            coherence_base=0.30,
            spread_base=0.67,
            overlap_base=0.66,
            collapse_base=0.24,
            stationarity_base=0.70,
            blocker="frame-incoherent",
        ),
        ProfileSpec(
            name="bad_nonstationary_window",
            family="bad_blocker",
            description="Angular transfer drifts across the Abel stationarity window.",
            expected_good=False,
            richness_base=0.75,
            coherence_base=0.70,
            spread_base=0.66,
            overlap_base=0.65,
            collapse_base=0.23,
            stationarity_base=0.28,
            blocker="nonstationary-window",
        ),
    ]


def deterministic_ripple(*, frame: int, regime: SweepRegime, phase: float) -> float:
    return 0.018 * math.sin(0.71 * frame + 0.43 * regime.sweep + phase)


def compute_components(
    *, spec: ProfileSpec, regime: SweepRegime, frame: int, params: Parameters
) -> dict[str, float]:
    phase = 2.0 * math.pi * frame / float(params.frames)
    angular_resolution_penalty = 0.42 * regime.angular_resolution
    localization_bonus = 0.22 * regime.localization_radius
    whitney_bonus = 0.33 * regime.whitney_thickness
    stationarity_penalty = 1.25 * regime.stationarity_tolerance

    richness = (
        spec.richness_base
        - angular_resolution_penalty
        + deterministic_ripple(frame=frame, regime=regime, phase=0.10)
    )
    coherence = (
        spec.coherence_base
        + localization_bonus
        + deterministic_ripple(frame=frame, regime=regime, phase=0.95)
    )
    spread = (
        spec.spread_base
        + 0.18 * richness
        + 0.08 * math.cos(phase)
        - 0.12 * spec.collapse_base
        + deterministic_ripple(frame=frame, regime=regime, phase=1.70)
    )
    overlap = (
        spec.overlap_base
        + whitney_bonus
        - 0.05 * abs(math.sin(phase))
        + deterministic_ripple(frame=frame, regime=regime, phase=2.30)
    )
    collapse = (
        spec.collapse_base
        + 0.22 * max(0.0, params.spread_floor - spread)
        + 0.07 * abs(math.sin(2.0 * phase))
        + deterministic_ripple(frame=frame, regime=regime, phase=3.10)
    )
    stationarity = (
        spec.stationarity_base
        - stationarity_penalty
        + 0.06 * math.cos(phase + 0.2 * regime.sweep)
        + deterministic_ripple(frame=frame, regime=regime, phase=4.00)
    )

    return {
        "lrt_angular_richness": clamp01(richness),
        "localized_frame_coherence": clamp01(coherence),
        "fourier_output_spread": clamp01(spread),
        "whitney_overlap": clamp01(overlap),
        "angular_collapse_penalty": clamp01(collapse),
        "stationarity_window": clamp01(stationarity),
    }


def failure_reasons(components: dict[str, float], params: Parameters) -> list[str]:
    reasons: list[str] = []
    if components["lrt_angular_richness"] < params.richness_floor:
        reasons.append("lrt_angular_richness_below_floor")
    if components["localized_frame_coherence"] < params.coherence_floor:
        reasons.append("localized_frame_coherence_below_floor")
    if components["fourier_output_spread"] < params.spread_floor:
        reasons.append("fourier_output_spread_below_floor")
    if components["whitney_overlap"] < params.overlap_floor:
        reasons.append("whitney_overlap_below_floor")
    if components["angular_collapse_penalty"] > params.collapse_ceiling:
        reasons.append("angular_collapse_penalty_above_ceiling")
    if components["stationarity_window"] < params.stationarity_floor:
        reasons.append("stationarity_window_below_floor")
    return reasons


def coupling_margin(components: dict[str, float], params: Parameters) -> float:
    margins = [
        components["lrt_angular_richness"] - params.richness_floor,
        components["localized_frame_coherence"] - params.coherence_floor,
        components["fourier_output_spread"] - params.spread_floor,
        components["whitney_overlap"] - params.overlap_floor,
        params.collapse_ceiling - components["angular_collapse_penalty"],
        components["stationarity_window"] - params.stationarity_floor,
    ]
    return min(margins)


def build_rows(args: argparse.Namespace) -> tuple[list[CouplingRow], list[SweepRegime], Parameters]:
    validate_args(args)
    params = parameters(args)
    regimes = sweep_regimes(args.sweeps)
    rows: list[CouplingRow] = []
    for regime in regimes:
        for spec in profile_specs():
            for frame in range(args.frames):
                components = compute_components(
                    spec=spec, regime=regime, frame=frame, params=params
                )
                reasons = failure_reasons(components, params)
                rows.append(
                    CouplingRow(
                        regime=regime.name,
                        sweep=regime.sweep,
                        frame=frame,
                        normal_phase=2.0 * math.pi * frame / float(args.frames),
                        profile=spec.name,
                        family=spec.family,
                        expected_good=spec.expected_good,
                        blocker=spec.blocker,
                        lrt_angular_richness=components["lrt_angular_richness"],
                        localized_frame_coherence=components["localized_frame_coherence"],
                        fourier_output_spread=components["fourier_output_spread"],
                        whitney_overlap=components["whitney_overlap"],
                        angular_collapse_penalty=components["angular_collapse_penalty"],
                        stationarity_window=components["stationarity_window"],
                        coupling_margin=coupling_margin(components, params),
                        passed_proxy_checks=not reasons,
                        failure_reasons=reasons,
                    )
                )
    return rows, regimes, params


def summarize_profiles(rows: Sequence[CouplingRow]) -> list[ProfileSummary]:
    summaries: list[ProfileSummary] = []
    for spec in profile_specs():
        profile_rows = [row for row in rows if row.profile == spec.name]
        if not profile_rows:
            continue
        rows_passing = sum(1 for row in profile_rows if row.passed_proxy_checks)
        reasons = sorted({reason for row in profile_rows for reason in row.failure_reasons})
        classification_matches = (
            rows_passing == len(profile_rows)
            if spec.expected_good
            else rows_passing == 0 and bool(reasons)
        )
        summaries.append(
            ProfileSummary(
                profile=spec.name,
                family=spec.family,
                expected_good=spec.expected_good,
                blocker=spec.blocker,
                row_count=len(profile_rows),
                rows_passing=rows_passing,
                rows_failing=len(profile_rows) - rows_passing,
                min_lrt_richness=min(row.lrt_angular_richness for row in profile_rows),
                min_frame_coherence=min(row.localized_frame_coherence for row in profile_rows),
                min_fourier_spread=min(row.fourier_output_spread for row in profile_rows),
                min_whitney_overlap=min(row.whitney_overlap for row in profile_rows),
                max_collapse_penalty=max(row.angular_collapse_penalty for row in profile_rows),
                min_stationarity_window=min(row.stationarity_window for row in profile_rows),
                min_coupling_margin=min(row.coupling_margin for row in profile_rows),
                classification_matches_expectation=classification_matches,
                failure_reasons=reasons,
            )
        )
    return summaries


def compact_rows(rows: Sequence[CouplingRow]) -> list[dict[str, object]]:
    return [
        {
            "regime": row.regime,
            "frame": row.frame,
            "profile": row.profile,
            "passed": row.passed_proxy_checks,
            "margin": round(row.coupling_margin, 6),
            "lrt": round(row.lrt_angular_richness, 6),
            "frame_coherence": round(row.localized_frame_coherence, 6),
            "spread": round(row.fourier_output_spread, 6),
            "whitney": round(row.whitney_overlap, 6),
            "collapse": round(row.angular_collapse_penalty, 6),
            "stationarity": round(row.stationarity_window, 6),
            "failures": row.failure_reasons,
        }
        for row in rows
    ]


def build_payload(args: argparse.Namespace) -> dict[str, object]:
    rows, regimes, params = build_rows(args)
    summaries = summarize_profiles(rows)
    good_summaries = [summary for summary in summaries if summary.expected_good]
    bad_summaries = [summary for summary in summaries if not summary.expected_good]
    stable_regimes = [regime for regime in regimes if regime.stable_range]

    validation_flags = {
        "stable_regimes_present": len(stable_regimes) >= max(3, args.sweeps // 2),
        "good_profiles_pass_all_rows": all(
            summary.rows_passing == summary.row_count for summary in good_summaries
        ),
        "bad_profiles_fail_all_rows": all(
            summary.rows_failing == summary.row_count for summary in bad_summaries
        ),
        "physical_rich_fourier_collapse_visible": any(
            summary.blocker == "physical-rich-but-Fourier-collapsed"
            and "fourier_output_spread_below_floor" in summary.failure_reasons
            and "angular_collapse_penalty_above_ceiling" in summary.failure_reasons
            for summary in bad_summaries
        ),
        "whitney_overlap_blocker_visible": any(
            summary.blocker == "no-Whitney-overlap"
            and "whitney_overlap_below_floor" in summary.failure_reasons
            for summary in bad_summaries
        ),
        "frame_incoherence_blocker_visible": any(
            summary.blocker == "frame-incoherent"
            and "localized_frame_coherence_below_floor" in summary.failure_reasons
            for summary in bad_summaries
        ),
        "nonstationary_blocker_visible": any(
            summary.blocker == "nonstationary-window"
            and "stationarity_window_below_floor" in summary.failure_reasons
            for summary in bad_summaries
        ),
        "expected_profile_outcomes_observed": all(
            summary.classification_matches_expectation for summary in summaries
        ),
        "diagnostic_only": True,
        "promotion_false": True,
    }
    ok = all(validation_flags.values())

    return {
        "harness": "ns_lrt_fourier_output_coupling_proxy",
        "script": "scripts/ns_lrt_fourier_output_coupling_proxy_harness.py",
        "diagnostic_only": True,
        "promotion": False,
        "clay_promoted": False,
        "ok": ok,
        "control": {
            "O": "Worker B NS A4 LRT physical-to-Fourier output coupling proxy lane.",
            "R": "Separate physical angular richness from Fourier output richness and Whitney/frame transfer.",
            "C": "scripts/ns_lrt_fourier_output_coupling_proxy_harness.py",
            "S": "Synthetic great-circle-frame table only; no LRT coupling theorem is established.",
            "L": "sweep regimes -> frame rows -> component margins -> good/bad separation -> fail-closed JSON.",
            "P": "Good profiles pass all component floors; bad profiles expose exactly the requested obstruction families.",
            "G": "promotion=false always; diagnostics cannot certify NS A4 or Clay progress.",
            "F": "Still missing the real Whitney/isotropy estimate linking physical vorticity richness to Fourier triadic output support.",
        },
        "parameters": asdict(params),
        "components": list(COMPONENTS),
        "summary": {
            "row_count": len(rows),
            "stable_sweep_count": len(stable_regimes),
            "profile_count": len(summaries),
            "good_profile_count": len(good_summaries),
            "bad_profile_count": len(bad_summaries),
            "good_rows_passing": sum(summary.rows_passing for summary in good_summaries),
            "bad_rows_passing": sum(summary.rows_passing for summary in bad_summaries),
            "min_good_coupling_margin": min(
                summary.min_coupling_margin for summary in good_summaries
            ),
            "max_bad_coupling_margin": max(
                summary.min_coupling_margin for summary in bad_summaries
            ),
            "min_good_fourier_spread": min(
                summary.min_fourier_spread for summary in good_summaries
            ),
            "max_bad_collapse_penalty": max(
                summary.max_collapse_penalty for summary in bad_summaries
            ),
            "ok": ok,
        },
        "validation_flags": validation_flags,
        "regimes": [asdict(regime) for regime in regimes],
        "profile_summaries": [asdict(summary) for summary in summaries],
        "rows": compact_rows(rows),
        "interpretation": {
            "supports": (
                "Synthetic A4 profiles can distinguish physical LRT angular richness from "
                "actual Fourier output spread and Whitney/frame transfer compatibility."
            ),
            "rejects": (
                "Physical richness alone is insufficient: the collapsed-output, missing-Whitney, "
                "frame-incoherent, and nonstationary profiles all fail."
            ),
            "residual_gap": (
                "A real A4 proof still needs a localized Whitney/isotropy coupling estimate "
                "between physical-space vorticity directions and Fourier triadic output directions."
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
        print("NS LRT Fourier output coupling proxy harness")
        print(f"wrote: {args.json_output}")
        print(
            "ok={ok} rows={rows} stable_sweeps={stable} good_margin={good:.6g} "
            "bad_margin={bad:.6g} min_good_spread={spread:.6g} "
            "max_bad_collapse={collapse:.6g} promotion=false".format(
                ok=str(payload["ok"]).lower(),
                rows=summary["row_count"],
                stable=summary["stable_sweep_count"],
                good=summary["min_good_coupling_margin"],
                bad=summary["max_bad_coupling_margin"],
                spread=summary["min_good_fourier_spread"],
                collapse=summary["max_bad_collapse_penalty"],
            )
        )
    return 0 if payload["ok"] and not payload["promotion"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
