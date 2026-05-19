#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
QUEUE_SCRIPT = ROOT / "scripts" / "generate_layer2_long_compute_queue.py"
HISTORY_PATH = ROOT / "artifacts" / "agda_route_cost_history.json"

L0_EXACT = {
    "DASHI/Geometry/CausalForcesLorentz31.agda",
    "DASHI/Geometry/Signature31FromIntrinsicShellForcing.agda",
    "DASHI/Physics/Signature31IntrinsicShiftInstance.agda",
    "DASHI/Physics/Signature31FromShiftOrbitProfile.agda",
    "DASHI/Physics/Closure/ContractionQuadraticToSignatureBridgeTheorem.agda",
    "DASHI/Physics/Closure/QuadraticToCliffordBridgeTheorem.agda",
    "DASHI/Physics/CliffordEvenLiftBridge.agda",
    "DASHI/Physics/Closure/CliffordToEvenWaveLiftBridgeTheorem.agda",
    "DASHI/Physics/Closure/CanonicalContractionToCliffordBridgeTheorem.agda",
    "DASHI/Physics/Closure/KnownLimitsQFTBridgeTheorem.agda",
    "DASHI/Physics/Closure/Canonical/LocalProgramBundle.agda",
    "DASHI/Physics/Closure/Canonical/Ladder.agda",
    "DASHI/Physics/Closure/PhysicsClosureSummary.agda",
    "Ontology/Hecke/Layer2FiniteSearchShell.agda",
}

L0_PREFIXES = (
    "Kernel/",
    "Verification/",
)

L1_EXACT = {
    "DASHI/Physics/Closure/CanonicalStageC.agda",
    "Ontology/Hecke/SaturatedInvariantRefinementStatus.agda",
}

L2_EXACT = {
    "DASHI/Everything.agda",
    "DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda",
    "DASHI/Physics/Closure/ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda",
    "DASHI/Physics/Closure/ShiftObservableSignaturePressureConsumer.agda",
    "DASHI/Physics/DashiDynamicsShiftInstance.agda",
    "DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda",
    "DASHI/Physics/Closure/CanonicalGaugeMatterStrengtheningTheorem.agda",
    "DASHI/Physics/Closure/KnownLimitsFullMatterGaugeTheorem.agda",
    "DASHI/Physics/Closure/AtomicPhotonuclearContactGateTheorem.agda",
    "DASHI/Physics/Closure/CanonicalP2KeyScheduleBridgeObstruction.agda",
    "DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda",
    "Ontology/Hecke/DefectOrbitSummaryRefinement.agda",
    "Ontology/Hecke/ForcedStableCountDecomposition.agda",
    "Ontology/Hecke/TriadIndexedDefectOrbitSummaryRefinement.agda",
    "Ontology/Hecke/CurrentSaturatedTriadHistogramSeparation.agda",
    "Ontology/Hecke/CurrentSaturatedSectorHistogramComputations.agda",
    "Ontology/Hecke/CurrentSaturatedPredictedPairComparisons.agda",
    "Ontology/Hecke/TriadSectorCorrelationRefinement.agda",
    "Ontology/Hecke/Layer2FiniteSearch.agda",
}

NATURAL_CHARGE_HEAVY_TIMEOUT_10 = {
    "DASHI/Physics/Closure/CanonicalP2KeyScheduleBridgeObstruction.agda",
    "DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda",
}


@dataclass(frozen=True)
class RouteDecision:
    target: str
    layer: str
    route: str
    execute_allowed: bool
    policy_reason_code: str
    rationale: str
    recommended_command: list[str]


def normalize_target(raw_target: str) -> str:
    path = Path(raw_target)
    if path.is_absolute():
        rel = path.resolve().relative_to(ROOT)
    else:
        rel = path
    rel_str = rel.as_posix()
    if not rel_str.endswith(".agda"):
        raise SystemExit(f"Target must be a .agda file path relative to {ROOT}: {raw_target}")
    if not (ROOT / rel_str).exists():
        raise SystemExit(f"Target does not exist under repo root: {rel_str}")
    return rel_str


def is_heavy_hecke_lane(target: str) -> bool:
    return target.startswith("Ontology/Hecke/") and target in L2_EXACT


def load_cost_history(path: Path) -> dict[str, object]:
    if not path.exists():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return payload if isinstance(payload, dict) else {}


def with_history_override(decision: RouteDecision, history: dict[str, object], budget_seconds: int) -> RouteDecision:
    row = history.get(decision.target)
    if not isinstance(row, dict):
        return decision
    timeout_count = int(row.get("timeout_count", 0) or 0)
    max_elapsed_s = float(row.get("max_elapsed_s", 0.0) or 0.0)
    if decision.layer != "L1":
        return decision
    if timeout_count >= 2 or max_elapsed_s >= 90.0:
        return RouteDecision(
            target=decision.target,
            layer="L2",
            route="offline-only",
            execute_allowed=False,
            policy_reason_code="observed_offline_only",
            rationale=(
                "Observed bounded-history cost is too high for routine execution; "
                "route this target offline until it is reclassified."
            ),
            recommended_command=["timeout", str(budget_seconds), "agda", "-i", ".", decision.target],
        )
    if timeout_count >= 1 or max_elapsed_s >= 20.0:
        return RouteDecision(
            target=decision.target,
            layer="L1",
            route="bounded",
            execute_allowed=True,
            policy_reason_code="observed_bounded_slow",
            rationale=(
                "Observed bounded-history cost is nontrivial; keep this target capped "
                "and treat it as a slower medium lane."
            ),
            recommended_command=decision.recommended_command,
        )
    return decision


def classify_target(
    target: str,
    budget_seconds: int,
    jobs: int,
    queue_dir: Path,
    history: dict[str, object],
) -> RouteDecision:
    decision: RouteDecision
    if target in L0_EXACT or target.startswith(L0_PREFIXES):
        decision = RouteDecision(
            target=target,
            layer="L0",
            route="interactive",
            execute_allowed=True,
            policy_reason_code="thin_interactive",
            rationale="Thin or routine validation target; safe for normal interactive loops.",
            recommended_command=["agda", "-i", ".", target],
        )
    elif target in L1_EXACT:
        decision = RouteDecision(
            target=target,
            layer="L1",
            route="bounded",
            execute_allowed=True,
            policy_reason_code="medium_bounded",
            rationale="Medium target; run only with an explicit bounded budget.",
            recommended_command=["timeout", str(budget_seconds), "agda", "-i", ".", target],
        )
    elif target in L2_EXACT:
        recommended_timeout = 10 if target in NATURAL_CHARGE_HEAVY_TIMEOUT_10 else budget_seconds
        if is_heavy_hecke_lane(target):
            decision = RouteDecision(
                target=target,
                layer="L2",
                route="queue",
                execute_allowed=True,
                policy_reason_code="hecke_heavy_queue",
                rationale=(
                    "Heavy current Layer 2 Hecke target; do not run interactively. "
                    "Materialize the fixed queue and hand off the heavy lane offline."
                ),
                recommended_command=[
                    sys.executable,
                    str(QUEUE_SCRIPT),
                    "--include-commands",
                    "--parallel",
                    "-j",
                    str(jobs),
                    "--write-batch-files",
                    str(queue_dir),
                ],
            )
        else:
            decision = RouteDecision(
                target=target,
                layer="L2",
                route="offline-only",
                execute_allowed=False,
                policy_reason_code="heavy_offline_only",
                rationale="Heavy aggregate target; keep it out of the interactive loop.",
                recommended_command=["timeout", str(recommended_timeout), "agda", "-i", ".", target],
            )
    elif target.startswith("Ontology/Hecke/"):
        decision = RouteDecision(
            target=target,
            layer="L1",
            route="bounded",
            execute_allowed=True,
            policy_reason_code="hecke_default_bounded",
            rationale="Hecke target outside the known heavy lane; treat conservatively as bounded-only.",
            recommended_command=["timeout", str(budget_seconds), "agda", "-i", ".", target],
        )
    elif "ValidationSummary" in target or target.endswith("Everything.agda"):
        decision = RouteDecision(
            target=target,
            layer="L2",
            route="offline-only",
            execute_allowed=False,
            policy_reason_code="aggregate_offline_only",
            rationale="Aggregate summary surface; conservative offline-only routing.",
            recommended_command=["timeout", str(budget_seconds), "agda", "-i", ".", target],
        )
    else:
        decision = RouteDecision(
            target=target,
            layer="L1",
            route="bounded",
            execute_allowed=True,
            policy_reason_code="default_bounded",
            rationale="Unknown target; default to bounded execution rather than interactive or heavy-only.",
            recommended_command=["timeout", str(budget_seconds), "agda", "-i", ".", target],
        )
    return with_history_override(decision, history, budget_seconds)


def render_text(decisions: list[RouteDecision]) -> str:
    lines: list[str] = []
    for decision in decisions:
        lines.extend(
            [
                f"target: {decision.target}",
                f"  layer: {decision.layer}",
                f"  route: {decision.route}",
                f"  execute_allowed: {'yes' if decision.execute_allowed else 'no'}",
                f"  policy_reason_code: {decision.policy_reason_code}",
                f"  rationale: {decision.rationale}",
                f"  command: {' '.join(decision.recommended_command)}",
            ]
        )
    return "\n".join(lines)


def update_cost_history(path: Path, result: dict[str, object]) -> None:
    if result["status"] == "blocked_by_policy":
        return
    history = load_cost_history(path)
    target = str(result["target"])
    row = history.get(target)
    if not isinstance(row, dict):
        row = {}
    elapsed_s = float(result.get("elapsed_s", 0.0) or 0.0)
    timeout_count = int(row.get("timeout_count", 0) or 0)
    success_count = int(row.get("success_count", 0) or 0)
    run_count = int(row.get("run_count", 0) or 0) + 1
    outcome = result.get("outcome_reason_code")
    if outcome == "timeout":
        timeout_count += 1
    if outcome == "completed":
        success_count += 1
    row.update(
        {
            "last_layer": result["layer"],
            "last_route": result["route"],
            "last_status": result["status"],
            "last_outcome_reason_code": outcome,
            "last_elapsed_s": elapsed_s,
            "max_elapsed_s": max(float(row.get("max_elapsed_s", 0.0) or 0.0), elapsed_s),
            "run_count": run_count,
            "timeout_count": timeout_count,
            "success_count": success_count,
        }
    )
    history[target] = row
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(history, indent=2, sort_keys=True), encoding="utf-8")


def run_decision(decision: RouteDecision, history_path: Path | None = None) -> dict[str, object]:
    if not decision.execute_allowed:
        return {
            "target": decision.target,
            "layer": decision.layer,
            "route": decision.route,
            "status": "blocked_by_policy",
            "policy_reason_code": decision.policy_reason_code,
            "outcome_reason_code": "blocked_by_policy",
            "rationale": decision.rationale,
            "recommended_command": decision.recommended_command,
        }
    started = time.monotonic()
    completed = subprocess.run(
        decision.recommended_command,
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    elapsed_s = round(time.monotonic() - started, 3)
    if completed.returncode == 0:
        outcome_reason_code = "completed"
        status = "ok"
    elif completed.returncode == 124:
        outcome_reason_code = "timeout"
        status = "failed"
    else:
        outcome_reason_code = "compile_error"
        status = "failed"
    result = {
        "target": decision.target,
        "layer": decision.layer,
        "route": decision.route,
        "status": status,
        "policy_reason_code": decision.policy_reason_code,
        "outcome_reason_code": outcome_reason_code,
        "elapsed_s": elapsed_s,
        "returncode": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
        "recommended_command": decision.recommended_command,
    }
    if history_path is not None:
        update_cost_history(history_path, result)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Classify dashi_agda modules into L0/L1/L2 and route them to "
            "interactive, bounded, or queue-only execution."
        )
    )
    parser.add_argument("targets", nargs="+", help="Agda file paths relative to the repo root.")
    parser.add_argument(
        "--budget-seconds",
        type=int,
        default=120,
        help="Timeout budget for bounded L1 routing and offline-only recommendations.",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=4,
        help="Parallel jobs to embed in the Layer 2 queue command template.",
    )
    parser.add_argument(
        "--queue-dir",
        type=Path,
        default=ROOT / "artifacts" / "layer2_queue_policy",
        help="Output directory used when routing heavy Hecke targets to the queue emitter.",
    )
    parser.add_argument(
        "--history-path",
        type=Path,
        default=HISTORY_PATH,
        help="JSON file used to record observed runtime and timeout history per target.",
    )
    parser.add_argument(
        "--format",
        choices=("text", "json"),
        default="text",
        help="Render the routing plan as human-readable text or JSON.",
    )
    parser.add_argument(
        "--execute",
        action="store_true",
        help="Run the routed action when policy allows it. L2 offline-only targets remain blocked.",
    )
    args = parser.parse_args()

    targets = [normalize_target(raw) for raw in args.targets]
    history = load_cost_history(args.history_path)
    decisions = [
        classify_target(
            target,
            budget_seconds=args.budget_seconds,
            jobs=args.jobs,
            queue_dir=args.queue_dir,
            history=history,
        )
        for target in targets
    ]

    if args.execute:
        payload = [run_decision(decision, history_path=args.history_path) for decision in decisions]
    else:
        payload = [asdict(decision) for decision in decisions]

    if args.format == "json":
        print(json.dumps(payload, indent=2))
    else:
        if args.execute:
            lines: list[str] = []
            for row in payload:
                lines.extend(
                    [
                        f"target: {row['target']}",
                        f"  layer: {row['layer']}",
                        f"  route: {row['route']}",
                        f"  status: {row['status']}",
                        f"  policy_reason_code: {row['policy_reason_code']}",
                    ]
                )
                if row["status"] == "blocked_by_policy":
                    lines.append(f"  rationale: {row['rationale']}")
                else:
                    lines.append(f"  outcome_reason_code: {row['outcome_reason_code']}")
                    lines.append(f"  returncode: {row['returncode']}")
            print("\n".join(lines))
        else:
            print(render_text(decisions))


if __name__ == "__main__":
    main()
