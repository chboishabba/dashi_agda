#!/usr/bin/env python3
"""Validate the fail-closed GD1/Q2 contradiction-gate tranche."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_gd1_q2_contradiction_gate_tranche.py"
CONTRACT = "check_ns_gd1_q2_contradiction_gate_tranche"
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260619/"
    "ns_gd1_q2_contradiction_gate_tranche_check_20260620.json"
)

MODULES = {
    "gd1": Path("DASHI/Physics/Closure/NSGD1MinPrincipleNoLambda3CollapseReceipt.agda"),
    "cz": Path("DASHI/Physics/Closure/NSGD1LayerCZIntegratedControlReceipt.agda"),
    "layer": Path("DASHI/Physics/Closure/NSBroadTubeLayerFractionContinuityReceipt.agda"),
    "lower": Path("DASHI/Physics/Closure/NSQ2BlowupLowerImplicationReceipt.agda"),
    "upper": Path("DASHI/Physics/Closure/NSQ2UniformUpperBoundFromGD1TheoremGReceipt.agda"),
    "audit": Path("DASHI/Physics/Closure/NSGD1Q2ContradictionGateAuditReceipt.agda"),
    "everything": Path("DASHI/Everything.agda"),
}

REQUIRED_MARKERS = {
    "gd1": (
        "dOmega_K = {lambda2 = 0}",
        "lambda3 is identified with g12",
        "Rellich-Kato eigenframe evolution",
        "integrated carrier boundary estimate",
        "viscous Kato gap cost",
        "pressureCzLInfNotAssumed",
        "hDelta1Discharged =\n        false",
    ),
    "cz": (
        "reject-pointwise-Linf-CZ-bound-as-discharge-gate",
        "pressure-hessian-integrated-control-gate",
        "surface-trace-sobolev-coarea-control-gate",
        "alpha=1-2*CCZ-positivity-assumption",
        "finalDischarge =\n        false",
    ),
    "layer": (
        "DNS 17% telemetry is only evidence",
        "uniform c_layer > 0",
        "incompressibility/Poincare",
        "broadTubeCoverageDischarged",
        "broadTubeCoverageDischarged ≡ false",
    ),
    "lower": (
        "finite-time blowup => Q2/carrier divergence",
        "layerFractionDependencyReal =\n        false",
        "nondegenerateCoareaTraceAligned =\n        false",
        "q2BlowupLowerImplicationDischarged =\n        false",
    ),
    "upper": (
        "dQ2/dt ≤ -δ1 * Q2 + C2 * ||u||_H5^4",
        "Finite-subinterval Gronwall row",
        "Uniform-to-blowup distinction",
        "finiteSubintervalBoundDischarged =\n        false",
        "uniformToBlowupBoundaryDischarged =\n        false",
    ),
    "audit": (
        "NSBroadTubeLayerFractionContinuityReceipt",
        "NSQ2UniformUpperBoundFromGD1TheoremGReceipt",
        "NSQ2BlowupLowerImplicationReceipt",
        "finiteSubintervalUpperBoundDependsOnNewModule =\n        false",
        "millerEnstrophyLowerRouteDependsOnNewModule =\n        false",
        "contradictionGateDischarged =\n        false",
        "clayNavierStokesPromoted =\n        false",
    ),
    "everything": (
        "import DASHI.Physics.Closure.NSGD1LayerCZIntegratedControlReceipt",
        "import DASHI.Physics.Closure.NSBroadTubeLayerFractionContinuityReceipt",
        "import DASHI.Physics.Closure.NSQ2BlowupLowerImplicationReceipt",
        "import DASHI.Physics.Closure.NSQ2UniformUpperBoundFromGD1TheoremGReceipt",
        "import DASHI.Physics.Closure.NSGD1Q2ContradictionGateAuditReceipt",
    ),
}

CONTROL_CARD = {
    "O": "Main agent validates the integrated GD1/Q2 contradiction-gate tranche.",
    "R": "Require all six proof-kernel surfaces to be present, wired, and fail-closed.",
    "C": SCRIPT_NAME,
    "S": "This checker validates markers and false gates only; it does not infer continuum analysis.",
    "L": "Read modules -> require markers -> emit JSON receipt.",
    "P": "FAIL_CLOSED_GD1_Q2_CONTRADICTION_GATE_TRANCHE",
    "G": "Promotion remains blocked unless explicit Agda fields flip under real proof terms.",
    "F": "Missing markers, missing imports, or accidentally promoted gates fail validation.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Path for checker JSON output.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON.")
    return parser.parse_args()


def _validate() -> tuple[list[str], dict[str, Any]]:
    errors: list[str] = []
    details: dict[str, Any] = {}
    for name, path in MODULES.items():
        if not path.exists():
            errors.append(f"missing module: {path}")
            details[name] = {"path": str(path), "exists": False}
            continue
        text = path.read_text(encoding="utf-8")
        marker_status = {marker: marker in text for marker in REQUIRED_MARKERS[name]}
        for marker, present in marker_status.items():
            if not present:
                errors.append(f"{name}: missing marker {marker!r}")
        details[name] = {
            "path": str(path),
            "exists": True,
            "markers": marker_status,
        }
    return errors, details


def main() -> int:
    args = _parse_args()
    errors, details = _validate()
    payload: dict[str, Any] = {
        "contract": CONTRACT,
        "status": "error" if errors else "ok",
        "control_card": CONTROL_CARD,
        "details": details,
        "errors": errors,
        "promotion_gate": False,
        "collapse_impossible": False,
        "clay_navier_stokes_promoted": False,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True)
        + "\n",
        encoding="utf-8",
    )
    print(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
