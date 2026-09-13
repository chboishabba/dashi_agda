#!/usr/bin/env python3
"""Focused static contract for the James sensorimotor decision/action tranche."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Cognition/PNF/JamesSensorimotorDecisionActionExact.agda"
REGRESSION = ROOT / "DASHI/Cognition/PNF/JamesSensorimotorDecisionActionRegression.agda"
AGGREGATE = ROOT / "DASHI/Cognition/PNF/PNFIRLearningEverything.agda"

OWNER_NEEDLES = [
    "10.1162/JOCN.a.2484",
    "10.20944/preprints202507.0979.v1",
    "SensorimotorEpisode",
    "activeSensingStep",
    "learningThroughActiveSensing",
    "observedActionDoesNotRecoverSensorimotorState",
    "decisionPhenomenonIsNotMechanism",
    "memoryDescriptionIsNotLearningUpdate",
    "jamesDoesNotProveDeterminism",
    "jamesDoesNotProveLibertarianFreeWill",
]

REGRESSION_NEEDLES = [
    "import DASHI.Cognition.PNF.JamesSensorimotorDecisionActionExact as James",
    "canonicalJamesSensorimotorRegression",
]

AGGREGATE_NEEDLE = "import DASHI.Cognition.PNF.JamesSensorimotorDecisionActionExact"


def require_file(path: Path) -> str:
    if not path.exists():
        raise AssertionError(f"missing required file: {path.relative_to(ROOT)}")
    return path.read_text(encoding="utf-8")


def require_needles(label: str, text: str, needles: list[str]) -> None:
    missing = [needle for needle in needles if needle not in text]
    if missing:
        raise AssertionError(f"{label} missing required surfaces: {missing}")


def main() -> int:
    owner_text = require_file(OWNER)
    regression_text = require_file(REGRESSION)
    aggregate_text = require_file(AGGREGATE)

    require_needles("owner", owner_text, OWNER_NEEDLES)
    require_needles("regression", regression_text, REGRESSION_NEEDLES)
    require_needles("aggregate", aggregate_text, [AGGREGATE_NEEDLE])

    print("James sensorimotor decision/action static contract: OK")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"James sensorimotor decision/action static contract: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
