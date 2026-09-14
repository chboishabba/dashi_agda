#!/usr/bin/env python3
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
REQUIRED = {
    "DASHI/Biology/DrosophilaSymbolicRateLearningCrossPollinationExact.agda": [
        "record SymbolicRateLearningCrossPollinationStatus",
        "continuousRateSpecializationImplemented",
        "archivedPartETraceRuleLocated",
        "heldOutPromotionGateImplemented",
        "finiteRunStabilityOnly",
        "globalStabilityClaimed",
        "kernelEligibilityAdapterImplemented",
        "maleCNSOrientationAdapterImplemented",
        "sparseRateArchivedTraceAdapterImplemented",
        "sparseRateTrainingEpochImplemented",
        "continuousNoLearningInterventionImplemented",
        "paperEligibilityConstructorRecovered",
        "maleCNSOrientationAdapterIsPaid",
        "sparseRateArchivedTraceAdapterIsPaid",
        "sparseRateTrainingEpochIsPaid",
        "continuousNoLearningInterventionIsPaid",
        "paperEligibilityConstructorStillUnpaid",
        "rateDynamicsDoNotReplaceTernaryKernel",
        "finiteRunBoundDoesNotProveGlobalStability",
        "archivedTraceRuleDoesNotPayViralTrainingRule",
        "paperFactorizationDoesNotCollapseToArchivedTraceRule",
        "maleCNSSourceTargetRequiresExplicitTranspose",
        "sparseArchivedAdapterDoesNotPayPaperEligibilityConstructor",
        "continuousNoLearningDoesNotPayTernaryLearningAdapter",
        "generalProgrammingStillNotPromotable",
    ],
    "DASHI/Biology/AnimalexicEverything.agda": [
        "DrosophilaSymbolicRateLearningCrossPollinationExact",
    ],
}

errors = []
for rel, needles in REQUIRED.items():
    path = ROOT / rel
    if not path.exists():
        errors.append(f"missing: {rel}")
        continue
    text = path.read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            errors.append(f"{rel}: missing {needle}")

if errors:
    print("\n".join(errors), file=sys.stderr)
    raise SystemExit(1)
print("drosophila symbolic rate-learning static contract: OK")
