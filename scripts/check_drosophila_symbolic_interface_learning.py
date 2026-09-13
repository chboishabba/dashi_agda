#!/usr/bin/env python3
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
REQUIRED = {
    "DASHI/Biology/DrosophilaSymbolicInterfaceLearningExact.agda": [
        "record SymbolicInterfaceExperiment",
        "data CompetenceLevel",
        "artificialSymbolicActuator",
        "connectomeDoesNotDetermineExecutableDynamics",
        "emittedCharactersDoNotEstablishPythonKnowledge",
        "fizzBuzzDoesNotEstablishGeneralProgrammingCompetence",
        "programTextDoesNotRecoverNeuralObservation",
        "record PythonDemoImplementationDebt",
        "canonicalPythonDemoImplementationDebt",
        "primaryImplementationStillUnpaid",
        "adjacentDemoAssistanceDoesNotTransferToPythonRun",
        "stronglyCorroboratedIdentityStillIsNotSameObjectReceipt",
        "record PublicArtifactSearchReceipt",
        "canonicalPublicArtifactSearchReceipt",
        "publicSearchNotFoundDoesNotProveNoArtifact",
        "publicArtifactStillNotLocated",
        "connectomeAdvantageRequiresNullComparison",
    ],
    "DASHI/Biology/DrosophilaSymbolicInterfaceLearningRegression.agda": [
        "canonicalDrosophilaSymbolicInterfaceRegression",
        "implementationRecoveryStillOpen",
        "adjacentAssistanceStillDoesNotTransfer",
        "sameObjectIdentityStillUnpaid",
        "negativePublicSearchStillDoesNotProveAbsence",
        "publicArtifactStillUnrecovered",
    ],
    "DASHI/Biology/AnimalexicEverything.agda": [
        "DrosophilaSymbolicInterfaceLearningExact",
        "DrosophilaSymbolicInterfaceLearningRegression",
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
print("drosophila symbolic interface static contract: OK")
