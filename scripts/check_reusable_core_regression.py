#!/usr/bin/env python3
"""Run the focused reusable-core regression tranche."""

from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

AGDA_TARGETS = [
    "DASHI/Core/AdapterCanonicalityCore.agda",
    "DASHI/Core/AuthorityNonPromotionCore.agda",
    "DASHI/Core/EmptyPromotionCore.agda",
    "DASHI/Core/CandidateOnlyCore.agda",
    "DASHI/Core/FormalLensQualificationCore.agda",
    "DASHI/Core/CandidateFunctionalCore.agda",
    "DASHI/Core/OperatorShapeNonAuthorityCore.agda",
    "DASHI/Core/BridgeRequirementCore.agda",
    "DASHI/Interop/VectorNonAuthorityCore.agda",
    "DASHI/Interop/PNFSpectralVectorIndex.agda",
    "DASHI/Interop/PNFResidualFieldInvariants.agda",
    "DASHI/Interop/PNFResolverSelectorCommitment.agda",
    "DASHI/Interop/PNFSpectralRegistryAnchoring.agda",
    "DASHI/Interop/PNFSpectralCoordinateRebuildability.agda",
    "DASHI/Interop/InterMediaCarrierBridge.agda",
    "DASHI/Interop/QiCarrierFieldBridge.agda",
    "DASHI/Interop/MeditationQiBridge.agda",
    "DASHI/Interop/InterMediaBridgeRegression.agda",
    "DASHI/Culture/QiOperatorTheoryBoundary.agda",
    "DASHI/Interop/TypedTermRoleFunctor.agda",
    "DASHI/Interop/StratifiedTypedComparisonLaw.agda",
    "DASHI/Interop/BackgroundDistributionBridge.agda",
    "DASHI/Promotion/CrossDomainClaimPromotionBoundary.agda",
    "DASHI/Interop/AggregateBidirectionalTranslationDischarge.agda",
    "DASHI/Biology/CrossSpeciesOntologyTranslationBridge.agda",
    "DASHI/Biology/EmbodiedMotorMultisensoryBridge.agda",
    "DASHI/Biology/AnimalSenseObservationThreadDischarge.agda",
    "DASHI/Interop/WikidataCandidateRoleBridge.agda",
    "DASHI/Ontology/WikidataAnimalSemanticJoinLayer.agda",
    "DASHI/Promotion/ObligationIndex.agda",
]

OPTIONAL_AGDA_TARGETS = [
    "DASHI/Biology/BioactiveMolecularRecognitionBridge.agda",
    "DASHI/Biology/NeurochemicalTransmissionBridge.agda",
    "DASHI/Biology/NeurochemicalVocabularyReceipt.agda",
    "DASHI/Promotion/NeurochemicalAuthorityBoundary.agda",
]

AGDA_TARGETS.extend(
    target for target in OPTIONAL_AGDA_TARGETS if (ROOT / target).is_file()
)


def run(label: str, cmd: list[str]) -> int:
    print(f"\n== {label} ==")
    print("+ " + " ".join(cmd))
    completed = subprocess.run(cmd, cwd=ROOT)
    if completed.returncode != 0:
        print(f"{label} failed with exit code {completed.returncode}")
    return completed.returncode


def active_agda_or_ghc() -> int:
    if shutil.which("ps") is None:
        return 0

    completed = subprocess.run(
        ["ps", "-eo", "pid=,comm=,args="],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        return 0

    current_pid = str(__import__("os").getpid())
    hits = []
    for line in completed.stdout.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith(current_pid + " "):
            continue
        parts = stripped.split(maxsplit=2)
        if len(parts) < 2:
            continue
        command = parts[1].lower()
        args = parts[2].lower() if len(parts) > 2 else ""
        command_line = f"{command} {args}".strip()
        if command in {"agda", "ghc", "ghc-iserv"} or command_line.startswith(
            ("agda ", "ghc ", "ghc-iserv ")
        ):
            hits.append(stripped)

    if hits:
        print("Active Agda/GHC-like processes detected before regression:")
        for hit in hits[:20]:
            print(f"  {hit}")
        if len(hits) > 20:
            print(f"  ... {len(hits) - 20} more")
        print("Continuing; stop competing checks manually if they are stale.")
    return 0


def main() -> int:
    active_agda_or_ghc()

    commands: list[tuple[str, list[str]]] = [
        ("git diff whitespace check", ["git", "diff", "--check"]),
        (
            "reusable core candidate audit",
            [sys.executable, "scripts/audit_reusable_core_candidates.py"],
        ),
    ]

    for target in AGDA_TARGETS:
        commands.append((f"agda {target}", ["agda", "-i", ".", target]))

    for label, cmd in commands:
        result = run(label, cmd)
        if result != 0:
            return result

    print("\nReusable-core regression passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
