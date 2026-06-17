#!/usr/bin/env python3
"""Run the focused reusable-core regression tranche."""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AGDA29_PARALLEL_CHECK = ROOT / "scripts" / "run_agda29_parallel_check.sh"

BASE_AGDA_TARGETS = [
    "DASHI/Core/AdapterCanonicalityCore.agda",
    "DASHI/Core/AuthorityNonPromotionCore.agda",
    "DASHI/Core/EmptyPromotionCore.agda",
    "DASHI/Core/CandidateOnlyCore.agda",
    "DASHI/Core/ControlCardCore.agda",
    "DASHI/Core/FormalLensQualificationCore.agda",
    "DASHI/Core/FormalLensVocabularyCore.agda",
    "DASHI/Core/HiddenLiftProjectionCore.agda",
    "DASHI/Core/StatisticalEvidenceCore.agda",
    "DASHI/Core/SourceProcessEvidenceCore.agda",
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
    "DASHI/Promotion/AuthorityBoundaryCore.agda",
    "DASHI/Biology/BioactiveAuthorityBoundaryCore.agda",
    "DASHI/Biology/BioactiveMolecularRecognitionBridge.agda",
    "DASHI/Biology/NeurochemicalAtomicChemistryBridge.agda",
    "DASHI/Biology/NeurochemicalBrainCarrierBridge.agda",
    "DASHI/Biology/NeurochemicalGenomicExpressionBridge.agda",
    "DASHI/Biology/NeurochemicalProteinTargetBridge.agda",
    "DASHI/Biology/NeurochemicalTransmissionBridge.agda",
    "DASHI/Biology/NeurochemicalVocabularyReceipt.agda",
    "DASHI/Promotion/NeurochemicalAuthorityBoundary.agda",
    "DASHI/Core/FingerprintProjectionCore.agda",
    "DASHI/Crypto/HashCandidateBoundary.agda",
    "DASHI/Crypto/RSAArithmeticCore.agda",
    "DASHI/Crypto/RSABatchSharedPrimeBoundary.agda",
    "DASHI/Crypto/RSACRTChamberCore.agda",
    "DASHI/Crypto/RSAEntropySourceStatisticalBoundary.agda",
    "DASHI/Crypto/RSAIterationLeakBoundary.agda",
    "DASHI/Crypto/RSAKeygenTraceCore.agda",
    "DASHI/Crypto/RSAKeygenSourceBoundary.agda",
    "DASHI/Crypto/RSASharedPrimeCollapse.agda",
    "DASHI/Crypto/RSAVulnerabilityBoundary.agda",
    "DASHI/Crypto/RSABTResidueBraidHypervoxelBoundary.agda",
    "DASHI/Core/FormalLensLawCore.agda",
    "DASHI/Core/FormalStructureLawCore.agda",
    "DASHI/Core/SourceProcessEvidenceLawCore.agda",
]


def _existing_targets(targets: list[str]) -> list[str]:
    """Return existing targets in the fixed order, deduplicated."""
    seen: set[str] = set()
    selected: list[str] = []
    for target in targets:
        if target in seen:
            continue
        if (ROOT / target).is_file():
            seen.add(target)
            selected.append(target)
    return selected


OPTIONAL_AGDA_TARGETS_AVAILABLE = _existing_targets(OPTIONAL_AGDA_TARGETS)
MISSING_OPTIONAL_AGDA_TARGETS = [
    target for target in OPTIONAL_AGDA_TARGETS if target not in OPTIONAL_AGDA_TARGETS_AVAILABLE
]
AGDA_TARGETS = BASE_AGDA_TARGETS + OPTIONAL_AGDA_TARGETS_AVAILABLE


def run(label: str, cmd: list[str], *, env: dict[str, str] | None = None) -> int:
    print(f"\n== {label} ==")
    print("+ " + " ".join(cmd))
    completed = subprocess.run(cmd, cwd=ROOT, env=env)
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

    current_pid = str(os.getpid())
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


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run the focused reusable-core regression tranche."
    )
    parser.add_argument(
        "--agda29-parallel",
        action="store_true",
        help="Use the Agda 2.9 parallel shadow-runner for module checks.",
    )
    parser.add_argument(
        "--agda29-jobs",
        type=int,
        default=8,
        help="Parallel jobs for --agda29-parallel (default: 8).",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.agda29_parallel and args.agda29_jobs < 1:
        print(f"--agda29-jobs must be >= 1 (got {args.agda29_jobs})")
        return 1
    active_agda_or_ghc()

    if MISSING_OPTIONAL_AGDA_TARGETS:
        print("Optional AGDA targets not present and will be skipped:")
        for target in MISSING_OPTIONAL_AGDA_TARGETS:
            print(f"  - {target}")

    commands: list[tuple[str, list[str], dict[str, str] | None]] = [
        ("git diff whitespace check", ["git", "diff", "--check"], None),
        (
            "reusable core candidate audit",
            [sys.executable, "scripts/audit_reusable_core_candidates.py"],
            None,
        ),
        (
            "authority-boundary candidate audit",
            [
                sys.executable,
                "scripts/audit_authority_boundary_candidates.py",
                "--no-write",
            ],
            None,
        ),
        (
            "control-card candidate audit",
            [
                sys.executable,
                "scripts/audit_control_card_candidates.py",
                "--no-write",
            ],
            None,
        ),
        (
            "source-process evidence candidate audit",
            [
                sys.executable,
                "scripts/audit_source_process_evidence_candidates.py",
            ],
            None,
        ),
    ]

    if args.agda29_parallel:
        if not AGDA29_PARALLEL_CHECK.is_file():
            print(
                f"Requested --agda29-parallel but helper is missing: {AGDA29_PARALLEL_CHECK}"
            )
            return 1
        if not os.access(AGDA29_PARALLEL_CHECK, os.X_OK):
            print(
                "Requested --agda29-parallel but helper is not executable: "
                f"{AGDA29_PARALLEL_CHECK}"
            )
            return 1
        agda29_env = os.environ.copy()
        agda29_env["AGDA_JOBS"] = str(args.agda29_jobs)
        commands.append(
            (
                "agda29 parallel reusable core targets",
                [str(AGDA29_PARALLEL_CHECK.relative_to(ROOT)), *AGDA_TARGETS],
                agda29_env,
            )
        )
    else:
        for target in AGDA_TARGETS:
            commands.append((f"agda {target}", ["agda", "-i", ".", target], None))

    for label, cmd, env in commands:
        result = run(label, cmd, env=env)
        if result != 0:
            return result

    print("\nReusable-core regression passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
