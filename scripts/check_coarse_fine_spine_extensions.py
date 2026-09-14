#!/usr/bin/env python3
"""Static contract for the #902 canonical-spine extension surface.

This checker is intentionally source-level.  It does not replace Agda kernel
checking; it catches cheap structural regressions and malformed source that
should fail before the expensive kernel stage.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED_FILES = [
    "DASHI/Core/CanonicalSpineRegistry.agda",
    "DASHI/Core/CanonicalSpineRegistryCrossDomainRegression.agda",
    "DASHI/Core/CanonicalSpineDependencyAtlasExact.agda",
    "DASHI/Core/CanonicalSpineDependencyAtlasRegression.agda",
    "DASHI/Core/ObserverRefinementCore.agda",
    "DASHI/Core/ObserverRefinementLatticeExact.agda",
    "DASHI/Core/ObserverRefinementOrientationCrosswalkExact.agda",
    "DASHI/Core/ObserverRefinementOrientationCrosswalkRegression.agda",
    "DASHI/Core/ObserverIncomparabilityTypedJoinExact.agda",
    "DASHI/Core/ObserverIncomparabilityCrosswalkExact.agda",
    "DASHI/Core/ObserverIncomparabilityCrosswalkRegression.agda",
    "DASHI/Core/KernelConsumerDescentFactorisationCrosswalkExact.agda",
    "DASHI/Core/KernelConsumerDescentFactorisationCrosswalkRegression.agda",
    "DASHI/Core/ConsumerIndexedResidualRefinementExact.agda",
    "DASHI/Core/ConsumerResidualRepairCrosswalkExact.agda",
    "DASHI/Core/ConsumerResidualRepairCrosswalkRegression.agda",
    "DASHI/Core/ConsumerObserverJoinResidualExact.agda",
    "DASHI/Core/ConsumerObserverJoinResidualCrosswalkExact.agda",
    "DASHI/Core/ConsumerObserverJoinResidualCrosswalkRegression.agda",
    "DASHI/Core/ReopenableConsumerInterventionCrossDomainRegression.agda",
    "DASHI/Core/ConsumerFibreRepairExact.agda",
    "DASHI/Core/ContextIndexedGovernedObservationExact.agda",
    "DASHI/Core/ContextIndexedGovernedObservationCanonicalRegression.agda",
    "DASHI/Core/ResidualObserverDependencyExact.agda",
    "DASHI/Core/ResidualObserverDependencyProjectionAdapterRegression.agda",
    "DASHI/Core/DeclaredScenarioRobustnessExact.agda",
    "DASHI/Core/DeclaredScenarioRobustnessRegression.agda",
    "DASHI/Core/RequiredObserverAxisJoinAdequacyExact.agda",
    "DASHI/Core/RequiredObserverAxisJoinCanonicalPairRegression.agda",
    "DASHI/Core/ExperimentalCoordinateProjectionBridgeExact.agda",
    "DASHI/Core/ExperimentalCoordinateProjectionBridgeRegression.agda",
    "DASHI/Core/SnowballOSINTAcquisitionInvariantExact.agda",
    "DASHI/Core/BoundedNegativeSearchExact.agda",
    "DASHI/Core/BoundedNegativeSearchRegression.agda",
    "DASHI/Interop/OSINTBoundedNegativeSearchAdapterExact.agda",
    "DASHI/Interop/OSINTBoundedNegativeSearchAdapterRegression.agda",
    "DASHI/Core/RobustExperimentInferenceFrontierExact.agda",
    "DASHI/Core/FrozenHeldOutRepairRefinementExact.agda",
    "DASHI/Core/FrozenHeldOutRepairRefinementRegression.agda",
    "DASHI/Core/MultipartSameObjectReconstructionExact.agda",
    "DASHI/Core/MultipartSameObjectReconstructionRegression.agda",
    "DASHI/ComputerScience/RSA260MultipartReconstructionSpineExact.agda",
    "DASHI/ComputerScience/RSA260MultipartReconstructionSpineRegression.agda",
    "DASHI/Core/FrozenProvenanceDynamicRefinementExact.agda",
    "DASHI/Core/QueryIndexedFrozenDynamicPromotionExact.agda",
    "DASHI/Semantics/SIOSemanticSurfaceBridge.agda",
    "DASHI/Semantics/SIOObserverRefinementLatticeAdapterExact.agda",
    "DASHI/Semantics/SIOObserverRefinementLatticeAdapterRegression.agda",
    "DASHI/CoarseFineFabricEverything.agda",
]

EXPECTED = {
    "DASHI/Core/CanonicalSpineRegistry.agda": [
        "observerRefinementOwner : CanonicalOwner",
        "requiredObserverAxisJoinOwner : CanonicalOwner",
        "declaredScenarioRobustnessOwner : CanonicalOwner",
        "osintAcquisitionOwner : CanonicalOwner",
        "boundedNegativeSearchOwner : CanonicalOwner",
        "robustExperimentInferenceOwner : CanonicalOwner",
        "multipartReconstructionOwner : CanonicalOwner",
        "frozenProvenanceDynamicOwner : CanonicalOwner",
        "queryIndexedFutureSafePromotionOwner : CanonicalOwner",
    ],
    "DASHI/Core/CanonicalSpineDependencyAtlasExact.agda": [
        "consumerRepairDependsOnObserverRefinement",
        "frozenDynamicDependsOnObserverRefinement",
        "requiredAxisJoinDependsOnObserverRefinement",
        "requiredAxisJoinDependsOnQueryAdequacy",
        "boundedNegativeSearchDependsOnOSINT",
        "attributionSnowballDependsOnAttributedSource",
        "requirementBatchDependsOnCandidateExecution",
        "futureSafePromotionDependsOnQueryAdequacy",
        "futureSafePromotionDependsOnFrozenDynamic",
        "structuralParentageImpliesCodeImportDependency",
    ],
    "DASHI/Core/ObserverRefinementLatticeExact.agda": [
        "record StrictRefinement",
        "pairObserver :",
        "strictPairRefinement :",
        "addingObserverShrinksResidualFibre :",
    ],
    "DASHI/Core/ObserverRefinementOrientationCrosswalkExact.agda": [
        "latticeRefinesToCore :",
        "coreRefinesToLattice :",
        "pairObserversAgreePointwise :",
        "latticeStrictToCore :",
        "coreStrictToLattice :",
    ],
    "DASHI/Core/ObserverIncomparabilityCrosswalkExact.agda": [
        "typedIncomparableToCoreCrossCollision :",
        "coreCrossCollisionToTypedIncomparable :",
        "typedJoinStrictLeftToCore :",
        "typedJoinStrictRightToLattice :",
    ],
    "DASHI/Core/KernelConsumerDescentFactorisationCrosswalkExact.agda": [
        "kernelDescentToFactorized :",
        "factorizedToKernelDescent :",
    ],
    "DASHI/Core/ConsumerResidualRepairCrosswalkExact.agda": [
        "residualCollisionToNonDescent :",
        "nonDescentToResidualCollision :",
        "residualRepairToCanonicalRepair :",
        "canonicalRepairToResidualRepair :",
        "residualMustSeparateViaCanonicalRepair :",
    ],
    "DASHI/Core/ConsumerObserverJoinResidualExact.agda": [
        "Lattice.pairObserver (observe left) (observe right)",
        "Lattice.pairRefinesLeft (observe left) (observe right)",
        "Lattice.pairRefinesRight (observe left) (observe right)",
    ],
    "DASHI/Core/ConsumerObserverJoinResidualCrosswalkExact.agda": [
        "hotColdToCoarseFineReopening :",
        "coarseFineReopeningToHotCold :",
        "consumerSufficientHotToFactorized :",
        "minimalHotSufficiencyToFactorized :",
    ],
    "DASHI/Core/ReopenableConsumerInterventionCrossDomainRegression.agda": [
        "ObserverResidualCrosswalk.sameHotAndResidualSameFineViaCanonical recoverableFine",
    ],
    "DASHI/Core/ConsumerFibreRepairExact.agda": [
        "Observer.pairObserver observe refine",
        "observerPairingHasSingleCanonicalOwner",
    ],
    "DASHI/Core/ContextIndexedGovernedObservationExact.agda": [
        "activeGovernedCollisionAsCanonicalNonDescent :",
        "Descent.nonDescentWitnessBlocksSufficiency",
    ],
    "DASHI/Core/ResidualObserverDependencyExact.agda": [
        "hiddenResidualDependencyProjectionCollision :",
        "hiddenResidualDependencyRefutesCoarseFactorisation :",
        "Calculus.consumerCannotFactorThroughProjection",
    ],
    "DASHI/Core/DeclaredScenarioRobustnessExact.agda": [
        "fromUniversalObligation :",
        "robustnessRestrictsToSubensemble :",
        "declaredFamilyAutomaticallyRecoversUniversalObligation = false",
    ],
    "DASHI/Core/RequiredObserverAxisJoinAdequacyExact.agda": [
        "jointAxis = Observer.pairObserver",
        "jointAxisIsCanonicalPairObserver :",
        "candidateRetainingBothRetainsJoint :",
        "leftAxisDefectBlocksRetainingBoth :",
        "rightAxisDefectBlocksRetainingBoth :",
    ],
    "DASHI/Core/ExperimentalCoordinateProjectionBridgeExact.agda": [
        "coordinateSeparationYieldsProjectionCollision :",
        "coordinateJoinRetainsExistingAndNewAxis :",
    ],
    "DASHI/Core/BoundedNegativeSearchExact.agda": [
        "boundedNegativeSearchWithCoverageProvesGlobalAbsence :",
    ],
    "DASHI/Interop/OSINTBoundedNegativeSearchAdapterExact.agda": [
        "osintSearchFailureDoesNotCreateKnownAbsence :",
        "coveredBoundedSearchProvesGlobalAbsence :",
    ],
    "DASHI/Core/FrozenHeldOutRepairRefinementExact.agda": [
        "record FrozenHeldOutRepair",
        "data TrainingFitCreatesHeldOutValidity : Set where",
    ],
    "DASHI/Core/MultipartSameObjectReconstructionExact.agda": [
        "record CompleteMultipartReconstruction",
        "reconstructionCreatesHistoricalCustodyIsFalse",
    ],
    "DASHI/ComputerScience/RSA260MultipartReconstructionSpineExact.agda": [
        "rsa260CompleteMultipartReconstructionStillUnpaid :",
        "rsa260LocalValidityDoesNotCreateWhole :",
    ],
    "DASHI/Semantics/SIOObserverRefinementLatticeAdapterExact.agda": [
        "sioPairedObserverCanonicalStrictRefinements :",
        "Crosswalk.coreStrictToLattice",
    ],
    "DASHI/CoarseFineFabricEverything.agda": [
        "import DASHI.Core.CanonicalSpineDependencyAtlasExact",
        "import DASHI.Core.ObserverRefinementLatticeExact",
        "import DASHI.Core.ObserverRefinementOrientationCrosswalkExact",
        "import DASHI.Core.ObserverIncomparabilityCrosswalkExact",
        "import DASHI.Core.KernelConsumerDescentFactorisationCrosswalkExact",
        "import DASHI.Core.ConsumerResidualRepairCrosswalkExact",
        "import DASHI.Core.ConsumerObserverJoinResidualCrosswalkExact",
        "import DASHI.Core.ReopenableConsumerInterventionCrossDomainRegression",
        "import DASHI.Core.ContextIndexedGovernedObservationExact",
        "import DASHI.Core.ResidualObserverDependencyExact",
        "import DASHI.Core.ResidualObserverDependencyProjectionAdapterRegression",
        "import DASHI.Core.DeclaredScenarioRobustnessExact",
        "import DASHI.Core.RequiredObserverAxisJoinAdequacyExact",
        "import DASHI.Core.RequiredObserverAxisJoinCanonicalPairRegression",
        "import DASHI.Core.BoundedNegativeSearchExact",
        "import DASHI.Core.MultipartSameObjectReconstructionExact",
        "import DASHI.Core.FrozenHeldOutRepairRefinementExact",
        "import DASHI.ComputerScience.RSA260MultipartReconstructionSpineExact",
        "import DASHI.Semantics.SIOObserverRefinementLatticeAdapterExact",
    ],
}

ESCAPED_AGDA_KEYWORD = re.compile(
    r"^\s*\\(?:data|record|module|import|open|postulate)\b", re.MULTILINE
)
OBVIOUS_PLACEHOLDER = re.compile(r"^\s*postulate\b|\{![^}]*!\}", re.MULTILINE)


def fail(message: str) -> None:
    raise SystemExit(message)


def read(rel: str) -> str:
    path = ROOT / rel
    if not path.is_file():
        fail(f"required #902 spine file missing: {rel}")
    text = path.read_text(encoding="utf-8")
    escaped = ESCAPED_AGDA_KEYWORD.search(text)
    if escaped:
        fail(f"escaped Agda keyword in {rel}: {escaped.group(0)!r}")
    placeholder = OBVIOUS_PLACEHOLDER.search(text)
    if placeholder:
        fail(f"obvious trust escape/placeholder in {rel}: {placeholder.group(0)!r}")
    return text


def main() -> None:
    texts = {rel: read(rel) for rel in REQUIRED_FILES}
    for rel, needles in EXPECTED.items():
        text = texts[rel]
        for needle in needles:
            if needle not in text:
                fail(f"missing required #902 spine symbol/import in {rel}: {needle}")
    print("coarse/fine canonical spine extension static contract: OK")


if __name__ == "__main__":
    main()
