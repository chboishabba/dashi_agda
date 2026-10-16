#!/usr/bin/env python3
"""Structural audit for the Monster/C3/369 chemistry/entropy/gravity max-cut.

This is not an Agda typecheck and not physical validation. It checks exact
finite arithmetic plus the presence of the current representation-native
promotion and non-promotion markers.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, *needles: str) -> None:
    """Require every marker string to occur in one repository file."""
    text = (ROOT / path).read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            raise AssertionError(f"missing {needle!r} in {path}")


def check(name: str, condition: bool) -> None:
    """Raise explicitly when a finite arithmetic regression fails, even under -O."""
    if not condition:
        raise AssertionError(f"failed arithmetic check: {name}")


def main() -> None:
    """Run finite arithmetic and structural-marker regression checks."""
    check("ternary residual 53", (3 + 3) * 9 - 1 == 53)
    check("extended ternary 71", (3 + 3 + 2) * 9 - 1 == 71)
    check("Monster degree two ways", 53 + 3 * 65610 == 196883 == 47 * 59 * 71)
    check("zeta basis-label dimension", 729 * 90 == 65610)
    check("three regular fibres", 3 * 65610 == 196830)
    check("regular plus residual", 196830 + 53 == 196883)
    check("proton-affinity difference", 8536 - 4223 == 4313)
    check("published STO-3G FCI-HF gap", 555245 - 554554 == 691)
    check("released SCI energy encoding", 55517555010 / 1_000_000_000 == 55.51755501)
    check("released FCI-run energy encoding", 55519414318 / 1_000_000_000 == 55.519414318)
    check("basis-label normalization numerator", 1 * 65610 == 65610)

    require(
        "DASHI/Physics/Chemistry/AmmoniaC3RegularRepresentationExact.agda",
        "ammoniaA1PlusEGeneratorCancels",
        "monsterRegularBlockMultiplicity",
        "monsterResidualMultiplicity",
        "sameRegularC3MotifCreatesMonsterModule",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaMonster3BC3QuotientLiftExact.agda",
        "nh3MonsterRoundTrip",
        "monsterNH3RoundTrip",
        "nh3MonsterMultiplicationIntertwines",
        "nh3MonsterInversionIntertwines",
        "nh3MonsterFourierRowsIntertwine",
        "quotientIntertwinerCreatesStateIntertwiner",
    )
    require(
        "DASHI/Moonshine/Monster3BWZetaBasisVectorRecognitionCorrectionExact.agda",
        "ActualZetaBasisRecognition",
        "ActualMultiplicityBasisRecognition",
        "WZetaBasisVectorRecognition",
        "finiteBasisLabelsDoNotBecomeAllVOAStates",
    )
    require(
        "DASHI/Moonshine/Monster3BProofRelevantRecognitionHardeningExact.agda",
        "PaidSchrodingerIsActualHZeta",
        "PaidActualLinearMultiplicityHomSpace",
        "PaidActualZetaBasisRecognition",
        "PaidWZetaBasisVectorRecognition",
        "typedObligationDoesNotCreateRecognitionWitness",
    )
    require(
        "DASHI/Moonshine/Monster3BHZetaCharacterTransportCompilerExact.agda",
        "HZetaCharacterTransport",
        "compiledEquivariantIso",
        "compiledPaidHZetaRecognition",
        "actualHZetaSameObjectInhabitedHere",
    )
    require(
        "DASHI/Moonshine/Monster3BWholeCharacterIsotypicAssemblyLeanReceiptExact.agda",
        "IsIsotypicOfType.linearEquiv_fun",
        "classifierToIsotypicAssemblySourceWritten",
        "postRecognitionCopyCountCompilerSourceWritten",
        "actualMonsterSimpleTypeClassifierPaid",
        "actualCopyCountNinetyPaidByThisReceipt",
    )
    require(
        "DASHI/Moonshine/Monster3BLinearActionProofRelevantHardeningExact.agda",
        "PaidWeightTwoLinearActionBridge",
        "PaidLinearSingleActionProducer",
        "actualPaidWeightTwoBridgeInhabitedHere",
        "actualPaidLinearZetaRestrictionInhabitedHere",
    )
    require(
        "DASHI/Moonshine/Monster3BRepresentationNativeCurrentMaxCutExact.agda",
        "genericIsotypicAssemblySourceWritten",
        "postRecognitionCopyCountCompilerSourceWritten",
        "actualPaidLinearZetaRestriction",
        "actualSimpleTypeClassifier",
        "actualWholeSectorIsotypicEquivalence",
        "actualMultiplicityHomEvaluation",
        "selected3BLinearRetraction",
        "selected3BProjectedAction",
        "finiteBasisChartIsWholeLinearStateRecognition",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaMonster3BRepresentationNativeCorrectionExact.agda",
        "Native369ActualBasisChart",
        "PhysicalNH3MonsterBasisAttachment",
        "actualBasisToNative369",
        "native369ToActualBasis",
        "finiteChartDoesNotCreateWholeVOAStateBijection",
        "phaseBijectionDoesNotCreatePhysicalAttachment",
        "physicalNH3ToMonsterLinearStatePaid",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaMonster3BPhaseQuotientNonFactorabilityExact.agda",
        "phaseCannotRecoverModelBasis",
        "phaseCannotRecoverWeightPosition",
        "phaseCannotRecoverMultiplicityCoordinate",
    )
    require(
        "DASHI/Physics/Chemistry/Atomic369Kernel6HeisenbergBridgeExact.agda",
        "kernel6RoundTrip",
        "x6RoundTrip",
        "physicalNH3StateToKernel6AssignmentPaid",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaMonster3BRefinedStateLiftCompilerExact.agda",
        "refinedModelRoundTrip",
        "modelRefinedRoundTrip",
        "actualBasisRecognitionLiftCompilerPaid",
        "wholeLiteralSectorFiniteLiftCompilerPaid",
    )
    require(
        "DASHI/Physics/Chemistry/AmmoniaMonster3BNative369FineCarrierExact.agda",
        "native369RoundTrip",
        "model369RoundTrip",
        "native369FiniteChartIsBasisLabelChart",
        "native369FiniteChartIsWholeVOAStateBijection",
        "physicalNH3StateToNative369FineCoordinatePaid",
    )
    require(
        "DASHI/Physics/Closure/MonsterC3Native369ConsumerSufficiencyExact.agda",
        "BasisLabelState",
        "phaseObserverNotSufficientForBasisLabel",
        "native369ObserverSufficientForBasisLabel",
        "finiteBasisLabelConsumerIsWholeLinearVOAStateConsumer",
    )
    require(
        "DASHI/Physics/Closure/MonsterC3Native369ZetaCountingEnsembleExact.agda",
        "zetaBasisLabelCount",
        "65610",
        "native369ZetaCountingEnsemble",
        "finiteBasisLabelsAreAllLinearWZetaStates",
        "nativeUniformCountingIsPhysicalThermalEnsemble",
    )
    require(
        "DASHI/Reasoning/Trialectic369Selected3BProjectionChoiceIndependenceExact.agda",
        "projectedActionIndependentOfRetraction",
        "SelectedEqualsIntrinsicConstituentAction",
        "actualSourceRetractionConstructedHere",
        "actualMonsterSameActionConstructedHere",
    )
    require(
        "DASHI/Physics/Closure/MonsterC3RepresentationNativeTerminalMaxCutExact.agda",
        "native369FiniteCarrierScopedToBasisLabels",
        "native369FiniteCarrierIsWholeVOAStateCarrier",
        "genericIsotypicAssemblySourceWritten",
        "postRecognitionCopyCountCompilerSourceWritten",
        "actualMonsterSimpleTypeClassifierPaid",
        "actualWholeSectorIsotypicEquivalencePaid",
        "actualSZetaHomEvaluationPaid",
        "selected3BProjectionChoiceIsIndependentBlocker",
        "count65610IsFiniteBasisLabelCount",
        "count65610IsCardinalityOfAllLinearWZetaStates",
        "countingMeasureIsPhysicalEntropy",
        "scalarEntropyDensityDeterminesEinsteinSource",
        "monsterSymmetryOfObserved3Plus1UniversePaid",
        "genericIsotypicAssemblyIsStillAResearchLeaf",
    )
    require(
        "DASHI/Physics/Closure/MonsterC3ZetaEntropyGravityCrossPollinationExact.agda",
        "native369FiniteBasisLabelChartPaid",
        "native369FiniteChartIsWholeLinearWZetaStateBijection",
        "genericIsotypicAssemblySourceWritten",
        "actualPaidLinearZetaRestriction",
        "actualSimpleTypeClassifier",
        "physicalNH3ToMonsterLinearStatePaid",
        "finiteBasisLabelsAreAllLinearWZetaStates",
    )
    require(
        "DASHI/Physics/Closure/EntropyGravityIntertwinerBoundaryExact.agda",
        "scalarEntropyDensityDeterminesStressTensor",
        "entropyObservableAloneDerivesEinsteinDynamics",
    )

    print("monster/C3/369 chemistry/entropy/gravity structural audit: ok")
    print("NH3 A1+E = one regular-C3 block; Monster bulk uses 65610 blocks + residual 53")
    print("phase quotient: exact for phase consumers, insufficient for finite basis-label identity")
    print("native369 <-> X6 x Fin90 is a 65610 basis-label chart, not all W_zeta vectors")
    print("representation-native target: H_zeta x Hom_E(H_zeta,W_zeta) <-> W_zeta")
    print("generic fixed-phase H_zeta iso + isotypic assembly + post-recognition copy-count machinery are already available")
    print("live Monster leaves are same-object linear restriction/classifier/Hom plus global retraction/same-action")
    print("uniform 1/65610 counting is mathematical basis-label counting only")
    print("physical ensemble/entropy, Lorentzian tensor gravity, and observed 3+1D Monster symmetry remain unpaid")


if __name__ == "__main__":
    main()
