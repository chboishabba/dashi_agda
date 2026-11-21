#!/usr/bin/env python3
"""Run existing ORIGINAL #1444 CMP119/122/116 and R445 source regressions.

No parallel YM theory or external numerical model. Fail closed on missing
master source owners or missing exact theorem names. Original tests own
the actual mathematical regressions; this file composes their receipts.
It does NOT run Agda or assert a physical mass gap.
"""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OWNERS = {
    "DASHI/Physics/YangMills/YMClayCMP119122116SelectedProducerWeldExact.agda": [
        "cmp119122BetaAndCMP116PotentialSameSource",
        "sameOriginalSharedMarkedHalfRateFiniteDecay",
        "sameOriginalSharedMarkedHalfRateYieldsGap",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact.agda": [
        "originalVariableN3IsNativeR445FineMeasure",
        "originalN3LiteralMixedLogJetIsActualR320PushforwardCovariance",
    ],
    "DASHI/Physics/YangMills/YMClayWilsonWEXTSelectedDistanceNonVacuityExact.agda": [
        "universalTimeForEveryDistanceIsImpossible",
        "with universal",
        "... | ()",
    ],
    "DASHI/Physics/YangMills/BalabanLiteralWilsonMarkedLocalizationSourceExact.agda": [
        "(selectedPhysicalDistance : Observable → Observable → Nat)",
        "selectedPhysicalDistance left (timeTranslate right time) ≡ time",
        "WilsonWEXTDownstreamSemantics dataSet (physicalDistance source)",
    ],
    "DASHI/Physics/YangMills/BalabanLiteralTwoWilsonR556CompletionExact.agda": [
        "Downstream.WilsonWEXTDownstreamSemantics dataSet physicalDistance",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalWilsonMarkedOS1AllTimesProducerWeldExact.agda": [
        "originalWEXTDownstreamFromOS1",
        "selectedOriginalMarkedDistanceIsEuclideanTime",
        "Marked.literalMarkedLocalizationCompilesToR556",
        "originalMarkedOS1CompilesToR556",
        "originalMarkedOS1ContinuumWilsonClustering",
        "originalMarkedOS1AllPairsTimes",
        "originalMarkedOS1SameSpectrumClustering",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.agda": [
        "originalFineCanonicalBlockedNumeratorEqualsPhysicalEffective",
        "originalCanonicalBlockedNormalizedEqualsPhysicalEffective",
        "sourceSortedBlockIsOriginalPairs",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalWilsonPhysicalF19PartitionExact.agda": [
        "originalFinePhysicalPartitionEqualsActualEffectivePartition",
        "originalPhysicalF19TwoMarksNormalizeByCanonicalPartition",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalF19CanonicalConnectedWilsonBIDIExact.agda": [
        "originalF19CanonicalMomentEqualsPhysical",
        "originalCanonicalF19ConnectedCovarianceSamePhysical",
        "cong₂ _-ℝ_",
        "cong₂ _*ℝ_",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalF19R445EveryLinkValueBIDIExact.agda": [
        "originalAllOriginalLinkValuesPreserved",
        "originalEveryCanonicalVectorAgreesWithR445",
        "originalEverySortedValueConsumerAgrees",
        "Labels.originalF19Complete1024LabelOrderMatchesR445",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalF19R445ActualSortedVectorBIDIExact.agda": [
        "originalF19TargetVectorValuesAreR445",
        "originalPhysicalF19ActualSortIsOriginalR445Codec",
        "originalEveryActualSortedWilsonConsumerAgrees",
        "Sorted.actualPairSpectatorReindexEveryOriginalVector",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalF19R445Full1024LabelsP0Exact.agda": [
        "originalF19SelectedPrefixMatchesR445",
        "originalF19Original896SpectatorsMatchR445",
        "originalF19Complete1024LabelOrderMatchesR445",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalF19NativeR445SelectedOrderBIDIExact.agda": [
        "originalF19PairListIsNativeR445Parity",
        "originalParityPairsAreNativeR445SelectedEnumeration",
        "originalF19Selected128AreNativeR445Selected128",
        "OriginalParityWeld.originalR445NativeFirstBondIsParity",
        "OriginalParityWeld.originalR445NativeSecondBondIsParity",
    ],
    "DASHI/Physics/YangMills/YMClayR445OriginalAxialBondParityInjectiveExact.agda": [
        "coord : Bit → Bit → Quad",
        "coarse : Quad → Bit",
        "phase : Quad → Bit",
        "originalR445SelectedFineBond",
    ],
    "DASHI/Physics/YangMills/YMClayR445OriginalNativeParityPairWeldExact.agda": [
        "originalR445NativeOriginIsEvenSite",
        "originalR445EvenSiteOneStepIsOddPhase",
        "originalR445NativeBlockAgreesExplicitParity",
    ],
    "DASHI/Physics/YangMills/YMClayR445CanonicalBondPermutationCodecExact.agda": [
        "originalR445ResidualBondEnumeration",
        "originalR445PairResidualFinite",
        "originalR445PairResidualComplete",
    ],
    "DASHI/Physics/YangMills/YMClayE1VariableCutoffCylinderLimitExact.agda": [
        "record ActualVariableCutoffCylinderFamily",
        "originalWilsonConverges",
        "continuumExpectation",
    ],
    "DASHI/Physics/YangMills/YMClayE1TimeKResidualCylinderWaveTransportExact.agda": [
        "timeKOriginalCylinder",
        "timeKOriginalCylinderRetainsResidual",
        "timeKOriginalWilsonExpectation",
        "timeKOriginalContinuumExpectation",
        "timeKOriginalFiniteToContinuum",
        "MDL.join-split",
        "E1.originalWilsonConverges",
    ],
    "DASHI/Physics/YangMills/YMClayR445TimeKResidualHyperfabricExact.agda": [
        "OriginalCodec.coarse",
        "OriginalCodec.phase",
        "OriginalCodec.coord",
        "originalNativeBlockOriginIsSelectedGeometry",
        "originalAllFineBondSelectedResidual",
        "oneFineStepKeepsCarryAndResidual",
        "oddFineStepCannotFactorThroughCoarseOnly",
        "twoFineStepsExactlyDescend",
        "waveZeroIsNotDeleted",
        "indexedZeroModeIsExactFiniteZeroWave",
        "timeKScaleResidualRoundTrip",
    ],
    "DASHI/Physics/YangMills/YMClayR445SelectedTimeReflectionForwardExact.agda": [
        "selectedNativeSiteTimeSquare",
        "selectedFineSiteReflectShiftDihedral",
        "selectedCoarseSiteShiftHasPeriodTwo",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalWilsonOS1R556R281CommutingSquareExact.agda": [
        "originalWilsonTimeTranslationSquare",
        "originalFiniteCovarianceSquare",
        "originalContinuumCovarianceSquare",
        "originalSourceFiniteContinuumConverges",
        "originalOS1SquareEndsInSameR281Spectrum",
        "originalSelectedSourceDistanceTime",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalWilsonAllTimesOS1R556R281BIDIExact.agda": [
        "originalAllTimesWilsonTests",
        "originalAllTimesSourceCovarianceConverges",
        "originalAllTimesSourceContinuumHalfRate",
        "originalAllWilsonPairsTimesTests",
        "originalAllWilsonPairsTimesConverge",
        "SameOSAllWilsonPairsTimesSpectrum",
        "indexForUsesSamePairAndTime",
        "originalAllWilsonPairsTimesSameR281Correlation",
        "originalAllWilsonPairsTimesSameR281SpectrumHasClustering",
        "SameOriginalOS1R556TimeGeometry",
        "originalWilsonSourceDistanceIsSameOS1Time",
        "R556.indexedAsContinuumClustering",
        "R332.supportDistanceIsTime",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalR445ReflectedWordCMP116BIDIExact.agda": [
        "originalSameFineSourceN3",
        "originalCenteredReflectedOSIsOriginalR320",
        "originalMixedJIsSameCenteredReflectedOS",
        "Source.originalN3LiteralMixedLogJetIsActualR320PushforwardCovariance",
        "R320.connectedCovarianceOfActualPushforward",
    ],
    "DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda": [
        "YMClayR445SelectedTimeReflectionForwardExact",
        "YMClayOriginalR445ReflectedPointwiseWordWeldExact",
        "YMClayOriginalR445ReflectedWordCMP116BIDIExact",
        "YMClayOriginalWilsonAllTimesOS1R556R281BIDIExact",
        "YMClayWilsonWEXTSelectedDistanceNonVacuityExact",
        "YMClayOriginalWilsonMarkedOS1AllTimesProducerWeldExact",
        "YMClayOriginalWilsonOS1R556R281CommutingSquareExact",
        "YMClayR445TimeKResidualHyperfabricExact",
        "YMClayE1TimeKResidualCylinderWaveTransportExact",
        "YMClayOriginalF19CanonicalConnectedWilsonBIDIExact",
        "YMClayOriginalF19NativeR445SelectedOrderBIDIExact",
        "YMClayOriginalF19R445Full1024LabelsP0Exact",
        "YMClayOriginalF19R445EveryLinkValueBIDIExact",
        "YMClayOriginalF19R445ActualSortedVectorBIDIExact",
    ],
    "DASHI/Physics/YangMills/YMClayNativeR445TemporalReversalExact.agda": [
        "originalSUNTimeReversalTwoLink",
    ],
    "DASHI/Physics/YangMills/YMClayNativeSideFourTwoLinkPairSameObjectExact.agda": [
        "originalSUNBlockIsLiteralTwoLinkProduct",
    ],
    "DASHI/Physics/YangMills/BalabanCMP119AnchoredNormalizedExpectationSourceExact.agda": [
        "CMP119LocalInsertionDictionary",
        "cmp119RepositoryLocalInsertionDictionaryLevel = conditional",
    ],
    "DASHI/Physics/YangMills/BalabanCMP119CMP122BoundaryReinjectionSourceExact.agda": [
        "CMP122BoundaryReinjectionStep",
        "cmp119CMP122BoundaryRepositoryDictionaryLevel = conditional",
    ],
    "DASHI/Physics/YangMills/BalabanCMP122ROperationReflectionSupportCutExact.agda": [
        "rOperationCrossingEquation1100",
        "cmp122ROperationCrossingKernelRPLevel = conditional",
    ],
    "DASHI/Physics/YangMills/YMClayD1OriginalFullWilsonSmallLargeFieldExact.agda": [
        "originalFullWilsonUniformGeometricClustering",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalWilsonNativeOSPullbackExact.agda": [
        "NativeBlockReflectsExactly",
        "originalR445OSReflectionPositiveFromSameFineWilson",
    ],
    "DASHI/Physics/YangMills/YMClayOriginalR445ReflectedPointwiseWordWeldExact.agda": [
        "original1444SUNReversedTwoLinkIsInverseNativeBlock",
        "originalActualPlaquetteWordsReflectThroughR445",
        "originalWordOSQuadraticIsNativeR445",
    ],
}
CHECKS = [
    "scripts/check_ym_cmp119116122_same_source_contract.py",
    "scripts/check_ym_r445_time_reflection_q8_20261106.py",
    "scripts/check_ym_r445_original_wilson_words_reflection.py",
    "scripts/check_ym_original_r445_os1_translation_commuting_square.py",
    "scripts/check_ym_r445_time_k_residual_hyperfabric.py",
    "scripts/check_ym_original_f19_r445_selected_residual_source.py",
    "scripts/check_ym_f19_r445_full1024_labels_p0.py",
]

def main():
    for name, symbols in OWNERS.items():
        file = ROOT / name
        if not file.is_file():
            raise SystemExit(f"FAIL: missing original master owner: {name}")
        text = file.read_text(encoding="utf-8")
        for symbol in symbols:
            if symbol not in text:
                raise SystemExit(f"FAIL: source has moved: {name}: {symbol}")
        if name.endswith("BalabanLiteralWilsonMarkedLocalizationSourceExact.agda"):
            if "(physicalDistance : Observable → Observable → Nat) →" in text:
                raise SystemExit("FAIL: impossible universal physical metric quantifier reintroduced")
        print("PASS source owner:", name)
    for name in CHECKS:
        file = ROOT / name
        if not file.is_file():
            raise SystemExit(f"FAIL: original reference missing: {name}")
        print("RUN", name, flush=True)
        subprocess.run([sys.executable, str(file)], cwd=ROOT, check=True)
    print("PASS source identity + finite non-Abelian tests")
    print("KERNEL LOCAL: bash scripts/check_ym_original_rg_p0_kernel.sh")
    print("OPEN native Agda geometry kernel, original physical analytic CMP estimates, "
          "fine published RP/source identification, E1/D1/D2/N1/G1")
if __name__ == "__main__":
    main()
