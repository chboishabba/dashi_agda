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
