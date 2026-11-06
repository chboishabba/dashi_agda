#!/usr/bin/env python3
"""Exact-head source-identity / honest-status regression for YM CMP119/116/122.

This checker intentionally cannot claim to prove an analytic estimate or pass
Agda. It blocks repo edits that orphan the selected source-weld symbols or
silently relabel conditional physics as already established.
"""
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
P = "DASHI/Physics/YangMills/"
OWNERS = {
    "CMP119_beta_history": ("Balaban1989BetaDrivenCompleteDensityFlowExact.agda",
        ("betaDrivenCompleteDensityFlow", "sourceCouplingIsBetaHistoryCoupling")),
    "CMP119_116_local_potential": ("BalabanBetaDrivenDensityToCMP109116CarrierRound108Exact.agda",
        ("asCMP109116Continuation", "cmp109PotentialIsLiteralBetaDrivenDensityPotential",
         "densityPotentialIsLocalizedCompositeSum")),
    "CMP122_published_UV": ("BalabanPublishedUVStabilityNonlinearRGCoreExact.agda",
        ("activeScaleInvariantFromPublishedCore",
         "literalPhysicalStateToPublishedRGCarrierLevel = conditional")),
    "CMP119_anchored_expectation": ("BalabanCMP119AnchoredNormalizedExpectationSourceExact.agda",
        ("CMP119LocalInsertionDictionary",
         "cmp119RepositoryLocalInsertionDictionaryLevel = conditional")),
    "CMP122_boundary": ("BalabanCMP119CMP122BoundaryReinjectionSourceExact.agda",
        ("CMP122BoundaryReinjectionStep",
         "cmp119CMP122BoundaryRepositoryDictionaryLevel = conditional")),
    "CMP116_mixed_source": ("BalabanCMP116LiteralTrajectorySourceRound342Exact.agda",
        ("LiteralTrajectoryCMP116Source",
         "literalSelectedDifferentiatedLocalization")),
    "CMP116_R344_shared": ("BalabanCMP116SharedMarkedDirectCalibrationRound344Exact.agda",
        ("SharedMarkedDirectCMP116Source",
         "asLiteralTrajectoryCMP116Source",
         "sharedMarkedEnvelopeBelowSpectrumEnvelope",
         "round344LiteralSelectedLocalizationLevel = conditional")),
    "CMP116_R342_R467": ("BalabanCMP116LiteralTrajectoryToPublishedLiteralR467Exact.agda",
        ("asPublishedLiteralSelectedLocalization",
         "sharedMarkedDirectAsPublishedLiteralSelectedLocalization")),
    "CMP116_R467_finite": ("BalabanCMP116PublishedLiteralSelectedRound467Exact.agda",
        ("finiteConnectedCovarianceLocalization",
         "literalRound467PublishedLiteralSelectedLocalizationLevel = conditional")),
    "CMP116_R482_gap": ("BalabanCMP116PublishedLiteralRateToGapRound482Exact.agda",
        ("publishedLiteralAndLocalRateBuildPositiveTransferGap",
         "arbitraryPositiveCandidateGapTokenRequired = false")),
    "CMP119_116_normalized_derivative": (
        "BalabanCMP116119NormalizedExpectationDerivativeRound281Exact.agda",
        ("round281LiteralObservablePairToSourceDirectionsLevel = conditional",
         "covarianceMagnitudeIsPublishedShell")),
    "CMP122_reflection_crossing": ("BalabanCMP122ROperationReflectionSupportCutExact.agda",
        ("rOperationCrossingEquation1100",
         "cmp122ROperationCrossingKernelRPLevel = conditional")),
    "ORIGINAL_WILSON_FINITE_JET": ("YMClayOriginalWilsonFiniteTwoSourceJetExact.agda",
        ("originalWilsonDensityIsSelectedWilson",
         "originalWilsonPartitionIsSelectedProductHaar",
         "originalWilsonFiniteIntegrationLaws",
         "originalWilsonUnitNumeratorIsPartition",
         "originalWilsonInsertionNumeratorAdd",
         "originalWilsonExpectationOfUnitIsOne",
         "originalWilsonNormalizedJet",
         "originalWilsonLiteralJetDirections",
         "originalWilsonMixedJetIsSameFiniteCovariance",
         "originalWilsonMixedJetIsOriginalConnectedCumulant")),
}
WELD = P + "YMClayCMP119122116SelectedProducerWeldExact.agda"
TERMS = (
    "cmp119122BetaAndCMP116PotentialSameSource",
    "sameLiteralR342SourceFiniteCovarianceDecay",
    "sameLiteralR342SourceYieldsR479TransferGap",
    "sameLiteralR342AndLocalRateYieldsGap",
    "sameOriginalSharedMarkedHalfRateFiniteDecay",
    "sameOriginalSharedMarkedHalfRateYieldsGap",
)
DOC = "Docs/physics/YMClayCMP119116122OriginalSameSourceMaxCut20261106.md"
WORKFLOW = ".github/workflows/ym-native-maxcut-exact-agda.yml"
ROOT_IMPORT = "DASHI/Unified/BalabanRGTOERegression.agda"

def text(path):
    file = ROOT / path
    if not file.is_file():
        raise AssertionError(f"MISSING original source: {path}")
    return file.read_text(encoding="utf-8")

def require(s, needle, label):
    if needle not in s:
        raise AssertionError(f"source drift: {label} missing {needle}")

def main():
    for label, (file, names) in OWNERS.items():
        source = text(P + file)
        for name in names:
            require(source, name, label)
    actual = text(WELD)
    require(actual, "{-# OPTIONS --safe #-}", "new weld safe")
    for term in TERMS:
        require(actual, term + " :", "exact theorem term " + term)
    if re.search(r"\bpostulate\b|\bprimTrustMe\b|\btrustMe\b|\{!|\bTERMINATING\b",actual):
        raise AssertionError("weld added a source-local trust escape")
    require(actual, "R344.asLiteralTrajectoryCMP116Source source", "canonical shared half-rate source")
    require(actual, "Bridge.asPublishedLiteralSelectedLocalization source",
            "single selected source")
    require(actual, "R482.publishedLiteralAndLocalRateBuildPositiveTransferGap",
            "positive energy derived by existing rate semantics")
    require(text(ROOT_IMPORT),
            "import DASHI.Physics.YangMills.YMClayCMP119122116SelectedProducerWeldExact",
            "canonical regression root")
    wf = text(WORKFLOW)
    require(wf,"$AGDA " + WELD,"Agda CI actual typecheck")
    jet = P + "YMClayOriginalWilsonFiniteTwoSourceJetExact.agda"
    require(text(ROOT_IMPORT),
            "import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact",
            "original finite jet regression root")
    require(wf,"$AGDA " + jet,"original Wilson finite jet Agda CI")
    require(wf,"- '" + jet + "'","original Wilson finite jet CI trigger")
    test = "scripts/check_ym_original_wilson_two_source_jet_reference.py"
    require(wf,"python3 " + test,"original finite jet exact reference CI")
    require(wf,"- '" + test + "'","original finite jet reference trigger")
    require(text(test), "changed_measure_negative_control",
            "two-marked BIDI negative control")
    require(wf,"- '" + WELD + "'","Agda CI trigger")
    document = text(DOC)
    for item in ("Y.01.","Y.02.","Y.03.","Y.04.","BalabanCMP116119NormalizedExpectationDerivativeRound281Exact",
                 "BalabanCMP122ROperationReflectionSupportCutExact"):
        require(document,item,"physical maxcut ledger")
    try:
        head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()
    except (OSError, subprocess.CalledProcessError):
        head="not a git checkout"
    print(json.dumps({
      "status":"PASS_SOURCE_IDENTITY_NOT_PHYSICAL_PROOF",
      "head":head, "golden_owners":len(OWNERS), "source_written_weld_terms":len(TERMS),
      "physical_same_object_theorem_witness":"NOT_TESTED",
      "agda_kernel_receipt":"SEPARATE_REQUIRED"
    },indent=2))

if __name__=="__main__": main()
