#!/usr/bin/env python3
"""Source-level only: Goodman Sonic Warfare coverage, reuse, and non-promotion.

This is NOT an Agda kernel/typecheck, not a human-subject experiment,
not a calibrated acoustics test, and not evidence for Kozyrev claims.
Run at exact checked repository head and record it separately from Agda.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "DASHI/Culture/GoodmanSonicWarfareExact.agda"
RHYTHM = ROOT / "DASHI/Culture/GoodmanSonicWarfareRhythmInterventionExact.agda"
TRANSPORT = ROOT / "DASHI/Culture/GoodmanSonicWarfareTransportExact.agda"
RATIONAL = ROOT / "DASHI/Culture/GoodmanSonicWarfareRationalInverseExact.agda"
STABILITY = ROOT / "scripts/check_goodman_inverse_stability_finite.py"
RIDGE = ROOT / "scripts/check_goodman_ridge_regularisation_finite.py"
DOC = ROOT / "Docs/papers/GoodmanSonicWarfare.md"
ROOTS = [
    ROOT / "DASHI/EverythingTOESymmetryResolved369.agda",
    ROOT / "DASHI/Unifier.agda",
    ROOT / "DASHI/Unified/Everything.agda",
    ROOT / "DASHI/Culture/Everything.agda",
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def check() -> None:
    module = MODULE.read_text(encoding="utf-8")
    doc = DOC.read_text(encoding="utf-8")
    rhythm = RHYTHM.read_text(encoding="utf-8")
    transport = TRANSPORT.read_text(encoding="utf-8")
    rational = RATIONAL.read_text(encoding="utf-8")
    stability = STABILITY.read_text(encoding="utf-8")
    ridge = RIDGE.read_text(encoding="utf-8")
    for owner in [
        "DASHI.Core.AttributedSourceCore",
        "DASHI.Core.SnowballAttributionProvenanceInvariantExact",
        "DASHI.Culture.GoodmanSonicWarfareRhythmInterventionExact",
        "DASHI.Culture.GoodmanSonicWarfareTransportExact",
        "DASHI.Core.QueryIndexedProjectionAdequacyExact",
        "DASHI.Physics.ObserverConditionedTransportBridge",
        "DASHI.Biology.BioacousticMultimodalLagFactorisationExact",
        "DASHI.Biology.BraidedEmotionEvidenceRegistry",
        "DASHI.Culture.CohnTechnostrategicDiscourseExact",
        "DASHI.Culture.PhilosophyClaimProvenanceHistoryBidiExact",
        "DASHI.Core.IntersectionalNonFactorability",
        "DASHI.Wikimedia.IbrahimSnowballSkepticismExpertiseTrustPropagandaBidiExact",
    ]:
        require(f"import {owner}" in module, f"missing canonical donor {owner}")
    for marker in [
        "10.7551/mitpress/7999.001.0001",
        "goodmanSources",
        "soundscapeComparatorSources",
        "acousticInverseSourceAtlas",
        "colettiDavisSchultz2025",
        "delaunayImperialeMoireau2026",
        "acousticInverseSourcesDoNotPromote",
        "zhangContextReview2025",
        "guoUrbanSoundscape2026",
        "isoNonAcousticContext2025",
        "isoSoundscapeAnalysis2025",
        "soundscapeComparatorsCannotPromote",
        "goodmanSnowballRole",
        "goodmanCitationDoesNotImportProof",
        "sourceCitationDoesNotPromote",
        "mirrorNameDoesNotDetermineMechanism",
        "acousticMirrorIsNotKozyrevReferent",
        "acousticFeaturesDoNotDetermineEveryResponse",
        "inaudibleIsNotUnrealised",
        "noCausalityFromLabel",
        "noPathogenFromMetaphor",
        "noSameObjectFromMirrorWord",
        "noEventFromFictionalDate",
        "sonicPropagandaIntentCannotDetermineTruth",
        "sonicSameContentCannotDetermineDeceptiveIntent",
        "signalAloneCannotDetermineContextualResponse",
        "contextAloneCannotDetermineContextualResponse",
        "jointSignalContextDeterminesSyntheticResponse",
        "allSonicChapters",
        "indexedChapterClaim",
    ]:
        require(marker in module, f"missing source/proof marker {marker}")
    require(not re.search(r"(?m)^\s*(postulate|{-#\s*TERMINATING\s*#-})", module),
            "new postulate or TERMINATING escape")
    chapter_ids = [
        int(m.group(1))
        for m in re.finditer(r"(?m)^\|\s*(\d+)\s*\|\s*\d+\s*\|", doc)
    ]
    require(chapter_ids == list(range(1, 35)), "chapter index must be exactly 1..34")
    chapter_rows = [
        (int(m.group(1)), int(m.group(2)))
        for m in re.finditer(r"(?m)^\|\s*(\d+)\s*\|\s*(\d+)\s*\|", doc)
    ]
    require(len(chapter_rows) == 34, "must have 34 printed-page rows")
    owners = [
        int(s) for s in re.findall(r"(?m)^\s+chapter(\d{2})\s*:\s*SonicChapter$", module)
    ]
    require(owners == list(range(1, 35)), "Agda constructors must be exactly chapter01..34")
    pages = [
        (int(ch), int(page)) for ch, page in re.findall(
            r"(?m)^chapterPrintedPage chapter(\d{2}) = (\d+)$", module)
    ]
    require(pages == chapter_rows, "Agda printed start pages must match source table exactly")
    for field in ("chapterTitle", "chapterTheme", "chapterStatus"):
        matches = [int(ch) for ch in re.findall(
            rf"(?m)^{field} chapter(\d{{2}}) =", module)]
        require(matches == list(range(1, 35)), f"missing exhaustive {field} mapping")
    require(
        "sourceCitationDoesNotPromote validation =" in module
        and "Attr.attributedSourceAtlasReceiptNonPromoting goodmanSources validation" in module,
        "source attribution non-promotion must reuse inherited owner"
    )
    # M1 finite four-state interaction must be total at source level.
    for label in (
        "signalOnly", "contextOnly", "jointSignalContext",
        "contextualResponse", "jointResponse",
    ):
        decls = re.findall(rf"(?m)^{label} (\w+) = ", module)
        require(len(decls) == 4 and len(set(decls)) == 4,
                f"M1 {label} must exhaust four distinct cases")
    require("IbrahimTrust.propagandaIntentCannotFactorTruthStatus" in module
            and "IbrahimTrust.falseContentCannotFactorDeceptiveIntent" in module,
            "M1/Ibrahim cross-pollination must remain owner-owned")
    for owner in (
        "DASHI.Core.QueryIndexedProjectionAdequacyExact",
        "DASHI.Core.IdentifiabilityActiveInformationExact",
        "DASHI.Core.SnowballAttributionProvenanceInvariantExact",
    ):
        require(f"import {owner}" in rhythm,
                f"R1/I1 must import existing owner {owner}")
    for marker in (
        "countCannotRecoverPhase",
        "phaseIsAdequateForPhase",
        "passiveObservationsDoNotIdentifyCausalModel",
        "logicalInterventionDistinguishesMechanisms",
        "addingControlledInterventionBreaksEquivalence",
        "sonicCitationCannotSupplyProof",
        "sonicCitationMustRetainSourceKind",
    ):
        require(marker in rhythm, f"missing rhythm/causal formalism {marker}")
    require(not re.search(r"(?m)^\s*postulate\b", rhythm),
            "new sonic rhythm/causal owner must not introduce postulates")
    sound_cases = re.findall(
        r"(?m)^soundReadout (\w+) (\w+) =", rhythm)
    require(len(sound_cases) == 6 and len(set(sound_cases)) == 6,
            "causal readout must cover six distinct design-by-model cases")
    require("Hernan" in doc or "Hernán" in doc,
            "source report should attribute causal inference authors")
    for owner in (
        "DASHI.Physics.ObserverConditionedTransportBridge",
        "DASHI.Core.QueryIndexedProjectionAdequacyExact",
        "DASHI.Core.ObserverRefinementLatticeExact",
        "DASHI.Core.RobustExperimentInferenceFrontierExact",
        "DASHI.Core.FrozenHeldOutRepairRefinementExact",
        "DASHI.Culture.GoodmanSonicWarfareRationalInverseExact",
    ):
        require(f"import {owner}" in transport,
                f"transport must import inherited theorem owner {owner}")
    require(not re.search(r"(?m)^\s*postulate\b", transport),
            "new finite transport owner must not add postulates")
    for name, expected in (
        ("applySource", 8),
        ("toyMicrophoneReadout", 8),
        ("sourceActivity", 4),
        ("toyMedium", 4),
        ("readAnswer", 8),
    ):
        matches = re.findall(rf"(?m)^{name} (.+?) =", transport)
        require(len(matches) == expected and len(set(matches)) == expected,
                f"transport {name} must enumerate {expected} unique cases")
    for theorem in (
        "toyTransportSystem",
        "sourceMonitorProjection",
        "jointReceiverAndSourceMonitor",
        "sourceMonitorAdequateForEmitterQuestion",
        "sourceMonitorStrictlyRefinesSelectedReceiver",
        "sonicFitDoesNotEstablishAdequacy",
        "sonicTrainingFitDoesNotPayHeldOutValidation",
        "Robust.sameFitDifferentAdequacy",
        "FrozenHeldOut.trainingFitDoesNotCreateHeldOutValidity",
        "jointObserverDoesNotIdentifyWholeWorld",
        "fullObserverStrictlyRefinesJointObserver",
        "fullObserverSeparatesToyWorlds",
        "sourceMonitorNotWorldSeparating",
        "mediumMonitorNotWorldSeparating",
        "receiverAndMediumNotWorldSeparating",
        "sourceAndMediumSeparatesAllFourWorlds",
        "fullObservationFactorsThroughParetoPair",
        "paretoPairFactorsThroughFullObservation",
        "recoverFullFromPareto",
        "forgetReceiverFromFull",
        "sameReceiverAndSourceReadingForDifferentMedia",
        "differentMediaInSilentWorlds",
        "Observer.strictPairRefinement",
        "sourceMonitorSeparatesSilentSourceCollision",
        "receiverProjectionAdequateForReceiverQuestion",
        "sourceActivityCollision",
        "sameReceiverReadoutCannotRecoverEmitterActivity",
        "sameSampleAtSelectedObserver",
        "toySourceOnVsOffObservable",
        "toySourceOnProducesSignalInTransmittingCase",
    ):
        require(theorem in transport, f"missing finite transport theorem {theorem}")
    # T4: Reject accidental partial case-splits in the full triple observer.
    full_cases = re.findall(
        r"(?m)^fullObserverSeparatesToyWorlds (\w+) (\w+) ", transport)
    require(len(full_cases) == 16 and len(set(full_cases)) == 16,
            "full observer must cover each of the sixteen ordered world pairs")
    require("Observer.strictPairRefinement" in transport,
            "T4 strict refinement must delegate to its original owner")
    # Comparator source identities and research/standard roles are explicit.
    for marker in (
        "10.1121/10.0036882",
        "10.1038/s42949-026-00482-2",
        "ISO/TS 16755-1:2025",
        "ISO/TS 12913-3:2025",
    ):
        require(marker in module and marker in doc,
                f"independent soundscape source not tracked in atlas and documentation: {marker}")
    require("Attr.attributedSourceAtlasReceiptNonPromoting" in module,
            "comparator sources cannot claim proof or empirical authority")
    # T5 Pareto: the separating two-observer pair closes all 4x4 cases.
    pairs = re.findall(
        r"(?m)^sourceAndMediumSeparatesAllFourWorlds (\w+) (\w+) ", transport)
    require(len(pairs) == 16 and len(set(pairs)) == 16,
            "Pareto source+medium separation must cover all sixteen world pairs")
    for theorem in (
        "fullObservationFactorsThroughParetoPair",
        "paretoPairFactorsThroughFullObservation",
    ):
        cases = re.findall(rf"(?m)^{theorem} (\w+) =", transport)
        require(len(cases) == 4 and len(set(cases)) == 4,
                f"{theorem} must cover four worlds")
    reconstructions = re.findall(
        r"(?m)^recoverFullFromPareto \((\w+) , (\w+)\) =", transport)
    require(len(reconstructions) == 4 and len(set(reconstructions)) == 4,
            "full observer reconstruction must have four pair cases")
    # T6: Exact-rational inverse diagnostics remain a synthetic finite
    # regression, and cannot claim any measured acoustics or kernel proof.
    for text in (
        "from fractions import Fraction as F",
        "determinant = F(1, n)",
        "assert hidden_error / measurement_error == n",
        "assert condition == 2*(n+1)",
        "two_channel_checks",
        "assert two_channel_checks == 24",
        '"not_verified": [',
        '"Agda kernel"',
        '"calibrated sound"',
    ):
        require(text in stability, f"missing exact-rational inverse check: {text}")
    for cited in (
        "T6 stability and genuinely measured evidence frontier",
        "RobustExperimentInferenceFrontierExact",
        "FrozenHeldOutRepairRefinementExact",
        "10.1038/s42949-026-00482-2",
    ):
        require(cited in doc, f"missing robustness provenance/documentation: {cited}")
    # T7: Exact rational algebra uses original ring solver and a
    # separately supplied nonzero inverse calibration certificate.
    for owner in (
        "Data.Rational.Tactic.RingSolver",
        "Data.Rational.Properties",
    ):
        require(f"import {owner}" in rational,
                f"rational adapter must reuse {owner}")
    for theorem in (
        "forwardTriangular",
        "recoverTriangular",
        "ringCancellation",
        "calibratedInverseRoundtrip",
        "ringPerturbation",
        "calibratedPerturbation",
        "twoChannelRingPerturbation",
        "calibratedTwoChannelPerturbation",
        "commonModeSecondCoordinateRecovers",
        "noisyTriangularPair",
        "calibratedFullPairPerturbation",
        "commonModePairRetainsFirstError",
        "ridgeSecond",
        "ridgeTwoChannelDecomposition",
        "ridgeBiasBalance",
        "ridgeNormalEquation",
    ):
        require(theorem in rational, f"missing T7 rational theorem {theorem}")
    require(rational.count("r * q ≡ 1ℚ") == 6,
            "all six calibrated inverse and full-pair theorems must retain calibration premise")
    require(not re.search(
        r"(?m)^\s*(?:postulate|{-#\s*(?:TERMINATING|NO_POSITIVITY_CHECK)\s*#-})",
        rational),
        "T7 has new postulate or trust escape")
    require("GoodmanSonicWarfareRationalInverseExact" in transport,
            "T7 rational proof must remain in the Goodman TOE import graph")
    for assertion in (
        "calibratedInverseRoundtrip",
        "calibratedPerturbation",
        "calibratedTwoChannelPerturbation",
        "Jacques Hadamard",
    ):
        require(assertion in doc, f"missing T7 proof/attribution memo {assertion}")
    # T9 ridge, inherited rational solver and independent source authors.
    for token in (
        "Coletti", "Davis", "Schultz", "10.1016/j.apacoust.2025.110756",
        "Delaunay", "Imperiale", "Moireau", "10.3934/ipi.2025043",
    ):
        require(token in module, f"missing independent inverse source attribution {token}")
    for token in (
        "from fractions import Fraction as Q",
        "assert checks == 72",
        "assert len(rows) == 18",
        "assert recovered - y == bias + gain*(second-first)",
        "assert (q*q + lam)*recovered == q*(b-a)",
    ):
        require(token in ridge, f"missing T9 finite diagnostic {token}")
    for token in (
        "T9 regularised inversion",
        "ridgeBiasBalance",
        "ridgeNormalEquation",
        "10.1016/j.apacoust.2025.110756",
        "10.3934/ipi.2025043",
    ):
        require(token in doc, f"missing T9 original attribution or scope {token}")
    require("Kozyrev" in doc and "Ibrahim" in doc and "Pinheiro dos Santos" in doc,
            "missing cross-domain/source priority cautions")
    for file in ROOTS:
        src = file.read_text(encoding="utf-8")
        require("import DASHI.Culture.GoodmanSonicWarfareExact" in src,
                f"missing root import: {file}")
    print("Goodman Sonic Warfare static source contract PASS")
    print("34 chapters indexed; 4 graph roots; existing proof donors; non-promotion markers")
    print("NOT CHECKED: Agda kernel, calibrated acoustics, historical events, human effects")


if __name__ == "__main__":
    check()
