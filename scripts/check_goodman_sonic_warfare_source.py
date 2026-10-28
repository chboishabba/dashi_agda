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
        "jointObserverDoesNotIdentifyWholeWorld",
        "fullObserverStrictlyRefinesJointObserver",
        "fullObserverSeparatesToyWorlds",
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
