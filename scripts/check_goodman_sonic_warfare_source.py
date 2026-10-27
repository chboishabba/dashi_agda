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
    for owner in [
        "DASHI.Core.AttributedSourceCore",
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
        for m in re.finditer(r"(?m)^\\|\\s*(\\d+)\\s*\\|\\s*(\\d+)\\s*\\|", doc)
    ]
    require(len(chapter_rows) == 34, "must have 34 printed-page rows")
    owners = [
        int(s) for s in re.findall(r"(?m)^\\s+chapter(\\d{2})\\s*:\\s*SonicChapter$", module)
    ]
    require(owners == list(range(1, 35)), "Agda constructors must be exactly chapter01..34")
    pages = [
        (int(ch), int(page)) for ch, page in re.findall(
            r"(?m)^chapterPrintedPage chapter(\\d{2}) = (\\d+)$", module)
    ]
    require(pages == chapter_rows, "Agda printed start pages must match source table exactly")
    for field in ("chapterTitle", "chapterTheme", "chapterStatus"):
        matches = [int(ch) for ch in re.findall(
            rf"(?m)^{field} chapter(\\d{{2}}) =", module)]
        require(matches == list(range(1, 35)), f"missing exhaustive {field} mapping")
    require(
        "sourceCitationDoesNotPromote validation =" in module
        and "Attr.attributedSourceAtlasReceiptNonPromoting goodmanSources validation" in module,
        "source attribution non-promotion must reuse inherited owner"
    )
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
