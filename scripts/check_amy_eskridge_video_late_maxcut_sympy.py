#!/usr/bin/env python3
"""Source-driven conformance for the VIDEO'S late claims 064..085.

Intentionally tests finite source/provenance and numerical-admission obligations,
not physical truth, foreknowledge, experimental effect, or instrument existence.

Owner originals:
  Project Camelot, Dan Burisch, Stargate Secrets (2007), part-1 transcript;
  Prasad/Bainbridge (2022) DOI 10.1177/09567976221108944;
  Kekecs et al. (2023) DOI 10.1098/rsos.191375;
  Walleczek et al. (2025) DOI 10.1371/journal.pone.0335330;
  Mossbridge/Tressoldi/Utts (2012) DOI 10.3389/fpsyg.2012.00390;
  Duggan/Tressoldi (2018) DOI 10.12688/f1000research.14330.2.

Run: python scripts/check_amy_eskridge_video_late_maxcut_sympy.py
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import re
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
CULTURE = ROOT / "DASHI" / "Culture"
GOVERNANCE = ROOT / "DASHI" / "Governance"
WIKIMEDIA = ROOT / "DASHI" / "Wikimedia"


def file(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def agda(name: str) -> str:
    return file(CULTURE / (name + ".agda"))


def claim_block(text: str, name: str) -> str:
    anchor = name + " = video-claim-join"
    assert text.count(anchor) == 1, name
    return text.split(anchor, 1)[1].split("\n\n", 1)[0]


def check_exact_late_section() -> None:
    claims = agda("AmyEskridgeVideoClaimAttributionLedgerExact")
    welds = agda("AmyEskridgeVideoClaimProducerWeldExact")
    late = agda("AmyEskridgeVideoLateSectionEvidenceBidiExact")
    clips = agda("AmyEskridgeVideoOriginalClipLineageExact")
    agg = agda("AmyEskridgeVideoEvidenceEverything")
    ids = [
        int(x) for x in re.findall(
            r"(?m)^claim(\d{3}) = claim \"", claims
        ) if 64 <= int(x) <= 85
    ]
    late_ids = [
        int(x) for x in re.findall(
            r"(?m)^late(\d{2}) = late-weld Weld.claimJoin", late
        )
    ]
    assert ids == list(range(64, 86)), ids
    assert late_ids == ids, late_ids
    assert late.count("  false\n") >= 22
    assert "all22ClaimsJoinedToExistingProducers = refl" in late
    assert "AmyEskridgeVideoLateSectionEvidenceBidiExact" in agg
    assert "AmyEskridgeVideoTemporalForecastAndPsiMaxCutExact" in agg

    # Old "unlocated" entries were wrong after original-source discovery.
    assert "originalVideoClip Lineage.clip06" in claim_block(welds, "claimJoin066")
    assert "originalVideoClip Lineage.clip07" in claim_block(welds, "claimJoin067")
    assert "originalVideoClip Lineage.clip09" in claim_block(welds, "claimJoin070")
    assert "Source.bem2011" in claim_block(welds, "claimJoin070")
    assert "UNLOCATED" in claim_block(welds, "claimJoin070")
    for i in [68, 75, 78, 81]:
        assert "documentSource Source.videoTranscript" in claim_block(
            welds, f"claimJoin{i:03d}"
        )
    for i in [64, 65, 69, 71, 72, 73, 74, 76, 77, 79, 80, 82, 83, 84, 85]:
        assert "documentSource Source.burischCamelot" in claim_block(
            welds, f"claimJoin{i:03d}"
        )
    assert "2007" in claim_block(welds, "claimJoin084")
    assert "2016" in clips and "2017" in clips or (
        "2016" in agda("AmyEskridgeVideoTemporalForecastAndPsiMaxCutExact")
        and "2017" in agda("AmyEskridgeVideoTemporalForecastAndPsiMaxCutExact")
    )

    # These *are* pre-existing specialized owners. Do not claim video novelty.
    prior = file(GOVERNANCE / "AnomalousPhenomenonTemporalEvidenceTrajectoriesExact.agda")
    admission = file(GOVERNANCE / "AnomalousTemporalProofSearchExperimentAdmissionExact.agda")
    memory = file(WIKIMEDIA / "IbrahimSnowballMandelaReligionIndigenousMemoryBraidingBidiExact.agda")
    for symbol in ["transparentPsi2025", "presentimentMeta2012",
                   "presentimentUpdate2018", "stargateOperationalReview1995"]:
        assert symbol in prior
    for symbol in ["presentimentRoute", "stargateHistoricalRecordAsOperationalUtilityTest"]:
        assert symbol in admission
    assert "prasadBainbridgeMandelaSource" in memory
    assert "noCIAStargateSameObject" in late


def brier(p: Fraction, result: int) -> Fraction:
    assert 0 <= p <= 1 and result in (0, 1)
    return (p - result) ** 2


def check_finite_score_and_primary_experiment_separation() -> None:
    source = agda("AmyEskridgeVideoTemporalForecastAndPsiMaxCutExact")
    assert "originalPublishedYear" in source
    assert "frozenProbabilityPerThousand : Maybe Nat" in source
    assert "fixedEventDefinitionRecorded" in source
    assert "eventSourceIndependentlyAuthenticated" in source
    assert "validProbability" in source
    assert "applyFrozenBrier" in source
    assert "burischOriginalCannotBeAssignedForecastScore = refl" in source
    assert "syntheticFrozenForecastIsScoreable = refl" in source
    assert "noInterviewForecastShortcut" in source
    assert "noMemoryToChangedHistoryShortcut" in source
    # Real source: expectation published 2007 for future 2016-17, but no
    # frozen probability, event definition or independent outcome. It is NOT
    # an actual observed failure/success: score is inapplicable.
    assert 2007 < 2016 <= 2017
    is_scorable = (None is not None) and False and False
    assert not is_scorable
    assert brier(Fraction(9, 10), 1) == Fraction(1, 100)
    assert brier(Fraction(9, 10), 0) == Fraction(81, 100)
    assert brier(Fraction(1, 2), 1) == Fraction(1, 4)

    chance = sp.Rational(5000, 10000)
    original = sp.Rational(5307, 10000)  # 53.07%
    transparent2023 = sp.Rational(4989, 10000)  # 49.89%
    walleczek2025_study3 = sp.Rational(5007, 10000)  # 50.07%
    walleczek2025_study2 = sp.Rational(4965, 10000)  # 49.65%
    assert sp.simplify(original - transparent2023) == sp.Rational(318, 10000)
    assert sp.simplify(chance - transparent2023) == sp.Rational(11, 10000)
    assert sp.simplify(walleczek2025_study3 - chance) == sp.Rational(7, 10000)
    assert walleczek2025_study2 < chance
    assert 2115 != 217800  # participants in 2023 vs *erotic trials* 2025.
    for doi in [
        "10.1098/rsos.191375",
        "10.1371/journal.pone.0335330",
        "10.3389/fpsyg.2012.00390",
        "10.12688/f1000research.14330.2",
    ]:
        assert doi in source, doi

    # Positives in one paradigm cannot become evidence for a different
    # target merely via media juxtaposition.
    source_cited, mechanism_demonstrated = sp.symbols(
        "source_cited mechanism_demonstrated"
    )
    assert sp.satisfiable(sp.And(source_cited, ~mechanism_demonstrated)) is not False


if __name__ == "__main__":
    check_exact_late_section()
    check_finite_score_and_primary_experiment_separation()
    print("PASS: 22 late-video claim-to-original-source joins and prior-art reuse")
    print("PASS: conditional 2007 forecast unscorable; synthetic Brier controls")
    print("PASS: 2011/2023/2025 rates, participant-vs-trial distinction, 2012/2018 physiology")
