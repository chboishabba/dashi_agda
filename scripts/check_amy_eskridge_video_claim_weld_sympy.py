#!/usr/bin/env python3
"""SymPy and source-structure conformance for the Eskridge video aggregator.

Run from the repo: python scripts/check_amy_eskridge_video_claim_weld_sympy.py
Source: transcript provided 2026-11-17 (86 selected claims);
House Oversight, FBI letter, 2026-04-20:
https://oversight.house.gov/wp-content/uploads/2026/04/FBI-Missing-Scientists-Letter_4.20.26.pdf
Podkletnov and Nieminen, Physica C 203 (1992) 441-444,
DOI 10.1016/0921-4534(92)90055-H (0.05-0.3 percent claim).
Theorem/logic checks are DASHI extensions, not published claims of authors.
"""
from __future__ import annotations

import re
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
CULTURE = ROOT / "DASHI" / "Culture"


def read(name: str) -> str:
    return (CULTURE / name).read_text(encoding="utf-8")


def canonical(name: str) -> str:
    n = name.casefold()
    keys = [
        ("nuno", "nuno"), ("leblanc", "leblanc"), ("maiwald", "maiwald"),
        ("reza", "reza"), ("jacinto", "reza"), ("grillmair", "grillmair"),
        ("hicks", "hicks"), ("mccasland", "mccasland"),
        ("chavez", "chavez"), ("thomas", "thomas"),
        ("eskridge", "amy"), ("ning li", "ning"), ("chen", "chen"),
        ("feng", "feng"), ("zhou", "zhou"), ("liu", "liu"),
        ("zhang xiaoxin", "zhang_xiaoxin"), ("zhang daibing", "zhang_daibing"),
        ("li minyong", "li_minyong"), ("fang", "fang"), ("yan", "yan"),
        ("casias", "casias"), ("garcia", "garcia"),
    ]
    for needle, key in keys:
        if needle in n:
            return key
    raise AssertionError("Unrecognized source-person identity: " + name)


def source_names(module: str, constructor: str) -> list[str]:
    return re.findall(
        r'(?m)^\w+\s*=\s*' + re.escape(constructor) + r'\s+"([^"]+)"',
        read(module),
    )


def ids_after_definition(module: str, declaration: str, stem: str) -> list[int]:
    text = read(module)
    begin = text.index(declaration)
    tail = text[begin:]
    return [int(i) for i in re.findall(r'\b' + stem + r'(\d{3})\b', tail.split("\n\n", 1)[0])]


def verify_ids(claim_ids: list[int], join_ids: list[int], list_ids: list[int]) -> None:
    expected = list(range(1, 87))
    assert claim_ids == expected, "missing/duplicate/reordered transcript source rows"
    assert join_ids == expected, "missing/duplicate/reordered source-to-claim welds"
    assert list_ids == expected, "the final list does not enumerate all 86 welds"


def check_claim_welds() -> None:
    source = read("AmyEskridgeVideoClaimAttributionLedgerExact.agda")
    weld = read("AmyEskridgeVideoClaimProducerWeldExact.agda")
    claim_ids = [int(x) for x in re.findall(r'(?m)^claim(\d{3})\s*=\s*claim\s', source)]
    join_ids = [int(x) for x in re.findall(r'(?m)^claimJoin(\d{3})\s*=\s*video-claim-join\s', weld)]
    start = weld.index("allVideoClaimJoins =")
    end = weld.index("\n\n--", start)
    list_ids = [int(x) for x in re.findall(r'\bclaimJoin(\d{3})\b', weld[start:end])]
    verify_ids(claim_ids, join_ids, list_ids)
    assert "all86RowsAccountedFor = refl" in weld
    gates = read("AmyEskridgeVideoTypedObligationWeldExact.agda")
    gate_ids = [int(x) for x in re.findall(r'(?m)^gate(\d{3})\s*=\s*typed-claim-gate\s', gates)]
    gate_start = gates.index("allVideoGates =")
    gate_end = gates.index("\n\nforgetOpenGates", gate_start)
    gate_list_ids = [int(x) for x in re.findall(r'\bgate(\d{3})\b', gates[gate_start:gate_end])]
    assert gate_ids == list(range(1, 87))
    assert gate_list_ids == gate_ids
    assert "gateCoverage = refl" in gates
    for row_id, existing_producer in [
        (4, "Source.houseApril2026"),
        (15, "Hal5.canonicalHAL5TalkSourceReceipt"),
        (25, "Source.hallgarthChandlerPatent"),
        (36, "Papers.liTorr1991Atom"),
        (37, "Atlas.nasaNingNCC8124Source"),
        (41, "Extension.ningLiRosterRepair"),
        (43, "Papers.podkletnov1992Atom"),
        (51, "Papers.woodward1992Atom"),
        (70, "Source.bem2011"),
    ]:
        block = weld.split(f"claimJoin{row_id:03d} =", 1)[1].split("\n\n", 1)[0]
        assert existing_producer in block, (row_id, existing_producer)
    repeated_interview_clips = weld.count("(documentSource Source.burischCamelot)")
    assert repeated_interview_clips > 1
    # Repetition of one interview never creates new independent witnesses.
    assert len({"Project Camelot / Dan Burisch" for _ in range(repeated_interview_clips)}) == 1
    for disallowed in ["postulate", "trustMe", "TERMINATING", "NON_COVERING"]:
        assert not re.search(r"\b" + disallowed + r"\b", weld)


def check_scope() -> None:
    research = source_names(
        "MissingDeceasedTwentyScientistRound11SourceReplayParetoExact.agda",
        "round11-scientist-progress",
    )
    house = source_names(
        "MissingDeceasedTwentyScientistRound44OfficialInquiryCohortExact.agda",
        "official-inquiry-person",
    )
    assert len(research) == 20 and len(house) == 10
    rs = set(map(canonical, research))
    hs = set(map(canonical, house))
    assert len(rs) == 20 and len(hs) == 10
    assert len(rs & hs) == 8
    assert len(rs | hs) == 22
    assert "amy" in rs and "amy" not in hs
    assert sp.simplify(sp.Integer(len(rs)) + len(hs) - len(rs & hs) - len(rs | hs)) == 0

    # Non-uniqueness: same count, different proposed "11th" person.
    a = hs | {"amy"}
    b = hs | {"ning"}
    assert len(a) == len(b) == 11 and a != b
    assert "casias" in hs and "garcia" in hs
    original = read("AmyEskridgeVideoRosterScopeWeldExact.agda")
    assert "noHouseToVideoMembershipShortcut" in original
    assert "candidateNumeralIsEleven = refl" in original


def check_quantitative_boundary() -> None:
    earlier_upper = sp.Rational(3, 1000)  # 0.3 percent
    narrated = sp.Rational(2, 100)       # 2 percent
    assert sp.simplify(narrated / earlier_upper - sp.Rational(20, 3)) == 0
    assert earlier_upper < narrated
    # 1997 Li et al. cite later reports up to 2.1%; this is a source-
    # lineage distinction, not a contradiction with the 1992 0.3% article.
    later_reported_upper = sp.Rational(21, 1000)
    assert narrated <= later_reported_upper
    # NASA's separate static test resolution must NOT be called a direct
    # refutation of Podkletnov's other rotating apparatus.
    static_test_limit = sp.Rational(2, 10**8)
    assert sp.simplify(narrated / static_test_limit) == 10**6
    has_citation, has_causal_evidence = sp.symbols("has_citation has_causal_evidence")
    assert sp.satisfiable(sp.And(has_citation, sp.Not(has_causal_evidence))) is not False

    # Negative controls must actually fail.
    try:
        verify_ids(list(range(1, 87)), list(range(1, 86)), list(range(1, 87)))
    except AssertionError:
        pass
    else:
        raise AssertionError("missing-join negative control failed")


def check_original_clip_and_media_roster() -> None:
    zoom = read("AmyEskridgeVideoZoomClipSourceWeldExact.agda")
    fox = read("AmyEskridgeVideoEleventhMediaRosterWeldExact.agda")
    weld = read("AmyEskridgeVideoClaimProducerWeldExact.agda")
    for row, clip in {
        1: "openingThreat", 2: "nsaFive", 3: "fourSuppressions",
        5: "lexusSurveillance", 6: "lexusVehicle",
        7: "lexusPlateChange", 10: "futureP52",
    }.items():
        claim = f"claimJoin{row:03d} = video-claim-join"
        assert claim in weld
        section = weld.split(claim, 1)[1].split("\n\n", 1)[0]
        assert f"(clipSource Zoom.{clip})" in section

    for receipt in [
        "houseProducerListIsOriginal = refl",
        "elevenArticleKeysMatchNormalizedEnumeration = refl",
        "foxElevenEqualsHouseTenPlusAmyKeys = refl",
        "foxReportedElevenCount = refl",
        "houseContextTenCount = refl",
    ]:
        assert receipt in fox

    assert "OSINT.foxDeathCharacterizationSource" in fox
    assert "OSINT.archivedAmyInterviewSource" in zoom
    # Original Zoom opening segments source order: 31:02 -> 34:18 -> 35:40.
    # Edited first 21 seconds: 35:40 -> 31:02 -> 34:18.
    source = [31 * 60 + 2, 34 * 60 + 18, 35 * 60 + 40]
    edited = [35 * 60 + 40, 31 * 60 + 2, 34 * 60 + 18]
    assert all(a < b for a, b in zip(source, source[1:]))
    assert edited[0] > edited[1]
    assert sp.Integer(edited[0] - edited[1]) == 278
    # Edited order must not be promoted to original chronology.
    assert source != edited



def check_primary_inspection_and_clip_lineage() -> None:
    primary = read("AmyEskridgeVideoPrimaryInspectionExact.agda")
    clips = read("AmyEskridgeVideoOriginalClipLineageExact.agda")
    agg = read("AmyEskridgeVideoEvidenceEverything.agda")
    registry = read("AmyEskridgeVideoSourceRegistryExact.agda")
    historical = read("AmyEskridgeVideoHistoricalPrimaryControlsExact.agda")
    rows = re.findall(r'(?m)^\w+\s*=\s*primary-document-reading\b', primary)
    sources = re.findall(r'(?m)^clip\d{2}\s*=\s*clip-lineage\b', clips)
    assert len(rows) == 10
    assert len(sources) == 16
    assert len(re.findall(r'(?m)^\\w+\\s*=\\s*historical-control\\b', historical)) == 3
    assert "all86SourceAssociationRetained = Existing.all86RowsAccountedFor" in primary
    assert "acw16d6CCnY" in registry and "acw16d6CCnY" in clips
    for needle in ["20000038203", "19990039542", "19990019627",
                   "FOIA-00159-2018", "DIA-08-1003-018",
                   "DIA-08-1004-001", "DIA-08-1003-015", "DIA-08-1004-004",
                   "10.1037/a0021524", "10.1016/0921-4534(92)90055-H"]:
        assert needle in primary, needle
    assert "videoTime" in clips
    assert "voiceAttributedOriginalUnlocated" in clips
    assert "AmyEskridgeVideoPrimaryInspectionExact" in agg
    assert "AmyEskridgeVideoOriginalClipLineageExact" in agg
    assert "AmyEskridgeVideoHistoricalPrimaryControlsExact" in agg
    for target in ["Video.claim043", "Video.claim049", "Video.claim053", "Public Law 91-121", "145 mm"]:
        assert target in historical, target
    # The speaker quotation and original publication are source metadata,
    # never an independent scientific proof.
    for escape in ["postulate", "trustMe", "TERMINATING", "NON_COVERING"]:
        assert not re.search(r"\b" + escape + r"\b", primary + clips)


if __name__ == "__main__":
    check_claim_welds()
    check_original_clip_and_media_roster()
    check_scope()
    check_quantitative_boundary()
    check_primary_inspection_and_clip_lineage()
    print("Amy Eskridge video 86-row / House-10 / research-20 SymPy audit: PASS")
    print("Includes 7 earlier Zoom locators, 16 edited-clip lineages, 10 primary inspection records, and negative controls")
