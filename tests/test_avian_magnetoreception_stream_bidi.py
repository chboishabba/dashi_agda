"""Regression tests: 2020 video / 2019-2026 avian evidence, no gene-editing protocol."""

from pathlib import Path

from scripts.check_avian_magnetoreception_stream_bidi import (
    ADAPTER, AGDA, BIO_ROOT, CORE, DOC, EXISTING, ROOT, TOE_ROOT,
    inspect_source_contract, load_sources, run_agda,
)


def test_all_source_owners_and_canonical_roots_are_wired():
    assert inspect_source_contract(load_sources(ROOT)) == []


def test_livestream_source_cannot_disappear_from_crosswalk():
    src = load_sources(ROOT)
    src[ADAPTER] = src[ADAPTER].replace("2020-06-17", "unknown-date")
    assert any("2020-06-17" in x for x in inspect_source_contract(src))


def test_2025_2026_brain_screen_is_not_silently_omitted():
    src = load_sources(ROOT)
    src[ADAPTER] = src[ADAPTER].replace(
        "10.1126/science.aea6425", "not-supported")
    assert any("10.1126/science.aea6425" in x for x in inspect_source_contract(src))


def test_2026_hepatic_owner_must_be_reused():
    src = load_sources(ROOT)
    src[ADAPTER] = src[ADAPTER].replace(
        "Hepatic.hepaticMacrophageGenericSurface", "new-duplicate-sensor")
    assert any("Hepatic.hepaticMacrophageGenericSurface" in x
               for x in inspect_source_contract(src))


def test_cryptochrome_and_vestibular_routes_cannot_be_collapsed():
    src = load_sources(ROOT)
    src[ADAPTER] = src[ADAPTER].replace(
        "Generic.vestibularCandidateChannel", "Generic.radicalPairRetinalChannel")
    assert any("Generic.vestibularCandidateChannel" in x
               for x in inspect_source_contract(src))


def test_no_video_to_human_edit_promotion():
    src = load_sources(ROOT)
    src[CORE] = src[CORE].replace(
        "videoDoesNotProveHumanGain", "videoProvesHumanGain")
    assert any("videoDoesNotProveHumanGain" in x
               for x in inspect_source_contract(src))


def test_constant_flux_does_not_auto_induce_voltage():
    src = load_sources(ROOT)
    src[CORE] = src[CORE].replace(
        "stationaryConstantFluxDoesNotSupplyInductionPremise",
        "constantFluxSuffices")
    assert any("stationaryConstantFluxDoesNotSupplyInductionPremise" in x
               for x in inspect_source_contract(src))


def test_postulates_metaholes_and_termination_escape_are_rejected():
    for unsafe in ("\npostulate\n  hidden : Set\n",
                   "\nfailed : Set\nfailed = {! !}\n",
                   "\n{-# TERMINATING #-}\n"):
        src = load_sources(ROOT)
        src[CORE] += unsafe
        assert any("unsafe Golden" in x or "trust escape" in x
                   for x in inspect_source_contract(src))


def test_loss_of_safety_flag_and_root_import_rejected():
    src = load_sources(ROOT)
    src[CORE] = src[CORE].replace("{-# OPTIONS --safe #-}", "")
    assert any("not safe" in x for x in inspect_source_contract(src))
    for root in (TOE_ROOT, BIO_ROOT):
        src = load_sources(ROOT)
        src[root] = src[root].replace(
            "import DASHI.Biology.AvianMagnetoreceptionThoughtEmporiumEvidenceExact",
            "")
        assert any("AvianMagnetoreceptionThoughtEmporiumEvidenceExact" in x
                   for x in inspect_source_contract(src))


def test_missing_existing_owner_is_rejected():
    src = load_sources(ROOT)
    src.pop(EXISTING[0])
    assert any("missing source" in x for x in inspect_source_contract(src))


def test_missing_agda_binary_is_explicit_not_a_success(monkeypatch):
    from scripts import check_avian_magnetoreception_stream_bidi as audit
    monkeypatch.setattr(audit.shutil, "which", lambda _name: None)
    outcome = run_agda(Path(ROOT))
    assert outcome["state"] == "unavailable"
    assert outcome["passed"] is False
    assert CORE in AGDA


def test_transcript_provenance_and_research_cut_preserved():
    src = load_sources(ROOT)
    assert "59388d04a5e7baa3465f84bcf25d71830e9e5d61c3ebc011d7c8ca05fda758c8" in src[DOC]
    assert "M08" in src[DOC]
    assert "No tested animal or human genetic gain of function" in src[DOC]
