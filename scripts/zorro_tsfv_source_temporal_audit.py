#!/usr/bin/env python3
"""Source-bounded Zorro/WingMakers/TSFV finite audit (not a physical test).

This module does not download evidence, authenticate the underlying DOJ PDFs,
establish legal liability, or demonstrate paranormal mechanisms.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
import unittest

TRANSCRIPT_SHA256 = "7811bb6f538dace90a7febace011c61569d31d2efd1300acfc8b5e960a7887ab"

@dataclass(frozen=True)
class Source:
    id: str
    origin_root: str
    form: str
    proposition: str
    ceiling: str

SOURCES = (
    Source("EFTA00578213", "zorro-task-2001", "ranch-task-list",
           "list reports one rock brought to old dog yard",
           "report in task list; original scanned PDF not visually inspected"),
    Source("EFTA00990932", "myhrvold-email-2014", "outgoing-email",
           "Epstein asks how to cut and polish granite bearing petroglyphs",
           "question; no cutting/polishing execution established"),
    Source("EFTA00694234", "myhrvold-email-2014", "reply-quoting-original",
           "Myhrvold states he will email more later and quotes same question",
           "same thread; no completed work or advice inferred"),
    Source("MAHU-CW-2013", "mahu-author-edition", "author-publisher-edition",
           "Ancient Arrow and Neruda interviews designated works of fiction",
           "edition status; not historical intelligence programme"),
    Source("BATES-2026", "clara-bates-journalism", "original-reporting",
           "petroglyph movement and Indigenous heritage concern reported",
           "journalism; repeating it is not independent field observation"),
    Source("APCG-2026", "pueblo-council-statement", "quoted-community-statement",
           "Pueblo council chair objects to damage/removal",
           "quote reproduced via reporting; full original statement uninspected"),
    Source("NMDOJ-2026-02-19", "new-mexico-doj", "agency-announcement",
           "state reopens Zorro Ranch criminal investigation",
           "investigation not conviction"),
    Source("NMDOJ-2026-03-09", "new-mexico-doj", "agency-announcement",
           "state announces search of property",
           "search not petroglyph-specific adjudication"),
    Source("NMDOJ-2026-08-05", "new-mexico-doj", "agency-litigation-announcement",
           "state files records-access suit against federal DOJ",
           "allegations and requests not judgment"),
    Source("NMDOJ-2026-10-21", "new-mexico-doj", "agency-civil-complaint",
           "state sues Indyke/Kahn and Epstein estate/trust",
           "claims in civil complaint; liability not adjudicated"),
    Source("REEL-2026", "instagram-reel-speaker", "attributed-video-transcript",
           "asserts secret stone technology and controllable retrocausality",
           "speaker claim, not physically validated"),
)

CLAIMS_NOT_ESTABLISHED = (
    "petroglyph_polishing_completed",
    "wingmakers_zorro_operational_join",
    "mj12_authenticated_technological_transfer",
    "remote_viewing_operational_utility",
    "controlled_retrocausal_intervention",
    "independent_original_DOJ_PDF_visual_audit",
    "petroglyph_specific_court_liability",
)

def root_index(sources: tuple[Source, ...] = SOURCES) -> dict[str, list[str]]:
    index: dict[str, list[str]] = {}
    for source in sources:
        index.setdefault(source.origin_root, []).append(source.id)
    return index

def independent_root_count(ids: tuple[str, ...], sources: tuple[Source, ...] = SOURCES) -> int:
    by_id = {s.id: s for s in sources}
    if len(set(ids)) != len(ids) or any(i not in by_id for i in ids):
        raise ValueError("IDs must be unique and from the declared source register")
    return len({by_id[i].origin_root for i in ids})

EARLIER = (0, 1)
LATER_FILTERS = (0, 1)

def unconditional_counts(later_filter: int) -> tuple[int, int]:
    if later_filter not in LATER_FILTERS:
        raise ValueError("unknown later filter")
    return (1, 1)

def selected_counts(later_filter: int) -> tuple[int, int]:
    if later_filter not in LATER_FILTERS:
        raise ValueError("unknown later filter")
    return tuple(int(bit == later_filter) for bit in EARLIER)

def normalise(counts: tuple[int, int]) -> tuple[float, float]:
    if len(counts) != 2 or any(x < 0 or not isinstance(x, int) for x in counts):
        raise ValueError("invalid finite count vector")
    n = sum(counts)
    if n <= 0:
        raise ValueError("zero support")
    return tuple(x / n for x in counts)

def temporal_fixture() -> dict:
    unconditioned = {str(a): normalise(unconditional_counts(a)) for a in LATER_FILTERS}
    selected = {str(a): normalise(selected_counts(a)) for a in LATER_FILTERS}
    return {
        "model": "finite classical selection, NOT Hilbert/TSVF physical realization",
        "unconditional_earlier": unconditioned,
        "postselected_earlier": selected,
        "preselected_distribution_invariant": unconditioned["0"] == unconditioned["1"],
        "postselected_distributions_differ": selected["0"] != selected["1"],
        "controlled_retrocausal_signal_established": False,
    }

def audit(transcript: Path | None = None) -> dict:
    rows = [s.__dict__ for s in SOURCES]
    ids = [s["id"] for s in rows]
    if len(ids) != len(set(ids)):
        raise AssertionError("duplicate evidence ID")
    if transcript is not None:
        actual = hashlib.sha256(transcript.read_bytes()).hexdigest()
        if actual != TRANSCRIPT_SHA256:
            raise ValueError(f"reel transcript SHA mismatch: {actual}")
    return {
        "transcript_sha256": TRANSCRIPT_SHA256,
        "transcript_byte_match_checked": transcript is not None,
        "sources": rows,
        "root_groups": root_index(),
        "distinct_roots": len(root_index()),
        "one_2014_thread_not_two": independent_root_count(("EFTA00990932", "EFTA00694234")) == 1,
        "claimed_but_not_established": CLAIMS_NOT_ESTABLISHED,
        "temporal_fixture": temporal_fixture(),
    }

class EvidenceAndTemporalTests(unittest.TestCase):
    def test_2014_same_thread(self):
        self.assertEqual(independent_root_count(("EFTA00990932", "EFTA00694234")), 1)

    def test_ranch_task_separate_root(self):
        self.assertEqual(independent_root_count(("EFTA00578213", "EFTA00990932")), 2)

    def test_agency_multiple_documents_one_institutional_root(self):
        self.assertEqual(independent_root_count(
            ("NMDOJ-2026-02-19", "NMDOJ-2026-03-09", "NMDOJ-2026-08-05", "NMDOJ-2026-10-21")), 1)

    def test_repeated_id_rejected(self):
        with self.assertRaises(ValueError):
            independent_root_count(("EFTA00990932", "EFTA00990932"))

    def test_unknown_id_rejected(self):
        with self.assertRaises(ValueError):
            independent_root_count(("NOT-AN-ARTIFACT",))

    def test_uniform_earlier_counts(self):
        self.assertEqual(unconditional_counts(0), unconditional_counts(1))

    def test_selected_earlier_counts_differ(self):
        self.assertEqual(selected_counts(0), (1, 0))
        self.assertEqual(selected_counts(1), (0, 1))

    def test_selected_vs_unconditional(self):
        result = temporal_fixture()
        self.assertTrue(result["preselected_distribution_invariant"])
        self.assertTrue(result["postselected_distributions_differ"])
        self.assertFalse(result["controlled_retrocausal_signal_established"])

    def test_zero_support_rejected(self):
        with self.assertRaises(ValueError):
            normalise((0, 0))

    def test_bad_negative_count_rejected(self):
        with self.assertRaises(ValueError):
            normalise((-1, 2))

    def test_unsupported_promotions_retained(self):
        result = audit()
        self.assertIn("petroglyph_polishing_completed", result["claimed_but_not_established"])
        self.assertIn("controlled_retrocausal_intervention", result["claimed_but_not_established"])
        self.assertEqual(len(result["sources"]), 11)

    def test_original_reel_digest(self):
        self.assertEqual(len(TRANSCRIPT_SHA256), 64)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--transcript", type=Path, default=None)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(EvidenceAndTemporalTests)
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        if not result.wasSuccessful():
            raise SystemExit(1)
    report = audit(args.transcript)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(f"{len(SOURCES)} records; {len(root_index())} source roots; "
              f"unconditional earlier distribution invariant: "
              f"{report['temporal_fixture']['preselected_distribution_invariant']}")
