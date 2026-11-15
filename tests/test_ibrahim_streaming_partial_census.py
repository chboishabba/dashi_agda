"""Original-parser streaming partial-graph census and negative-source controls."""
from __future__ import annotations
from hashlib import sha256
import json
from pathlib import Path
import sys
import unittest
from tempfile import TemporaryDirectory

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from ibrahim_streaming_partial_census import run_census


def row(pageid, title, text):
    return {
        "pageid": pageid,
        "oldid": 1000 + pageid,
        "title": title, "wikitext": text,
        "wikitext_sha256": sha256(text.encode("utf-8")).hexdigest(),
    }


def write_corpus(path, pages):
    data = b"".join((json.dumps(p, sort_keys=True).encode("utf-8") + b"\n")
                    for p in pages)
    path.write_bytes(data)
    return sha256(data).hexdigest()


class PartialCensusTests(unittest.TestCase):
    def test_cycle_deadend_unresolved_and_sink_fibres_remain_distinct(self):
        with TemporaryDirectory() as d:
            root = Path(d)
            pages = [
                row(1, "A", "[[B]]"), row(2, "B", "[[C]]"),
                row(3, "C", "[[B]]"), row(4, "D", "No first link"),
                row(5, "E", "[[OutsideOriginalSource]]"),
                row(6, "F", "[[D]]"), row(7, "G", "[[B]]"),
                row(8, "X", "[[X]]"),
            ]
            digest = write_corpus(root / "corpus.jsonl", pages)
            result = run_census(
                jsonl=root / "corpus.jsonl", index_path=root / "index.sqlite",
                output=root / "receipt.json", expected_jsonl_sha256=digest)
            self.assertEqual(result["input_pages"], 8)
            self.assertEqual(result["outcome_counts"]["cycle"], 5)
            self.assertEqual(result["outcome_counts"]["dead_end"], 2)
            self.assertEqual(result["outcome_counts"]["unresolved_target"], 1)
            self.assertEqual(result["total_distinct_cycle_basins"], 2)
            by_root = {r["root"]: r for r in result["observed_cycles"]}
            self.assertEqual(by_root["B"], {"root": "B", "period": 2, "basin_size": 4})
            self.assertEqual(by_root["X"], {"root": "X", "period": 1, "basin_size": 1})
            self.assertFalse(result["every_wikipedia_page_globally_enumerated"])
            self.assertFalse(result["out_of_corpus_missing_targets_are_negative_evidence"])

    def test_original_corpus_digest_mismatch_fails_closed(self):
        with TemporaryDirectory() as d:
            root = Path(d)
            write_corpus(root / "corpus.jsonl", [row(1, "A", "[[A]]")])
            with self.assertRaises(ValueError):
                run_census(jsonl=root / "corpus.jsonl", index_path=root / "index.sqlite",
                           output=root / "receipt.json",
                           expected_jsonl_sha256="0" * 64)
            self.assertFalse((root / "receipt.json").exists())

    def test_duplicate_title_or_original_pageid_refused(self):
        for duplicated in (row(2, "A", "[[A]]"), row(1, "B", "[[A]]")):
            with self.subTest(duplicated=duplicated):
                with TemporaryDirectory() as d:
                    root = Path(d)
                    digest = write_corpus(root / "corpus.jsonl",
                                          [row(1, "A", "[[A]]"), duplicated])
                    with self.assertRaises(Exception):
                        run_census(jsonl=root / "corpus.jsonl",
                                   index_path=root / "index.sqlite",
                                   output=root / "receipt.json",
                                   expected_jsonl_sha256=digest)

    def test_wikitext_hash_must_bind_actual_original_row(self):
        with TemporaryDirectory() as d:
            root = Path(d)
            entry = row(1, "A", "[[A]]")
            entry["wikitext_sha256"] = "0" * 64
            digest = write_corpus(root / "corpus.jsonl", [entry])
            with self.assertRaises(ValueError):
                run_census(jsonl=root / "corpus.jsonl", index_path=root / "index.sqlite",
                           output=root / "receipt.json", expected_jsonl_sha256=digest)

    def test_refuse_replacing_existing_original_census_index(self):
        with TemporaryDirectory() as d:
            root = Path(d)
            digest = write_corpus(root / "corpus.jsonl", [row(1, "A", "[[A]]")])
            (root / "index.sqlite").write_text("pre-existing")
            with self.assertRaises(ValueError):
                run_census(jsonl=root / "corpus.jsonl", index_path=root / "index.sqlite",
                           output=root / "receipt.json", expected_jsonl_sha256=digest)


if __name__ == "__main__":
    unittest.main()
