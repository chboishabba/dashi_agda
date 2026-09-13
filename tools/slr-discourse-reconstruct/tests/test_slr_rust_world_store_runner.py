from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "run_world_research_typed_route_round.sh"


class RustWorldStoreRunnerTests(unittest.TestCase):
    def test_runner_builds_binary_observation_then_compiles_and_stores(self) -> None:
        text = RUNNER.read_text(encoding="utf-8")
        self.assertIn("SLR_SOURCE_TEXT", text)
        self.assertIn("SLR_SOURCE_DOCUMENT_REF", text)
        self.assertIn("SLR_SOURCE_QID", text)
        self.assertIn("SLR_SOURCE_LANGUAGE", text)
        self.assertIn("SLR_SOURCE_REVISION_REF", text)
        self.assertIn("slr_spacy_observation_wire.py", text)
        self.assertIn("SLR_SPACY_OBSERVATION_STREAM", text)
        self.assertIn("SLR_WORLD_COMPILER_BIN", text)
        self.assertIn("sensiblaw-world-compiler", text)
        self.assertIn("compile", text)
        self.assertIn("world-wire.slrw", text)
        self.assertIn("SLR_WORLD_STORE_BIN", text)
        self.assertIn("sensiblaw-world-store", text)
        self.assertIn("ingest-wire", text)
        self.assertIn("frontier", text)
        self.assertIn("postgres-latest-frontier.slrw", text)
        self.assertIn("binary_wire=true", text)
        self.assertIn("rust-world-compiler-unavailable", text)

    def test_python_is_confined_to_spacy_boundary_and_legacy_text_abis_are_absent(self) -> None:
        text = RUNNER.read_text(encoding="utf-8")
        self.assertEqual(text.count("python3 "), 1)
        self.assertIn('python3 "$HERE/slr_spacy_observation_wire.py"', text)
        for forbidden in (
            "ingest-round",
            "ingest-ndjson",
            ".jsonl",
            ".json",
            "slr_world_pg_store.py",
            "slr_article_pnf_semantic_weld.py",
            "slr_semantic_world_closure.py",
            "backend=python-fallback",
            "grep ",
        ):
            self.assertNotIn(forbidden, text, forbidden)


if __name__ == "__main__":
    unittest.main()
