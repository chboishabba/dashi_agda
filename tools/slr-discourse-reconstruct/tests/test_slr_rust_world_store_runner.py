from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "run_world_research_typed_route_round.sh"


class RustWorldStoreRunnerTests(unittest.TestCase):
    def test_runner_requires_binary_observation_compiler_and_world_store(self) -> None:
        text = RUNNER.read_text(encoding="utf-8")
        self.assertIn("SLR_WORLD_COMPILER_BIN", text)
        self.assertIn("sensiblaw-world-compiler", text)
        self.assertIn("SLR_SPACY_OBSERVATION_STREAM", text)
        self.assertIn("compile", text)
        self.assertIn("world-wire.slrw", text)
        self.assertIn("SLR_WORLD_STORE_BIN", text)
        self.assertIn("sensiblaw-world-store", text)
        self.assertIn("ingest-wire", text)
        self.assertIn("frontier", text)
        self.assertIn("postgres-latest-frontier.slrw", text)
        self.assertIn("binary_wire=true", text)
        self.assertIn("binary-observation-wire-unavailable", text)
        self.assertIn("rust-world-compiler-unavailable", text)

    def test_legacy_text_world_abis_are_absent(self) -> None:
        text = RUNNER.read_text(encoding="utf-8")
        for forbidden in (
            "ingest-round",
            "ingest-ndjson",
            ".jsonl",
            ".json",
            "slr_world_pg_store.py",
            "backend=python-fallback",
            "python3 ",
            "grep ",
        ):
            self.assertNotIn(forbidden, text, forbidden)


if __name__ == "__main__":
    unittest.main()
