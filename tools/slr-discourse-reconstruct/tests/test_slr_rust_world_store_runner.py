from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "run_world_research_typed_route_round.sh"


class RustWorldStoreRunnerTests(unittest.TestCase):
    def test_runner_requires_binary_rust_world_store_and_streaming_frontier(self) -> None:
        text = RUNNER.read_text(encoding="utf-8")
        self.assertIn("SLR_WORLD_STORE_BIN", text)
        self.assertIn("sensiblaw-world-store", text)
        self.assertIn("SLR_WORLD_WIRE_STREAM", text)
        self.assertIn("ingest-wire", text)
        self.assertNotIn("ingest-round", text)
        self.assertIn("frontier", text)
        self.assertIn("postgres-latest-frontier.slrw", text)
        self.assertIn("buffered_full_frontier=false", text)
        self.assertIn("binary_wire=true", text)
        self.assertNotIn(".jsonl", text)

    def test_legacy_json_persistence_is_not_in_typed_route_runner(self) -> None:
        text = RUNNER.read_text(encoding="utf-8")
        self.assertNotIn("slr_world_pg_store.py", text)
        self.assertNotIn("backend=python-fallback", text)
        self.assertNotIn("postgres-world-persistence-receipt.json", text)
        self.assertIn("rust-world-store-unavailable", text)
        self.assertIn("binary-world-wire-unavailable", text)


if __name__ == "__main__":
    unittest.main()
