from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "run_world_research_typed_route_round.sh"


class RustWorldStoreRunnerTests(unittest.TestCase):
    def test_runner_prefers_rust_world_store_and_queries_frontier(self) -> None:
        text = RUNNER.read_text(encoding="utf-8")
        self.assertIn("SLR_WORLD_STORE_BIN", text)
        self.assertIn("sensiblaw-world-store", text)
        self.assertIn("ingest-round", text)
        self.assertIn("frontier", text)
        self.assertIn("postgres-latest-frontier.jsonl", text)
        self.assertIn("postgres_persistence_is_semantic_authority", text)

    def test_python_persistence_is_only_fallback(self) -> None:
        text = RUNNER.read_text(encoding="utf-8")
        self.assertIn("SLR_WORLD_REQUIRE_RUST_STORE", text)
        self.assertIn("slr_world_pg_store.py", text)
        self.assertIn("rust-world-store-unavailable", text)


if __name__ == "__main__":
    unittest.main()
