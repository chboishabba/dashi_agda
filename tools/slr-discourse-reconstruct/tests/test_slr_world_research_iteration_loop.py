from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOOP = ROOT / "run_world_research_iteration_loop.sh"


class WorldResearchIterationLoopTests(unittest.TestCase):
    def test_loop_advances_only_on_nonempty_next_binary_observation(self) -> None:
        text = LOOP.read_text(encoding="utf-8")
        self.assertIn("SLR_MAX_ITERATIONS", text)
        self.assertIn("run_world_research_typed_route_round.sh", text)
        self.assertIn("next-spacy-observations.slro", text)
        self.assertIn("SLR_SPACY_OBSERVATION_STREAM", text)
        self.assertIn("bounded-stop:no-next-observation", text)
        self.assertIn("bounded-stop:repeated-observation", text)
        self.assertIn("bounded-stop:max-iterations", text)
        self.assertIn("continue:next-observation", text)
        self.assertIn("cmp -s", text)

    def test_loop_does_not_reintroduce_legacy_semantic_abis(self) -> None:
        text = LOOP.read_text(encoding="utf-8")
        for forbidden in (
            ".json",
            ".jsonl",
            "grep ",
            "python3 ",
            "slr_semantic_world_closure.py",
            "slr_article_pnf_semantic_weld.py",
        ):
            self.assertNotIn(forbidden, text, forbidden)


if __name__ == "__main__":
    unittest.main()
