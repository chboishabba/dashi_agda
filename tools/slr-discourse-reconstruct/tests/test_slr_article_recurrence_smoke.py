from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SMOKE = ROOT / "run_slr_article_recurrence_smoke.sh"


class ArticleRecurrenceSmokeTests(unittest.TestCase):
    def test_smoke_forces_article_semantic_wikipedia_recurrence(self) -> None:
        text = SMOKE.read_text(encoding="utf-8")
        self.assertIn("smoke:q207:article-recurrence-seed", text)
        self.assertIn("Q207", text)
        self.assertIn("need-patient", text)
        self.assertIn(" patient any", text)
        self.assertIn("sensiblaw-consumer-residual", text)
        self.assertIn("run_world_research_iteration_loop.sh", text)
        self.assertIn("SLR_MAX_ITERATIONS", text)
        self.assertIn("2", text)
        self.assertIn("candidate_only=true", text)
        self.assertIn("semantic_promotion=false", text)

    def test_smoke_does_not_embed_legacy_world_pipeline(self) -> None:
        text = SMOKE.read_text(encoding="utf-8")
        for forbidden in (
            ".json",
            ".jsonl",
            "grep ",
            "slr_semantic_world_closure.py",
            "slr_article_pnf_semantic_weld.py",
        ):
            self.assertNotIn(forbidden, text, forbidden)


if __name__ == "__main__":
    unittest.main()
