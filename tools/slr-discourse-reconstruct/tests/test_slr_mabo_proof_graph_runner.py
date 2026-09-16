from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "run_slr_mabo_proof_graph.sh"


class MaboProofGraphRunnerTests(unittest.TestCase):
    def test_runner_delegates_typed_profile_to_existing_bounded_recurrence(self) -> None:
        text = RUNNER.read_text(encoding="utf-8")
        self.assertIn("SLR_MABO_CONSUMER_SPEC", text)
        self.assertIn("SLR_CONSUMER_SPEC", text)
        self.assertIn("run_world_research_iteration_loop.sh", text)
        self.assertIn("SLR_MAX_ITERATIONS", text)
        self.assertIn("candidate_only=true", text)
        self.assertIn("semantic_promotion=false", text)
        self.assertIn("legal_semantics_owner=SensibLaw", text)
        self.assertIn("research_recurrence_owner=SLR", text)

    def test_runner_does_not_duplicate_mabo_legal_semantics_or_legacy_transport(self) -> None:
        text = RUNNER.read_text(encoding="utf-8")
        for forbidden in (
            "mabo_slr_profile.py",
            "lee_residual_search_gate.py",
            "reject_doctrine",
            "recognise_native_title",
            "--evidence-requirement",
            ".json",
            ".jsonl",
            "grep ",
            "python3 ",
        ):
            self.assertNotIn(forbidden, text, forbidden)

    def test_runner_requires_source_metadata_instead_of_inventing_a_mabo_source(self) -> None:
        text = RUNNER.read_text(encoding="utf-8")
        self.assertIn("SLR_SOURCE_TEXT", text)
        self.assertIn("SLR_SOURCE_DOCUMENT_REF", text)
        self.assertIn("SLR_SOURCE_QID", text)
        self.assertIn("SLR_SOURCE_REVISION_REF", text)
        self.assertIn("mabo-profile-unavailable", text)
        self.assertIn("mabo-source-metadata-incomplete", text)


if __name__ == "__main__":
    unittest.main()
