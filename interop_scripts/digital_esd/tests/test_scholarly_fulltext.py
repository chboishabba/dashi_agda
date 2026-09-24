#!/usr/bin/env python3
"""Structural regression for the Digital-ESD scholarly full-text prototype.

This regression proves only the interop contract:
  exact artifact digest -> parser request -> document/facet candidates ->
  wrapper verification.

It does not certify scientific extraction quality.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


class ScholarlyFullTextInteropTest(unittest.TestCase):
    def test_plain_text_vertical_slice(self) -> None:
        repo_root = Path(__file__).resolve().parents[3]
        wrapper = repo_root / "interop_scripts" / "digital_esd" / "scholarly_fulltext.py"
        parser = repo_root / "interop_scripts" / "digital_esd" / "scholarly_parser_prototype.py"

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            artifact = root / "study.txt"
            artifact.write_text(
                """METHODS

We conducted a quasi-experimental study with n=120 university students.
Students participated in a digital sustainability course intervention, while
a comparison group completed the usual curriculum. Data were collected using
a questionnaire and analysed with regression.

RESULTS

The primary outcome was environmental knowledge score. The intervention group
showed higher post-test knowledge scores than the comparison group.

LIMITATIONS

The study has limitations including self-selection and a relatively small
sample for subgroup analysis.
""",
                encoding="utf-8",
            )
            digest = hashlib.sha256(artifact.read_bytes()).hexdigest()
            input_path = root / "fulltext.jsonl"
            input_path.write_text(
                json.dumps(
                    {
                        "source_identity_reference": "ERIC:TEST0001",
                        "source_revision_ref": f"fulltext-sha256:{digest}",
                        "content_digest_ref": f"sha256:{digest}",
                        "artifact_reference": str(artifact),
                        "acquisition_receipt_ref": "fixture:test",
                        "candidate_only": True,
                        "creates_source_audit_admission": False,
                    },
                    sort_keys=True,
                )
                + "\n",
                encoding="utf-8",
            )

            requests = root / "requests.jsonl"
            parser_output = root / "parser-output.jsonl"
            verified = root / "verified.jsonl"

            subprocess.run(
                [
                    sys.executable,
                    str(wrapper),
                    "prepare",
                    "--input",
                    str(input_path),
                    "--output",
                    str(requests),
                    "--verify-files",
                ],
                check=True,
            )
            subprocess.run(
                [
                    sys.executable,
                    str(parser),
                    "--input",
                    str(requests),
                    "--output",
                    str(parser_output),
                ],
                check=True,
            )
            subprocess.run(
                [
                    sys.executable,
                    str(wrapper),
                    "verify",
                    "--requests",
                    str(requests),
                    "--parser-output",
                    str(parser_output),
                    "--output",
                    str(verified),
                ],
                check=True,
            )

            bundle = json.loads(verified.read_text(encoding="utf-8").splitlines()[0])
            self.assertEqual(bundle["source_identity_reference"], "ERIC:TEST0001")
            self.assertTrue(bundle["candidate_only"])
            self.assertFalse(bundle["reviewed"])
            self.assertGreater(bundle["document_node_count"], 0)
            self.assertGreater(bundle["study_facet_count"], 0)

            facet_kinds = {row["facet_kind"] for row in bundle["study_facets"]}
            self.assertTrue(
                {
                    "population",
                    "sample",
                    "study_design",
                    "intervention",
                    "comparator",
                    "outcome",
                    "method",
                    "limitation",
                }.issubset(facet_kinds)
            )
            for facet in bundle["study_facets"]:
                observation = facet["observation"]
                self.assertTrue(observation["candidate_only"])
                self.assertFalse(observation["creates_semantic_authority"])
                self.assertFalse(observation["applicability_promoted"])
                self.assertFalse(observation["claim_truth_promoted"])


if __name__ == "__main__":
    unittest.main()
