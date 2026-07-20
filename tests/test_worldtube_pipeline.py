import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "worldtube_importer", ROOT / "scripts" / "import_google_timeline_worldtube.py"
)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class WorldTubePipelineTests(unittest.TestCase):
    def test_normalizes_records_and_marks_large_gap(self):
        payload = {
            "locations": [
                {
                    "timestampMs": "1000",
                    "latitudeE7": -273000000,
                    "longitudeE7": 1529000000,
                    "accuracy": 12,
                },
                {
                    "timestampMs": "10000000",
                    "latitudeE7": -273100000,
                    "longitudeE7": 1529100000,
                    "accuracy": 20,
                },
            ]
        }
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Records.json"
            path.write_text(json.dumps(payload), encoding="utf-8")
            result = MODULE.normalize(path, maximum_gap_ms=1000)
        self.assertEqual(result["schema"], "dashi.worldtube.v1")
        self.assertEqual(len(result["observations"]), 2)
        self.assertEqual(result["segments"][0]["status"], "unknown_gap")
        self.assertFalse(result["complete_experience_claim"])
        self.assertFalse(result["authority_claim"])
        self.assertFalse(result["observations"][0]["exact_position"])

    def test_ecef_is_finite(self):
        xyz = MODULE.ecef(-27.47, 153.02, 10.0)
        self.assertEqual(len(xyz), 3)
        self.assertTrue(all(abs(value) < 7_000_000 for value in xyz))


if __name__ == "__main__":
    unittest.main()
