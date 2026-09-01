import json
import tempfile
import unittest
from pathlib import Path

import proof_jacquard_export as exporter


def valid_frames():
    return [
        {"kind": "start", "proof_step_id": 0, "motif": "premise", "payload_bits": [0, 0]},
        {"kind": "motif_begin", "proof_step_id": 0, "motif": "branch", "provenance_id": 7, "payload_bits": [0, 0]},
        {"kind": "provenance", "proof_step_id": 0, "motif": "branch", "provenance_id": 7, "payload_bits": [0, 0]},
        {"kind": "continuation", "proof_step_id": 0, "continuation_id": 0, "more": True, "motif": "branch", "provenance_id": 7, "payload_bits": [0, 0]},
        {"kind": "continuation", "proof_step_id": 0, "continuation_id": 1, "more": False, "motif": "branch", "provenance_id": 7, "payload_bits": [1, 1]},
        {"kind": "motif_end", "proof_step_id": 0, "motif": "branch", "provenance_id": 7, "payload_bits": [0, 0]},
        {"kind": "stop", "proof_step_id": 1, "motif": "conclusion", "payload_bits": [0, 0]},
    ]


class ExporterTests(unittest.TestCase):
    def test_valid_tape_writes_rectangular_bmp(self):
        layout = exporter.Layout()
        frames = valid_frames()
        for frame in frames:
            exporter.validate_local(frame, layout, 2)
        exporter.validate_structure(frames)
        rows = [exporter.physical_row(frame, layout, 2) for frame in frames]
        self.assertTrue(rows)
        self.assertTrue(all(len(row) == len(rows[0]) for row in rows))
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "proof.bmp"
            exporter.write_bmp(path, rows)
            data = path.read_bytes()
            self.assertEqual(data[:2], b"BM")
            self.assertGreater(len(data), 54)

    def test_bad_parity_is_rejected(self):
        layout = exporter.Layout()
        frame = valid_frames()[0]
        frame["parity_bit"] = 1 - exporter.expected_parity(frame, layout, 2)
        with self.assertRaises(ValueError):
            exporter.validate_local(frame, layout, 2)

    def test_bad_frame_order_is_rejected(self):
        frames = valid_frames()
        frames[2], frames[3] = frames[3], frames[2]
        with self.assertRaises(ValueError):
            exporter.validate_structure(frames)

    def test_wif_requires_actual_shaft_factorisation(self):
        rows = [[0, 1], [1, 0]]
        with self.assertRaises(ValueError):
            exporter.verify_shaft_factorisation(rows, [1, 1])

    def test_wif_liftplan_emits_when_factorable(self):
        rows = [[1, 0], [0, 1]]
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "proof.wif"
            exporter.write_wif(path, rows, [1, 2])
            text = path.read_text(encoding="utf-8")
            self.assertIn("[LIFTPLAN]", text)
            self.assertIn("Treadles=0", text)


if __name__ == "__main__":
    unittest.main()
