from pathlib import Path
import hashlib
import importlib.util
import io
import struct
import sys
import unittest

HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE.parent / "slr_spacy_observation_wire.py"
spec = importlib.util.spec_from_file_location("slr_spacy_observation_wire", MODULE_PATH)
assert spec and spec.loader
wire = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = wire
spec.loader.exec_module(wire)


def _text(value: str) -> bytes:
    raw = value.encode("utf-8")
    return struct.pack("<I", len(raw)) + raw


class SpacyObservationWireTests(unittest.TestCase):
    def test_manifestation_frame_matches_slro_header(self) -> None:
        out = io.BytesIO()
        wire.write_manifestation(
            out,
            document_ref="wiki:Q207:en:456",
            qid="Q207",
            language="en",
            revision_ref="456",
            source_sha256=bytes([7]) * 32,
        )
        data = out.getvalue()
        self.assertEqual(data[:4], b"SLRO")
        self.assertEqual(int.from_bytes(data[4:6], "little"), 1)
        self.assertEqual(data[6], 1)

    def test_token_frame_uses_exact_dependency_shape_tag(self) -> None:
        out = io.BytesIO()
        wire.write_token(
            out,
            document_ref="wiki:Q207:en:456",
            sentence_id=3,
            local_ordinal=0,
            start_char=0,
            end_char=4,
            head_ordinal=1,
            dependency_shape=wire.NOMINAL_SUBJECT,
            orth="Bush",
            lemma="Bush",
            head_orth="signed",
            head_lemma="sign",
        )
        data = out.getvalue()
        self.assertEqual(data[:4], b"SLRO")
        self.assertEqual(data[6], 2)
        self.assertIn(b"Bush", data)
        self.assertIn(b"sign", data)

    def test_dependency_labels_map_without_regex_semantics(self) -> None:
        self.assertEqual(wire.dependency_shape("nsubj"), wire.NOMINAL_SUBJECT)
        self.assertEqual(wire.dependency_shape("obj"), wire.DIRECT_OBJECT)
        self.assertEqual(wire.dependency_shape("nsubjpass"), wire.PASSIVE_SUBJECT)
        self.assertEqual(wire.dependency_shape("neg"), wire.NEGATION)
        self.assertEqual(wire.dependency_shape("ccomp"), wire.CLAUSAL_COMPLEMENT)
        self.assertEqual(wire.dependency_shape("unknown-label"), wire.UNRESOLVED_DEPENDENCY)

    def test_slrx_acquired_source_decodes_without_json_or_regex(self) -> None:
        text = "George Walker Bush served as president."
        digest = hashlib.sha256(text.encode("utf-8")).digest()
        frame = (
            b"SLRX"
            + struct.pack("<H", 1)
            + bytes([1, 1])
            + _text('wikipedia:Q207:en:W/"123"')
            + _text("Q207")
            + _text("en")
            + _text('W/"123"')
            + _text("https://en.wikipedia.org/wiki/George_W._Bush")
            + digest
            + _text(text)
        )
        source = wire.read_acquired_source(io.BytesIO(frame))
        self.assertEqual(source.document_ref, 'wikipedia:Q207:en:W/"123"')
        self.assertEqual(source.qid, "Q207")
        self.assertEqual(source.language, "en")
        self.assertEqual(source.revision_ref, 'W/"123"')
        self.assertEqual(source.text, text)
        self.assertEqual(source.source_sha256, digest)
        self.assertTrue(source.candidate_only)
        self.assertFalse(source.semantic_promotion)

    def test_producer_source_does_not_import_json_or_regex(self) -> None:
        text = MODULE_PATH.read_text(encoding="utf-8")
        self.assertNotIn("import json", text)
        self.assertNotIn("import re", text)
        self.assertNotIn("from re", text)


if __name__ == "__main__":
    unittest.main()
