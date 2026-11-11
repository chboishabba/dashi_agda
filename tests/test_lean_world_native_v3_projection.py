#!/usr/bin/env python3
"""Native-v3 projection negative controls. These are NOT Lean kernel tests."""
from __future__ import annotations
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from lean_world_native_v3_projection import extract_candidates,NativeV3Error


def export(name_index=1, expr_index=1, *, bad=False):
    rows=[
        {"meta":{"format":{"version":"3.1.0"}}},
        {"str":{"pre":0,"str":"Demo"},"in":name_index},
        {"sort":0,"ie":expr_index},
        {"thm":{"name":name_index,"levelParams":[],
                "type":expr_index,"value":expr_index,"all":[]}}
    ]
    if bad:
        rows[-1]["thm"]["value"]=999
    return ("\n".join(json.dumps(x) for x in rows)+"\n").encode()


class NativeProjectionTests(unittest.TestCase):
    def test_real_format_record_fields_are_projected_without_certification(self):
        candidate,=extract_candidates(export())
        self.assertEqual(candidate.name,"Demo")
        self.assertEqual(candidate.kind,"thm")
        self.assertTrue(candidate.proof_value_present)
        self.assertFalse(candidate.kernel_certified)
        self.assertTrue(candidate.canonical_type)

    def test_sparse_integer_tables_preserve_exact_candidate_type(self):
        first,=extract_candidates(export())
        second,=extract_candidates(export(47,987))
        self.assertEqual(first.canonical_type,second.canonical_type)
        self.assertEqual(first.type_sha256,second.type_sha256)

    def test_missing_proof_expression_reference_fails_closed(self):
        with self.assertRaisesRegex(NativeV3Error,"unresolved expression"):
            extract_candidates(export(bad=True))

    def test_missing_name_reference_fails_closed(self):
        raw=export().replace(b'"name": 1',b'"name": 900')
        with self.assertRaisesRegex(NativeV3Error,"unresolved name"):
            extract_candidates(raw)

    def test_duplicate_expression_index_rejected(self):
        rows=export().splitlines()
        duplicated=b"\n".join([rows[0],rows[1],rows[2],rows[2],rows[3]])+b"\n"
        with self.assertRaisesRegex(NativeV3Error,"duplicate"):
            extract_candidates(duplicated)

    def test_unsupported_inductive_is_explicit_not_silently_discarded(self):
        rows=export().splitlines()
        raw=b"\n".join([rows[0],b'{"inductive":{"types":[],"ctors":[],"recs":[]}}',
                          *rows[1:]])+b"\n"
        with self.assertRaisesRegex(NativeV3Error,"inductive group"):
            extract_candidates(raw)

    def test_type_constant_reference_is_resolved_to_name(self):
        rows=[
            {"meta":{"format":{"version":"3.0"}}},
            {"str":{"pre":0,"str":"Ty"},"in":11},
            {"str":{"pre":0,"str":"Demo"},"in":12},
            {"const":{"name":11,"us":[]},"ie":2},
            {"thm":{"name":12,"levelParams":[],"type":2,"value":2,"all":[]}}
        ]
        candidate,=extract_candidates(("\n".join(json.dumps(x) for x in rows)+"\n").encode())
        self.assertEqual(candidate.direct_constants,("Ty",))

    def test_empty_export_and_invalid_meta_rejected(self):
        with self.assertRaises(NativeV3Error):
            extract_candidates(b"")
        with self.assertRaisesRegex(NativeV3Error,"unsupported native format"):
            extract_candidates(b'{"meta":{"format":{"version":"2.0"}}}\n')


if __name__=="__main__":
    unittest.main()
