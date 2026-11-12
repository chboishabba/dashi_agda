#!/usr/bin/env python3
"""P1 exporter Expr identity tests. Structural tests, not Lean kernel tests."""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
import json
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from lean_world_native_v3_projection import extract_candidates,NativeV3Error
from lean_world_native_p1_codec import (
    alpha_type,exact_type_roundtrip,exact_proof_roundtrip,
    candidate_receipt,P1CodecError)

def raw(rows):
    return ("\n".join(json.dumps(x) for x in rows)+"\n").encode()

def binder(name="x",*,lit="0",mdata=None,universe=None):
    # Real lean4export 3.1 uses Expr index ZERO. This regression must not
    # silently renumber it to a positive-only fixture.
    rows=[{"meta":{"format":{"version":"3.1.0"}}},
          {"str":{"pre":0,"str":"Demo"},"in":1},
          {"str":{"pre":0,"str":"Nat"},"in":2},
          {"str":{"pre":0,"str":name},"in":3},
          {"const":{"name":2,"us":[]},"ie":0},
          {"bvar":0,"ie":1},
          {"natVal":lit,"ie":2},
          {"app":{"fn":1,"arg":2},"ie":3},
          {"forallE":{"name":3,"type":0,"body":3,"binderInfo":"default"},"ie":4}]
    root=4
    if mdata is not None:
        rows.append({"mdata":{"expr":4,"data":mdata},"ie":5})
        root=5
    rows.append({"thm":{"name":1,"levelParams":[],"type":root,
                        "value":root,"all":[]}})
    return raw(rows)

class NativeP1(unittest.TestCase):
    def test_real_zero_expression_reference_and_complete_export_roundtrip(self):
        (c,)=extract_candidates(binder())
        self.assertTrue(c.canonical_type)
        self.assertTrue(c.canonical_proof)
        self.assertEqual(exact_type_roundtrip(c.canonical_type),c.canonical_type)
        self.assertEqual(exact_proof_roundtrip(c.canonical_proof),c.canonical_proof)
        self.assertEqual(sha256(c.canonical_proof).hexdigest(),c.proof_digest)
        receipt=candidate_receipt(
            c,toolchain="lean-v4.28.0",source_sha256="a"*64,
            export_sha256="b"*64)
        self.assertTrue(receipt["exported_expr_roundtrip"])
        self.assertFalse(receipt["kernel_certified"])
        self.assertFalse(receipt["world_admitted"])
        self.assertFalse(receipt["original_source_text_reconstructed_by_this_codec"])

    def test_binder_names_change_exact_export_but_not_alpha_key(self):
        a,=extract_candidates(binder("x"))
        b,=extract_candidates(binder("n"))
        self.assertNotEqual(a.canonical_type,b.canonical_type)
        self.assertEqual(alpha_type(a.canonical_type),alpha_type(b.canonical_type))

    def test_changed_natural_literal_does_not_merge(self):
        a,=extract_candidates(binder(lit="0"))
        b,=extract_candidates(binder(lit="1"))
        self.assertNotEqual(alpha_type(a.canonical_type),alpha_type(b.canonical_type))

    def test_exported_metadata_retained_exactly_but_ignored_for_alpha(self):
        a,=extract_candidates(binder(mdata={"site":"first"}))
        b,=extract_candidates(binder(mdata={"site":"second"}))
        c,=extract_candidates(binder())
        self.assertNotEqual(a.canonical_type,b.canonical_type)
        self.assertEqual(alpha_type(a.canonical_type),alpha_type(c.canonical_type))
        self.assertEqual(alpha_type(b.canonical_type),alpha_type(c.canonical_type))

    def test_nested_metadata_does_not_shift_alpha_dag_postorder(self):
        plain,=extract_candidates(binder())
        decorated=raw([
            {"meta":{"format":{"version":"3.1.0"}}},
            {"str":{"pre":0,"str":"Demo"},"in":1},
            {"str":{"pre":0,"str":"Nat"},"in":2},
            {"str":{"pre":0,"str":"x"},"in":3},
            {"const":{"name":2,"us":[]},"ie":0},
            {"bvar":0,"ie":1},
            {"natVal":"0","ie":2},
            {"mdata":{"expr":1,"data":{"source":"in-body"}},"ie":3},
            {"app":{"fn":3,"arg":2},"ie":4},
            {"forallE":{"name":3,"type":0,"body":4,
                        "binderInfo":"default"},"ie":5},
            {"thm":{"name":1,"levelParams":[],"type":5,
                    "value":5,"all":[]}}
        ])
        wrapped,=extract_candidates(decorated)
        self.assertNotEqual(plain.canonical_type,wrapped.canonical_type)
        self.assertEqual(alpha_type(plain.canonical_type),
                         alpha_type(wrapped.canonical_type))

    def test_same_printed_name_different_lean_name_constructor_does_not_merge(self):
        def exp(kind):
            names=[{"str":{"pre":0,"str":"Demo"},"in":1},
                   {"str":{"pre":0,"str":"Foo"},"in":2}]
            segment={"str":{"pre":2,"str":"1"},"in":3} if kind=="str" else (
                    {"num":{"pre":2,"i":1},"in":3})
            return raw([{"meta":{"format":{"version":"3.1.0"}}},
                        *names,segment,
                        {"const":{"name":3,"us":[]},"ie":0},
                        {"thm":{"name":1,"levelParams":[],"type":0,
                                "value":0,"all":[]}}])
        a,=extract_candidates(exp("str"))
        b,=extract_candidates(exp("num"))
        self.assertEqual(a.direct_constants,b.direct_constants)
        self.assertNotEqual(alpha_type(a.canonical_type),alpha_type(b.canonical_type))

    def test_universe_parameter_binder_renaming(self):
        def exp(level_name):
            return raw([
                {"meta":{"format":{"version":"3.1.0"}}},
                {"str":{"pre":0,"str":"Demo"},"in":1},
                {"str":{"pre":0,"str":level_name},"in":2},
                {"param":2,"il":1},
                {"sort":1,"ie":0},
                {"thm":{"name":1,"levelParams":[2],"type":0,
                        "value":0,"all":[]}}
            ])
        a,=extract_candidates(exp("u"))
        b,=extract_candidates(exp("v"))
        self.assertNotEqual(a.canonical_type,b.canonical_type)
        self.assertEqual(alpha_type(a.canonical_type),alpha_type(b.canonical_type))

    def test_fail_closed_on_forward_ref_and_index_collision(self):
        for rows in [
            raw([{"meta":{"format":{"version":"3.1.0"}}},
                 {"str":{"pre":0,"str":"D"},"in":1},
                 {"sort":0,"ie":0},
                 {"sort":0,"ie":0},
                 {"thm":{"name":1,"levelParams":[],"type":0,
                         "value":0,"all":[]}}]),
            raw([{"meta":{"format":{"version":"3.1.0"}}},
                 {"str":{"pre":0,"str":"D"},"in":1},
                 {"app":{"fn":1,"arg":1},"ie":0},
                 {"thm":{"name":1,"levelParams":[],"type":0,
                         "value":0,"all":[]}}])
        ]:
            with self.assertRaises(NativeV3Error):
                extract_candidates(rows)

if __name__=="__main__":
    unittest.main()
