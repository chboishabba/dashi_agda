#!/usr/bin/env python3
"""P1 source/typed-expression cross-branch bridge: no certificate promotion."""
from __future__ import annotations
from hashlib import sha256
from io import BytesIO
from pathlib import Path
import base64
import json
import os
import sys
import tarfile
import tempfile
import unittest
import uuid

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from lean_world_native_p1_pg import (
    inspect_observation,load_selected_codec,persist_original_p1,
    bounded_original_alpha_fibre,retrieve_original_native_p1,NativeP1PGError)
from run_lean_world_stream_pg import ingest_stream,migrate

try:
    import psycopg
    from psycopg import sql
except ImportError:
    psycopg=None

def encoded(obj):
    return json.dumps(obj,sort_keys=True,ensure_ascii=False,
                      separators=(",",":")).encode()

EXACT=encoded(["lean4export-v3-type-dag-v1",[],
               "sort",[1,[["sort",["zero"]]]]])
PROOF=encoded([1,[["sort",["zero"]]]])

class CandidateCodec:
    """Test-only stand-in, NOT an authentic native export reader."""
    __file__=__file__
    def exact_type_roundtrip(self,x):return x
    def exact_proof_roundtrip(self,x):return x
    def alpha_type(self,x):return b"alpha-candidate-"+x

def observation(root,source,*,alpha=None,promoted=False,codec_sha=None):
    alpha=alpha if alpha is not None else CandidateCodec().alpha_type(EXACT)
    record={
       "schema":"dashi-lean-v3-type-projection-observation-v1",
       "status":"native-v3-type-projected-uncertified",
       "native_dag_complete":False,
       "imported_dependencies_resolved":False,
       "kernel_certified":False,
       "world_admitted":promoted,
       "exported_expr_roundtrip":True,
       "original_source_text_reconstructed_by_codec":False,
       "repository":"example/test",
       "revision":"a"*40,
       "module":"Sample",
       "declaration":"originalProof",
       "toolchain":"Lean-4.28",
       "handoff_key":"c"*64,
       "p1_codec_sha256":codec_sha or sha256(Path(__file__).read_bytes()).hexdigest(),
       "dependency_closure_id":"",
       "artifact_sha256":"b"*64,
       "original_source_path":"Sample.lean",
       "original_source_sha256":sha256(source).hexdigest(),
       "source_closure":[["Sample.lean",sha256(source).hexdigest()]],
       "canonical_type_b64":base64.b64encode(EXACT).decode(),
       "canonical_type_sha256":sha256(EXACT).hexdigest(),
       "exact_exported_type_b64":base64.b64encode(EXACT).decode(),
       "exact_exported_type_sha256":sha256(EXACT).hexdigest(),
       "alpha_type_b64":base64.b64encode(alpha).decode(),
       "alpha_type_sha256":sha256(alpha).hexdigest(),
       "exact_exported_proof_b64":base64.b64encode(PROOF).decode(),
       "exact_exported_proof_sha256":sha256(PROOF).hexdigest(),
       "proof_value_present":True,
       "direct_statement_constants":[],
       "direct_proof_constants":[]
    }
    data=encoded(record)+b"\n"
    path=root/(sha256(data).hexdigest()+".native-type-observation.json")
    path.write_bytes(data)
    return path

def source_archive(raw):
    stream=BytesIO()
    with tarfile.open(fileobj=stream,mode="w:gz") as tf:
        info=tarfile.TarInfo("repo/Sample.lean")
        info.size=len(raw)
        tf.addfile(info,BytesIO(raw))
    stream.seek(0)
    return stream

class NativeP1SourceBoundary(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.source=b"theorem originalProof : True := by trivial\n"

    def test_exact_and_alpha_observation_remains_unadmitted(self):
        path=observation(self.root,self.source)
        record,digest,exact,alpha,proof=inspect_observation(path,CandidateCodec())
        self.assertEqual(exact,EXACT)
        self.assertEqual(proof,PROOF)
        self.assertFalse(record["world_admitted"])
        self.assertEqual(digest,path.name.split(".")[0])

    def test_tampered_alpha_even_if_filename_rehashed_fails(self):
        path=observation(self.root,self.source,alpha=b"unrelated")
        with self.assertRaisesRegex(NativeP1PGError,"mismatch"):
            inspect_observation(path,CandidateCodec())

    def test_changed_codec_source_identity_rejected(self):
        path=observation(self.root,self.source,codec_sha="d"*64)
        with self.assertRaisesRegex(NativeP1PGError,"codec implementation"):
            inspect_observation(path,CandidateCodec())

    def test_candidate_cannot_promote_to_world(self):
        path=observation(self.root,self.source,promoted=True)
        with self.assertRaisesRegex(NativeP1PGError,"authority"):
            inspect_observation(path,CandidateCodec())

    def test_original_source_closure_cannot_be_rebound(self):
        path=observation(self.root,self.source)
        record=json.loads(path.read_bytes())
        record["source_closure"]=[["Other.lean","d"*64]]
        data=encoded(record)+b"\n"
        altered=self.root/(sha256(data).hexdigest()+".native-type-observation.json")
        altered.write_bytes(data)
        with self.assertRaisesRegex(NativeP1PGError,"source"):
            inspect_observation(altered,CandidateCodec())

@unittest.skipUnless(
    psycopg is not None and bool(os.environ.get("PGDATABASE")) and
    bool(os.environ.get("DASHI_LEAN_P1_CODEC")),
    "requires explicit isolated PGDATABASE and #1495 P1 codec source")
class RealSourcePostgresP1(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.conn=psycopg.connect("")
        self.schema="lean_p1_src_"+uuid.uuid4().hex
        with self.conn.cursor() as cur:
            cur.execute(sql.SQL("CREATE SCHEMA {}").format(sql.Identifier(self.schema)))
            cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                sql.Identifier(self.schema)))
        self.conn.commit()
        migrate(self.conn)
        self.conn.commit()
        self.source=b"theorem originalProof : True := by trivial\n"
        with self.conn.transaction():
            ingest_stream(self.conn,"example/test","a"*40,
                          source_archive(self.source))
        self.codec=load_selected_codec(Path(os.environ["DASHI_LEAN_P1_CODEC"]))
        self.addCleanup(self.cleanup)

    def cleanup(self):
        self.conn.rollback()
        with self.conn.cursor() as cur:
            cur.execute("RESET search_path")
            cur.execute(sql.SQL("DROP SCHEMA {} CASCADE").format(
                sql.Identifier(self.schema)))
        self.conn.commit()
        self.conn.close()

    def test_original_source_exact_type_proof_and_index_are_persistent(self):
        alpha=self.codec.alpha_type(EXACT)
        path=observation(
            self.root,self.source,alpha=alpha,
            codec_sha=sha256(Path(self.codec.__file__).read_bytes()).hexdigest())
        first=persist_original_p1(self.conn,path,self.codec)
        second=persist_original_p1(self.conn,path,self.codec)
        self.assertEqual(first,second)
        self.assertTrue(first["exported_expr_roundtrip"])
        self.assertTrue(first["source_bytes_retrieved_and_verified"])
        self.assertFalse(first["world_admitted"])
        with self.conn.cursor() as cur:
            cur.execute("""
                SELECT type_exact,type_alpha,proof_exact,status
                FROM lean_world_native_p1_observation
                WHERE repository=%s AND revision=%s AND path=%s
                  AND declaration=%s
            """,("example/test","a"*40,"Sample.lean","originalProof"))
            row=cur.fetchone()
        self.assertEqual(tuple(bytes(x) if isinstance(x,memoryview) else x
                               for x in row[:3]),(EXACT,alpha,PROOF))
        self.assertEqual(row[3],"source-bound-projected-not-kernel-checked")
        restored=retrieve_original_native_p1(
            self.conn,repository="example/test",revision="a"*40,
            path="Sample.lean",declaration="originalProof",
            export_sha256="b"*64)
        self.assertEqual(restored["source"],self.source)
        self.assertEqual(restored["type_exact"],EXACT)
        self.assertEqual(restored["type_alpha"],alpha)
        self.assertEqual(restored["proof_exact"],PROOF)
        self.assertFalse(restored["kernel_certified"])
        self.assertFalse(restored["world_admitted"])
        hit=bounded_original_alpha_fibre(
            self.conn,toolchain="Lean-4.28",alpha_type=alpha,limit=1)
        self.assertEqual(hit["returned"],1)
        self.assertTrue(hit["complete"])
        self.assertEqual(hit["matches"][0]["declaration"],"originalProof")
        self.assertFalse(hit["kernel_certified"])
        negative=bounded_original_alpha_fibre(
            self.conn,toolchain="Lean-4.28",alpha_type=alpha+b"change",limit=1)
        self.assertEqual(negative["returned"],0)
        with self.assertRaisesRegex(NativeP1PGError,"budget"):
            bounded_original_alpha_fibre(
                self.conn,toolchain="Lean-4.28",alpha_type=alpha,limit=0)

if __name__=="__main__":
    unittest.main()
