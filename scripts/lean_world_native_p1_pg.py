#!/usr/bin/env python3
"""Source-bound P1 exported Lean Expr intake into EXISTING source PostgreSQL.

The exact Expr codec is imported from the selected #1495 worktree, never
reimplemented here. This writer validates actual stored source bytes, exact
type/proof roundtrip, alpha-key derivation and immutable source provenance.
It persists *observations*, NOT accepted typechecked declarations, complete
native import closures, an alternate world builder or theorem certificates.
"""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
import base64
import importlib.util
import json
import re

from run_lean_world_stream_pg import retrieve_source,SCHEMA_RE

class NativeP1PGError(ValueError): pass

HEX40=re.compile(r"[0-9a-f]{40}\Z")
HEX64=re.compile(r"[0-9a-f]{64}\Z")
SOURCE_LIMIT=8*1024*1024

def _hex(value,n=64):
    return type(value) is str and (HEX64 if n==64 else HEX40).fullmatch(value) is not None

def load_selected_codec(path: Path):
    """The *actual* #1495 owner is supplied from its isolated worktree."""
    path=Path(path).resolve(strict=True)
    if path.name!="lean_world_native_p1_codec.py" or not path.is_file():
        raise NativeP1PGError("requires original selected #1495 P1 codec file")
    spec=importlib.util.spec_from_file_location("dashi_selected_p1_codec",path)
    if spec is None or spec.loader is None:
        raise NativeP1PGError("unloadable source-owner codec")
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    for symbol in ("alpha_type","exact_type_roundtrip","exact_proof_roundtrip"):
        if not callable(getattr(module,symbol,None)):
            raise NativeP1PGError("selected source-owner codec lacks "+symbol)
    return module

def _decode(obs,key):
    v=obs.get(key)
    if type(v) is not str or len(v)>12_000_000:
        raise NativeP1PGError("missing or oversized "+key)
    try:
        result=base64.b64decode(v,validate=True)
    except (ValueError,UnicodeError) as exc:
        raise NativeP1PGError("invalid encoded "+key) from exc
    if len(result)>SOURCE_LIMIT:
        raise NativeP1PGError("exporter expression exceeds reviewed cap")
    return result

def inspect_observation(path:Path,codec):
    """Reject any promotion, unverifiable source or falsified alpha relation."""
    path=Path(path)
    if path.is_symlink() or not path.is_file() or path.stat().st_size>25_000_000:
        raise NativeP1PGError("unsafe native observation")
    raw=path.read_bytes()
    digest=sha256(raw).hexdigest()
    if path.name!=digest+".native-type-observation.json":
        raise NativeP1PGError("content-addressed observation filename mismatch")
    try: o=json.loads(raw)
    except (ValueError,UnicodeError) as exc:
        raise NativeP1PGError("invalid observation JSON") from exc
    if (not isinstance(o,dict) or
        o.get("schema")!="dashi-lean-v3-type-projection-observation-v1" or
        o.get("status")!="native-v3-type-projected-uncertified" or
        o.get("native_dag_complete") is not False or
        o.get("imported_dependencies_resolved") is not False or
        o.get("kernel_certified") is not False or
        o.get("world_admitted") is not False or
        o.get("exported_expr_roundtrip") is not True or
        o.get("original_source_text_reconstructed_by_codec") is not False):
        raise NativeP1PGError("observation status/authority boundary invalid")
    for key in ("repository","path","declaration","toolchain","handoff_key"):
        field="original_source_path" if key=="path" else key
        if type(o.get(field)) is not str or not o[field]:
            raise NativeP1PGError("missing original identity: "+field)
    if (not _hex(o.get("revision"),40) or
        not _hex(o.get("artifact_sha256")) or
        not _hex(o.get("handoff_key")) or
        not _hex(o.get("p1_codec_sha256")) or
        not _hex(o.get("original_source_sha256")) or
        type(o.get("proof_value_present")) is not bool):
        raise NativeP1PGError("invalid immutable original/export identity")
    implementation=getattr(codec,"__file__",None)
    if (type(implementation) is not str or
        sha256(Path(implementation).read_bytes()).hexdigest()!=
           o["p1_codec_sha256"]):
        raise NativeP1PGError("P1 source-owner codec implementation mismatch")
    source_closure=o.get("source_closure")
    if (not isinstance(source_closure,list) or not source_closure or
        any(type(s) is not list or len(s)!=2 or
            type(s[0]) is not str or not _hex(s[1])
            for s in source_closure)):
        raise NativeP1PGError("invalid original source closure")
    sources={r[0]:r[1] for r in source_closure}
    if (len(sources)!=len(source_closure) or
        sources.get(o["original_source_path"])!=o["original_source_sha256"]):
        raise NativeP1PGError("selected source was not in original closure")
    for field in ("direct_statement_constants","direct_proof_constants"):
        names=o.get(field)
        if (type(names) is not list or
            any(type(n) is not str or not n for n in names) or
            len(set(names))!=len(names)):
            raise NativeP1PGError("invalid direct constant reference list")
    exact=_decode(o,"exact_exported_type_b64")
    alpha=_decode(o,"alpha_type_b64")
    proof=_decode(o,"exact_exported_proof_b64")
    old=_decode(o,"canonical_type_b64")
    if exact!=old:
        raise NativeP1PGError("original exported type re-bound")
    if (codec.exact_type_roundtrip(exact)!=exact or
        codec.alpha_type(exact)!=alpha or
        sha256(exact).hexdigest()!=o.get("exact_exported_type_sha256") or
        sha256(exact).hexdigest()!=o.get("canonical_type_sha256") or
        sha256(alpha).hexdigest()!=o.get("alpha_type_sha256")):
        raise NativeP1PGError("exported exact/alpha expression mismatch")
    if o["proof_value_present"]:
        if (not proof or codec.exact_proof_roundtrip(proof)!=proof or
            sha256(proof).hexdigest()!=o.get("exact_exported_proof_sha256")):
            raise NativeP1PGError("original proof expression mismatch")
    elif proof or o.get("exact_exported_proof_sha256") is not None:
        raise NativeP1PGError("unexpected proof expression")
    return o,digest,exact,alpha,proof

def persist_original_p1(conn,path,codec):
    """Idempotent append-only source-bound observation, not world promotion."""
    o,observation_sha,exact,alpha,proof=inspect_observation(path,codec)
    raw_source=retrieve_source(conn,o["repository"],o["revision"],
                               o["original_source_path"])
    if sha256(raw_source).hexdigest()!=o["original_source_sha256"]:
        raise NativeP1PGError("P1 export disagrees with original PostgreSQL bytes")
    identity=(o["repository"],o["revision"],o["original_source_path"],
              o["declaration"],bytes.fromhex(o["artifact_sha256"]))
    fields=(bytes.fromhex(o["original_source_sha256"]),o["toolchain"],
            o["handoff_key"],bytes.fromhex(o["p1_codec_sha256"]),
            o.get("dependency_closure_id",""),
            exact,sha256(exact).digest(),alpha,sha256(alpha).digest(),
            proof,sha256(proof).digest() if proof else None,
            o["direct_statement_constants"],o["direct_proof_constants"],
            bytes.fromhex(observation_sha),"source-bound-projected-not-kernel-checked")
    sqlfile=Path(__file__).resolve().parent/"sql"/"lean_world_native_p1_observation_v1.sql"
    with conn.transaction():
        with conn.cursor() as cur:
            cur.execute(sqlfile.read_text(encoding="utf-8"))
            cur.execute("""
              INSERT INTO lean_world_native_p1_observation (
                repository,revision,path,declaration,native_export_sha256,
                original_source_sha256,toolchain,handoff_key,
                p1_codec_sha256,dependency_closure_id,type_exact,type_exact_sha256,
                type_alpha,type_alpha_sha256,proof_exact,proof_exact_sha256,
                direct_statement_constants,direct_proof_constants,
                observation_sha256)
              VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,
                      %s::jsonb,%s::jsonb,%s) ON CONFLICT DO NOTHING
            """,(*identity,*fields[:11],json.dumps(fields[11]),
                  json.dumps(fields[12]),fields[13]))
            cur.execute("""
              SELECT original_source_sha256,toolchain,handoff_key,
                p1_codec_sha256,dependency_closure_id,type_exact,type_exact_sha256,
                type_alpha,type_alpha_sha256,proof_exact,proof_exact_sha256,
                direct_statement_constants,direct_proof_constants,
                observation_sha256,status
              FROM lean_world_native_p1_observation
              WHERE repository=%s AND revision=%s AND path=%s
                AND declaration=%s AND native_export_sha256=%s
            """,identity)
            found=cur.fetchone()
            if found is None:
                raise NativeP1PGError("native P1 observation missing after insert")
            actual=tuple(bytes(x) if isinstance(x,memoryview) else x for x in found)
            if actual!=fields:
                raise NativeP1PGError("conflicting native observation history")
    return {
        "status":"source-bound-projected-not-kernel-checked",
        "repository":o["repository"],"revision":o["revision"],
        "source_path":o["original_source_path"],
        "declaration":o["declaration"],
        "type_exact_sha256":sha256(exact).hexdigest(),
        "type_alpha_sha256":sha256(alpha).hexdigest(),
        "proof_exact_sha256":sha256(proof).hexdigest() if proof else None,
        "p1_codec_sha256":o["p1_codec_sha256"],
        "source_bytes_retrieved_and_verified":True,
        "exported_expr_roundtrip":True,
        "dependencies_resolved":False,
        "kernel_certified":False,
        "world_admitted":False
    }
