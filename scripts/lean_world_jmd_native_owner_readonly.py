#!/usr/bin/env python3
"""Read-only native-v3 cross-check through JMD's existing dashi_lean4 PR #105.

Uses ONLY nodes_from_export/reachable/expression_fingerprint of the selected
authoritative AST builder, never calls connect/import_export, and never writes
its separate SQLite metadata world. The #1484 PostgreSQL source world remains
the persistence owner for this P1 slice.

Read-only parsing and structural consistency are NOT independent Lean
verification, not a certified mathematical transport or an authenticated
shared-world builder transaction.
"""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
import importlib.util
import re

class JMDNativeOwnerError(ValueError):pass
HEX64=re.compile(r"[a-f0-9]{64}\Z")
HEX40=re.compile(r"[a-f0-9]{40}\Z")

def read_only_check(*,source_path,export_path,declaration,expected_export_sha):
    source_path=Path(source_path).resolve(strict=True)
    export_path=Path(export_path).resolve(strict=True)
    if (source_path.name!="build_jmd_lean_ast_world.py" or
        not source_path.is_file() or
        not export_path.is_file() or export_path.is_symlink() or
        type(declaration) is not str or not declaration or
        not HEX64.fullmatch(expected_export_sha)):
        raise JMDNativeOwnerError("invalid selected JMD builder/native source")
    if export_path.stat().st_size>200_000_000:
        raise JMDNativeOwnerError("export exceeds original builder size cap")
    if sha256(export_path.read_bytes()).hexdigest()!=expected_export_sha:
        raise JMDNativeOwnerError("original native export digest mismatch")
    spec=importlib.util.spec_from_file_location("selected_jmd_native_ast_owner",
                                               source_path)
    if spec is None or spec.loader is None:
        raise JMDNativeOwnerError("JMD owner source not loadable")
    owner=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(owner)
    for name in ("nodes_from_export","reachable","expression_fingerprint"):
        if not callable(getattr(owner,name,None)):
            raise JMDNativeOwnerError("JMD owner missing real parser: "+name)
    world=owner.nodes_from_export(export_path)
    if world.get("sha")!=expected_export_sha:
        raise JMDNativeOwnerError("original builder export hash mismatch")
    meta=world.get("meta")
    if not isinstance(meta,dict):
        raise JMDNativeOwnerError("native exporter meta missing")
    lean=meta.get("lean")
    compiler=lean.get("githash") if isinstance(lean,dict) else None
    if type(compiler) is not str or not HEX40.fullmatch(compiler):
        raise JMDNativeOwnerError("original Lean compiler revision not pinned")
    matches=[]
    for kind,info in world["decls"]:
        if not isinstance(info,dict) or "name" not in info or "type" not in info:
            continue
        named=world["names"].get(info["name"])
        if named==declaration:matches.append((kind,info))
    if len(matches)!=1:
        raise JMDNativeOwnerError("native builder selected declaration missing/ambiguous")
    kind,info=matches[0]
    ty=info["type"]
    type_nodes,type_refs=owner.reachable(ty,world["exprs"],world["names"])
    type_fp=owner.expression_fingerprint(
        ty,world["exprs"],world["names"],world["levels"])
    value_refs=set()
    value_nodes=set()
    proof_fp=None
    if type(info.get("value")) is int:
        value_nodes,value_refs=owner.reachable(
            info["value"],world["exprs"],world["names"])
        proof_fp=owner.expression_fingerprint(
            info["value"],world["exprs"],world["names"],world["levels"])
    return {
        "status":"jmd-native-builder-readonly-roots-validated",
        "builder_source_sha256":sha256(source_path.read_bytes()).hexdigest(),
        "native_export_sha256":expected_export_sha,
        "selected_declaration":declaration,
        "declaration_kind":kind,
        "original_lean_revision":compiler,
        "indexed_native_expr_count":len(world["exprs"]),
        "selected_type_reachable_nodes":len(type_nodes),
        "selected_proof_reachable_nodes":len(value_nodes),
        "type_fingerprint_candidate_only":type_fp,
        "proof_fingerprint_candidate_only":proof_fp,
        "direct_type_constants":sorted(type_refs),
        "direct_proof_constants":sorted(value_refs),
        "used_original_jmd_builder_parser":True,
        "wrote_another_world_database":False,
        "typechecked_by_lean_here":False,
        "world_admitted":False
    }
