#!/usr/bin/env python3
"""Structural Lean4export 3.x declaration projection, NOT a type checker.

Turns export integer name/level/expression references into an index-independent
canonical expression representation. Rejects absent, duplicate, forward and
cyclic term references. A separate trusted Lean kernel must check typing,
definitional equality and the actual proof term. Never infer certification here.
Reference: leanprover/lean4export format_ndjson.md (3.1).
"""
from __future__ import annotations
from dataclasses import dataclass
from hashlib import sha256
import json

class NativeV3Error(ValueError):
    pass

def integer(value):
    return type(value) is int and value >= 0

def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":")).encode("utf-8")

@dataclass(frozen=True)
class NativeCandidate:
    name: str
    kind: str
    canonical_type: bytes
    type_sha256: str
    direct_constants: tuple[str, ...]
    proof_value_present: bool
    kernel_certified: bool = False

def extract_candidates(raw: bytes, *, max_records: int=5_000_000):
    if not isinstance(raw, bytes) or not raw or len(raw) > 200_000_000:
        raise NativeV3Error("invalid native export size")
    names = {0: ""}
    levels = {0: ("zero",)}
    expressions = {}
    candidates = []
    def ref(table, value, label):
        if not integer(value) or value not in table:
            raise NativeV3Error("unresolved "+label+" reference")
        return table[value]
    def intern(table, id_value, value, label):
        if not integer(id_value) or id_value == 0 or id_value in table:
            raise NativeV3Error("duplicate or invalid "+label+" index")
        table[id_value] = value
    def name_ref(i):
        return ref(names, i, "name")
    def expr_ref(i):
        return ref(expressions, i, "expression")
    def level_ref(i):
        return ref(levels, i, "universe")
    kinds = ("axiom","def","opaque","thm","quot")
    rows=0
    for line in raw.splitlines():
        rows+=1
        if rows > max_records or not line or len(line)>8_000_000:
            raise NativeV3Error("invalid record length or count")
        try:
            obj=json.loads(line)
        except (ValueError, UnicodeError) as exc:
            raise NativeV3Error("invalid NDJSON") from exc
        if not isinstance(obj,dict):
            raise NativeV3Error("non-object record")
        if rows == 1:
            meta=obj.get("meta")
            fmt=meta.get("format") if isinstance(meta,dict) else None
            version=fmt.get("version") if isinstance(fmt,dict) else None
            if not isinstance(version,str) or not version.startswith("3."):
                raise NativeV3Error("unsupported native format")
            continue
        if "meta" in obj:
            raise NativeV3Error("duplicate metadata")
        tagged = [k for k in ("str","num","succ","max","imax","param",
                               "bvar","sort","const","app","lam","forallE",
                               "letE","proj","natVal","strVal","mdata",
                               *kinds,"inductive") if k in obj]
        if len(tagged)!=1:
            raise NativeV3Error("unsupported or multiply tagged record")
        tag=tagged[0]
        val=obj[tag]
        if tag in ("str","num"):
            if not isinstance(val,dict):
                raise NativeV3Error("invalid name record")
            prefix=name_ref(val.get("pre"))
            segment=val.get("str") if tag=="str" else val.get("i")
            if tag=="str" and (not isinstance(segment,str) or not segment):
                raise NativeV3Error("invalid name segment")
            if tag=="num" and not integer(segment):
                raise NativeV3Error("invalid numeric name")
            intern(names,obj.get("in"),
                   (prefix+"." if prefix else "")+str(segment),"name")
        elif tag in ("succ","max","imax","param"):
            if tag=="succ":
                node=("succ",level_ref(val))
            elif tag=="param":
                node=("param",name_ref(val))
            else:
                if not isinstance(val,list) or len(val)!=2:
                    raise NativeV3Error("invalid universe pair")
                node=(tag,level_ref(val[0]),level_ref(val[1]))
            intern(levels,obj.get("il"),node,"universe")
        elif "ie" in obj:
            if tag=="bvar":
                if not integer(val): raise NativeV3Error("invalid bvar")
                node=("bvar",val)
            elif tag=="sort":
                node=("sort",level_ref(val))
            elif tag=="const":
                if not isinstance(val,dict) or not isinstance(val.get("us"),list):
                    raise NativeV3Error("invalid constant")
                node=("const",name_ref(val.get("name")),
                      tuple(level_ref(i) for i in val["us"]))
            elif tag=="app":
                node=("app",expr_ref(val["fn"]),expr_ref(val["arg"]))
            elif tag in ("lam","forallE"):
                if val.get("binderInfo") not in (
                    "default","implicit","strictImplicit","instImplicit"):
                    raise NativeV3Error("invalid binder info")
                node=(tag,name_ref(val["name"]),expr_ref(val["type"]),
                      expr_ref(val["body"]),val["binderInfo"])
            elif tag=="letE":
                if type(val.get("nondep")) is not bool:
                    raise NativeV3Error("invalid let nondep")
                node=(tag,name_ref(val["name"]),expr_ref(val["type"]),
                      expr_ref(val["value"]),expr_ref(val["body"]),val["nondep"])
            elif tag=="proj":
                if not integer(val.get("idx")):
                    raise NativeV3Error("invalid projection index")
                node=(tag,name_ref(val["typeName"]),val["idx"],expr_ref(val["struct"]))
            elif tag=="natVal":
                if not isinstance(val,str) or not val.isascii() or not val.isdecimal():
                    raise NativeV3Error("invalid natural literal")
                node=(tag,str(int(val)))
            elif tag=="strVal":
                if not isinstance(val,str): raise NativeV3Error("invalid string literal")
                node=(tag,val)
            elif tag=="mdata":
                if not isinstance(val,dict):
                    raise NativeV3Error("invalid metadata expression")
                node=expr_ref(val["expr"])
            else:
                raise NativeV3Error("unsupported expression form")
            intern(expressions,obj["ie"],node,"expression")
        elif tag in kinds:
            if not isinstance(val,dict):
                raise NativeV3Error("invalid declaration")
            name=name_ref(val.get("name"))
            typ=expr_ref(val.get("type"))
            params=val.get("levelParams")
            if not name or not isinstance(params,list):
                raise NativeV3Error("invalid declaration header")
            universe_params=tuple(name_ref(i) for i in params)
            value_present=tag in ("thm","def","opaque")
            if value_present:
                expr_ref(val.get("value"))
            canonical_type=canonical(("lean4export-v3-type",universe_params,typ))
            constants=set()
            pending=[typ]
            # Walk fully expanded trees; avoid recursion over deep terms.
            while pending:
                item=pending.pop()
                if isinstance(item,(tuple,list)):
                    if item and item[0]=="const":
                        constants.add(item[1])
                    pending.extend(item[1:])
            candidates.append(NativeCandidate(
                name,tag,canonical_type,sha256(canonical_type).hexdigest(),
                tuple(sorted(constants-{name})),value_present))
        else:
            # Mutual inductive blocks are not safe to project piecemeal:
            # checker validation and group semantics are both required.
            raise NativeV3Error("inductive group projection not implemented")
    if not candidates:
        raise NativeV3Error("no supported declarations")
    if len({c.name for c in candidates})!=len(candidates):
        raise NativeV3Error("duplicate declaration name")
    return tuple(candidates)
