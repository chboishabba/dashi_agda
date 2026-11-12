#!/usr/bin/env python3
"""Bounded native lean4export 3.x DAG projection; NOT a Lean kernel checker.

Resolves source name/universe/expression indices, then serializes selected
types and proof terms as compact, structurally interned, index-independent
expression DAGs. Different serialization indices and sharing layouts cannot
create different canonical candidate identities. No hash injectivity is
assumed: the full canonical bytes are carried to the world store.
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
    return json.dumps(value,ensure_ascii=False,sort_keys=True,
                      separators=(",",":")).encode("utf-8")

@dataclass(frozen=True)
class NativeCandidate:
    name: str
    kind: str
    canonical_type: bytes
    type_sha256: str
    direct_constants: tuple[str, ...]
    proof_value_present: bool
    proof_digest: str = ""
    proof_direct_constants: tuple[str, ...] = ()
    kernel_certified: bool = False
    canonical_proof: bytes = b""

def extract_candidates(raw: bytes, *, max_records: int=5_000_000,
                       selected_names: frozenset[str] | None = None):
    if type(raw) is not bytes or not raw or len(raw)>200_000_000:
        raise NativeV3Error("invalid native export size")
    names={0:""}
    name_shapes={0:("anon",)}
    levels={0:("zero",)}
    # Expressions contain CHILD IDS, never nested expanded child expressions.
    expressions={}
    selected=[]
    def ref(table,i,label):
        if not integer(i) or i not in table:
            raise NativeV3Error("unresolved "+label+" reference")
        return table[i]
    def intern(table,i,node,label,*,allow_zero=False):
        # Lean4export native v3 reserves Name 0 and Level 0, but Expr 0
        # is a real expression index. Its own Nat.add_succ export starts
        # with {"ie":0,"sort":1}; rejecting it blocks real source.
        if (not integer(i) or (i==0 and not allow_zero) or i in table):
            raise NativeV3Error("duplicate or invalid "+label+" index")
        table[i]=node
    def name(i): return ref(names,i,"name")
    def name_shape(i): return ref(name_shapes,i,"name shape")
    def level(i): return ref(levels,i,"universe")
    def expr(i):
        ref(expressions,i,"expression")
        return i
    def children(node):
        tag=node[0]
        if tag=="app": return (node[1],node[2])
        if tag in ("lam","forallE"): return (node[2],node[3])
        if tag=="letE": return (node[2],node[3],node[4])
        if tag=="proj": return (node[3],)
        if tag in ("alias","mdata"): return (node[1],)
        return ()
    def expression_dag(root):
        """Postorder structural interning with deterministic canonical IDs."""
        assigned={}
        interned={}
        nodes=[]
        stack=[(root,False)]
        while stack:
            index,leaving=stack.pop()
            if index in assigned:
                continue
            node=expressions[index]
            if not leaving:
                stack.append((index,True))
                for dependency in reversed(children(node)):
                    if dependency not in assigned:
                        stack.append((dependency,False))
                continue
            tag=node[0]
            if tag=="alias":
                assigned[index]=assigned[node[1]]
                continue
            if tag=="mdata":
                norm=("mdata",assigned[node[1]],node[2])
            elif tag=="app":
                norm=(tag,assigned[node[1]],assigned[node[2]])
            elif tag in ("lam","forallE"):
                norm=(tag,node[1],assigned[node[2]],
                      assigned[node[3]],node[4],node[5])
            elif tag=="letE":
                norm=(tag,node[1],assigned[node[2]],assigned[node[3]],
                      assigned[node[4]],node[5],node[6])
            elif tag=="proj":
                norm=(tag,node[1],node[2],assigned[node[3]],node[4])
            else:
                norm=node
            key=canonical(norm)
            if key not in interned:
                interned[key]=len(nodes)+1
                nodes.append(norm)
            assigned[index]=interned[key]
        return (assigned[root],nodes)
    def direct_constants(root):
        found=set()
        visited=set()
        pending=[root]
        while pending:
            index=pending.pop()
            if index in visited: continue
            visited.add(index)
            node=expressions[index]
            if node[0]=="const": found.add(node[1])
            pending.extend(children(node))
        return tuple(sorted(found))
    def root_tag(root):
        while expressions[root][0]=="alias":
            root=expressions[root][1]
        return expressions[root][0]
    kinds=("axiom","def","opaque","thm","quot")
    for count,line in enumerate(raw.splitlines(),1):
        if count>max_records or not line or len(line)>8_000_000:
            raise NativeV3Error("invalid native record length/count")
        try:
            obj=json.loads(line)
        except (ValueError,UnicodeError) as exc:
            raise NativeV3Error("invalid native JSONL") from exc
        if not isinstance(obj,dict):
            raise NativeV3Error("non-object native record")
        if count==1:
            metadata=obj.get("meta")
            fmt=metadata.get("format") if isinstance(metadata,dict) else None
            v=fmt.get("version") if isinstance(fmt,dict) else None
            if not isinstance(v,str) or not v.startswith("3."):
                raise NativeV3Error("unsupported native format")
            continue
        if "meta" in obj: raise NativeV3Error("duplicate metadata")
        tagged=[k for k in ("str","num","succ","max","imax","param",
                             "bvar","sort","const","app","lam","forallE",
                             "letE","proj","natVal","strVal","mdata",
                             *kinds,"inductive") if k in obj]
        if len(tagged)!=1:
            raise NativeV3Error("unsupported or multiply tagged native row")
        tag=tagged[0]
        value=obj[tag]
        if tag in ("str","num"):
            if not isinstance(value,dict):
                raise NativeV3Error("invalid name")
            prefix=name(value.get("pre"))
            segment=value.get("str") if tag=="str" else value.get("i")
            if tag=="str" and (type(segment) is not str or not segment):
                raise NativeV3Error("invalid string name")
            if tag=="num" and not integer(segment):
                raise NativeV3Error("invalid numeric name")
            index=obj.get("in")
            intern(names,index,(prefix+"." if prefix else "")+str(segment),"name")
            intern(name_shapes,index,(tag,name_shape(value.get("pre")),segment),
                   "name shape")
        elif tag in ("succ","max","imax","param"):
            if tag=="succ": node=("succ",level(value))
            elif tag=="param": node=("param",name(value),name_shape(value))
            else:
                if not isinstance(value,list) or len(value)!=2:
                    raise NativeV3Error("invalid universe pair")
                node=(tag,level(value[0]),level(value[1]))
            intern(levels,obj.get("il"),node,"universe")
        elif "ie" in obj:
            if tag=="bvar":
                if not integer(value): raise NativeV3Error("invalid bvar")
                node=(tag,value)
            elif tag=="sort": node=(tag,level(value))
            elif tag=="const":
                if not isinstance(value,dict) or not isinstance(value.get("us"),list):
                    raise NativeV3Error("invalid constant")
                node=(tag,name(value.get("name")),
                      tuple(level(i) for i in value["us"]),
                      name_shape(value.get("name")))
            elif tag=="app":
                node=(tag,expr(value["fn"]),expr(value["arg"]))
            elif tag in ("lam","forallE"):
                if value.get("binderInfo") not in (
                    "default","implicit","strictImplicit","instImplicit"):
                    raise NativeV3Error("invalid binder information")
                node=(tag,name(value["name"]),expr(value["type"]),
                      expr(value["body"]),value["binderInfo"],
                      name_shape(value["name"]))
            elif tag=="letE":
                if type(value.get("nondep")) is not bool:
                    raise NativeV3Error("invalid let dependency")
                node=(tag,name(value["name"]),expr(value["type"]),
                      expr(value["value"]),expr(value["body"]),value["nondep"],
                      name_shape(value["name"]))
            elif tag=="proj":
                if not integer(value.get("idx")):
                    raise NativeV3Error("invalid projection index")
                node=(tag,name(value["typeName"]),value["idx"],expr(value["struct"]),
                      name_shape(value["typeName"]))
            elif tag=="natVal":
                if type(value) is not str or not value.isascii() or not value.isdecimal():
                    raise NativeV3Error("invalid natural literal")
                node=(tag,str(int(value)))
            elif tag=="strVal":
                if type(value) is not str: raise NativeV3Error("invalid string literal")
                node=(tag,value)
            elif tag=="mdata":
                if (not isinstance(value,dict) or
                    not isinstance(value.get("data"),dict)):
                    raise NativeV3Error("invalid native metadata payload")
                node=("mdata",expr(value["expr"]),value["data"])
            else:
                raise NativeV3Error("unsupported expression node")
            intern(expressions,obj.get("ie"),node,"expression",allow_zero=True)
        elif tag in kinds:
            if not isinstance(value,dict):
                raise NativeV3Error("invalid native declaration")
            declaration=name(value.get("name"))
            typ=expr(value.get("type"))
            params=value.get("levelParams")
            if not declaration or not isinstance(params,list):
                raise NativeV3Error("invalid declaration header")
            universes=tuple(name(i) for i in params)
            has_proof=tag in ("thm","def","opaque")
            proof=expr(value.get("value")) if has_proof else None
            if selected_names is not None and declaration not in selected_names:
                continue
            type_bytes=canonical(("lean4export-v3-type-dag-v1",universes,
                                  root_tag(typ),expression_dag(typ)))
            if len(type_bytes)>8_000_000:
                raise NativeV3Error("selected type DAG exceeds size budget")
            proof_bytes=canonical(expression_dag(proof)) if has_proof else b""
            if len(proof_bytes)>8_000_000:
                raise NativeV3Error("selected proof DAG exceeds size budget")
            selected.append(NativeCandidate(
                declaration,tag,type_bytes,sha256(type_bytes).hexdigest(),
                tuple(x for x in direct_constants(typ) if x!=declaration),
                has_proof,sha256(proof_bytes).hexdigest() if has_proof else "",
                tuple(x for x in direct_constants(proof) if x!=declaration)
                    if has_proof else (),False,proof_bytes))
        else:
            # Grouped inductive constants are kernel-atomic: record references
            # are checked here but the group is NOT promoted or projected.
            if not isinstance(value,dict) or any(
                not isinstance(value.get(k),list) for k in ("types","ctors","recs")
            ) or not value["types"]:
                raise NativeV3Error("invalid or empty inductive group")
            for group in ("types","ctors","recs"):
                for item in value[group]:
                    if not isinstance(item,dict):
                        raise NativeV3Error("invalid inductive member")
                    name(item.get("name"));expr(item.get("type"))
    if not selected:
        raise NativeV3Error("no supported selected declaration")
    if len({d.name for d in selected})!=len(selected):
        raise NativeV3Error("duplicate declaration name")
    return tuple(selected)
