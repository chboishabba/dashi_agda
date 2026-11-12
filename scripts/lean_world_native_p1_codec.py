#!/usr/bin/env python3
"""Lossless projected Lean4export v3 Expr DAG vs binder-alpha candidate identity.

Source text is stored separately. Even a lossless exporter payload is not a
Lean kernel judgment. Metadata is preserved when emitted; the exporter can
omit it upstream. Constant Name.str/Name.num, universes and literals survive
alpha normalization. Never turn an alpha key into an equivalence certificate.
"""
from __future__ import annotations
from hashlib import sha256
import json

class P1CodecError(ValueError): pass

def encode(obj):
    return json.dumps(obj,sort_keys=True,ensure_ascii=False,
                      separators=(",",":")).encode("utf-8")

def _read(raw):
    if type(raw) is not bytes or not raw or len(raw)>8_000_000:
        raise P1CodecError("missing or oversized exported Expr")
    try: obj=json.loads(raw)
    except (ValueError,UnicodeError) as exc:
        raise P1CodecError("invalid exported Expr JSON") from exc
    if encode(obj)!=raw:
        raise P1CodecError("noncanonical exported Expr JSON")
    return obj

def _children(node):
    tag=node[0]
    if tag=="app": return (node[1],node[2])
    if tag in ("lam","forallE"): return (node[2],node[3])
    if tag=="letE": return (node[2],node[3],node[4])
    if tag=="proj": return (node[3],)
    if tag=="mdata": return (node[1],)
    if tag in ("bvar","sort","const","natVal","strVal"): return ()
    raise P1CodecError("unsupported native Expr constructor")

def _dag(obj):
    if (type(obj) is not list or len(obj)!=2 or
        type(obj[0]) is not int or type(obj[1]) is not list or
        not obj[1] or len(obj[1])>2_000_000):
        raise P1CodecError("invalid projected Expr DAG envelope")
    root,nodes=obj
    if not 1<=root<=len(nodes):raise P1CodecError("invalid Expr root")
    arity={"bvar":2,"sort":2,"const":4,"app":3,"lam":6,
           "forallE":6,"letE":7,"proj":5,"natVal":2,
           "strVal":2,"mdata":3}
    for i,n in enumerate(nodes,1):
        if type(n) is not list or not n or n[0] not in arity or len(n)!=arity[n[0]]:
            raise P1CodecError("invalid Expr constructor arity")
        if n[0] in ("lam","forallE") and n[4] not in (
            "default","implicit","strictImplicit","instImplicit"):
            raise P1CodecError("invalid binder info")
        if n[0]=="letE" and type(n[5]) is not bool:
            raise P1CodecError("invalid let dependency")
        if n[0]=="mdata" and type(n[2]) is not dict:
            raise P1CodecError("invalid exported metadata")
        for c in _children(n):
            if type(c) is not int or not 1<=c<i:
                raise P1CodecError("unresolved or forward Expr reference")
    seen=set()
    stack=[root]
    while stack:
        i=stack.pop()
        if i in seen:continue
        seen.add(i)
        stack.extend(_children(nodes[i-1]))
    if len(seen)!=len(nodes):
        raise P1CodecError("unreachable Expr node")
    return root,nodes

def parse_type(raw):
    x=_read(raw)
    if (type(x) is not list or len(x)!=4 or
        x[0]!="lean4export-v3-type-dag-v1" or
        type(x[1]) is not list or
        any(type(p) is not str for p in x[1]) or
        len(set(x[1]))!=len(x[1]) or type(x[2]) is not str):
        raise P1CodecError("invalid projected type envelope")
    root,nodes=_dag(x[3])
    if nodes[root-1][0]!=x[2]:raise P1CodecError("type root tag mismatch")
    return x[1],root,nodes

def _level(l,params):
    if type(l) is not list or not l:raise P1CodecError("invalid level")
    tag=l[0]
    if tag=="zero" and len(l)==1:return ["zero"]
    if tag=="param" and len(l)==3:
        if l[1] not in params:raise P1CodecError("unbound universe")
        return ["param",params.index(l[1])]
    if tag=="succ" and len(l)==2:return ["succ",_level(l[1],params)]
    if tag in ("max","imax") and len(l)==3:
        return [tag,_level(l[1],params),_level(l[2],params)]
    raise P1CodecError("invalid universe expression")

def alpha_type(raw):
    """Typed structural candidate key, never mathematical proof authority."""
    params,root,nodes=parse_type(raw)
    assigned={}
    interned={}
    output=[]
    for i,n in enumerate(nodes,1):
        tag=n[0]
        if tag=="mdata":
            assigned[i]=assigned[n[1]]
            continue
        if tag=="app": norm=[tag,assigned[n[1]],assigned[n[2]]]
        elif tag in ("lam","forallE"):
            norm=[tag,assigned[n[2]],assigned[n[3]],n[4]]
        elif tag=="letE":
            norm=[tag,assigned[n[2]],assigned[n[3]],assigned[n[4]],n[5]]
        elif tag=="proj":norm=[tag,n[4],n[2],assigned[n[3]]]
        elif tag=="sort":norm=[tag,_level(n[1],params)]
        elif tag=="const":
            if type(n[2]) is not list:raise P1CodecError("invalid constant levels")
            norm=[tag,n[3],[_level(v,params) for v in n[2]]]
        else:norm=n
        key=encode(norm)
        if key not in interned:
            interned[key]=len(output)+1
            output.append(norm)
        assigned[i]=interned[key]
    return encode(["lean4export-v3-alpha-type-dag-v1",len(params),
                   assigned[root],output])

def exact_type_roundtrip(raw):
    params,root,nodes=parse_type(raw)
    result=encode(["lean4export-v3-type-dag-v1",params,
                   nodes[root-1][0],[root,nodes]])
    if result!=raw:raise P1CodecError("exported type roundtrip failed")
    return result

def exact_proof_roundtrip(raw):
    root,nodes=_dag(_read(raw))
    result=encode([root,nodes])
    if result!=raw:raise P1CodecError("exported proof roundtrip failed")
    return result

def candidate_receipt(candidate,*,toolchain,source_sha256,export_sha256):
    if not all(type(s) is str and s for s in (
            toolchain,source_sha256,export_sha256)):
        raise P1CodecError("missing original export/source identity")
    exact=exact_type_roundtrip(candidate.canonical_type)
    alpha=alpha_type(exact)
    proof=candidate.canonical_proof
    if candidate.proof_value_present:
        exact_proof_roundtrip(proof)
        if sha256(proof).hexdigest()!=candidate.proof_digest:
            raise P1CodecError("inconsistent original proof digest")
    elif proof:
        raise P1CodecError("unexpected proof bytes")
    return {"schema":"dashi-native-v3-p1-expr-observation-v1",
            "status":"exported-expression-roundtrip-candidate",
            "declaration":candidate.name,"toolchain":toolchain,
            "source_sha256":source_sha256,"export_sha256":export_sha256,
            "exact_exported_type_sha256":sha256(exact).hexdigest(),
            "alpha_type_sha256":sha256(alpha).hexdigest(),
            "exact_exported_proof_sha256":sha256(proof).hexdigest() if proof else None,
            "exact_type_bytes":exact,"alpha_type_bytes":alpha,
            "exact_proof_bytes":proof,
            "exported_expr_roundtrip":True,
            "original_source_text_reconstructed_by_this_codec":False,
            "kernel_certified":False,"world_admitted":False}
