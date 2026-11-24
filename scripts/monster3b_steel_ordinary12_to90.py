#!/usr/bin/env python3
"""Monster 3B: acquire Steel's ordinary 6.Suz faithful12 and derive the exact
90D inner generators over Q(zeta3) from 12D input. NEVER substitute GF3
2.Suz:2 quotient matrices or assert mmgroup-word/Hom identification.

Run:
  python3 scripts/monster3b_steel_ordinary12_to90.py --acquire
  python3 scripts/monster3b_steel_ordinary12_to90.py --schema
  python3 scripts/monster3b_steel_ordinary12_to90.py --matrix-json source12.json

Original source: Allan Steel, Ordinary Representations Database, 2012
(updated 2024), d12.6Suz.nfdeg2.M. Downloaded source is never evaluated
as Python; its Magma source syntax must be inspected separately.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path
import re
import urllib.request

URL="https://magma.maths.usyd.edu.au/~allan/reps/db/d12.6Suz.nfdeg2.M"
SCHEMA="monster3b-steel6suz-ordinary12-v1"
O=(Q(0),Q(0))
I=(Q(1),Q(0))
T=(Q(2),Q(0))
H=(Q(1,2),Q(0))

def plus(x,y): return (x[0]+y[0],x[1]+y[1])
def minus(x,y): return (x[0]-y[0],x[1]-y[1])
def mult(x,y):
    a,b=x; c,d=y
    return (a*c-b*d,a*d+b*c-b*d)
def conjugate(x): return (x[0]-x[1],-x[1])
def invert_scalar(x):
    a,b=x
    n=a*a-a*b+b*b
    if n==0: raise ZeroDivisionError("zero pivot Q(zeta3)")
    return ((a-b)/n,-b/n)
def total(xs):
    s=O
    for x in xs: s=plus(s,x)
    return s
def tr(A): return total(A[i][i] for i in range(len(A)))
def transpose(A): return [list(row) for row in zip(*A)]
def product(A,B):
    n=len(A)
    return [[total(mult(A[i][k],B[k][j]) for k in range(n))
             for j in range(n)] for i in range(n)]
def inverse_matrix(A):
    n=len(A)
    M=[row.copy()+[I if i==j else O for j in range(n)]
       for i,row in enumerate(A)]
    for j in range(n):
        k=next((i for i in range(j,n) if M[i][j]!=O),None)
        if k is None: raise ValueError("singular original ordinary 12")
        M[j],M[k]=M[k],M[j]
        fac=invert_scalar(M[j][j])
        M[j]=[mult(fac,x) for x in M[j]]
        for i in range(n):
            if i!=j and M[i][j]!=O:
                fac=M[i][j]
                M[i]=[minus(a,mult(fac,b)) for a,b in zip(M[i],M[j])]
    return [r[n:] for r in M]
def symmetric_square(B):
    """Polynomial basis e_i*e_j, i<=j; exact column-vector action."""
    n=len(B); pairs=[(i,j) for i in range(n) for j in range(i,n)]
    S=[[O for _ in pairs] for _ in pairs]
    for col,(i,j) in enumerate(pairs):
        for row,(u,v) in enumerate(pairs):
            if i==j:
                z=mult(B[u][i],B[v][i])
                S[row][col]=z if u==v else mult(T,z)
            elif u==v:
                S[row][col]=mult(B[u][i],B[u][j])
            else:
                S[row][col]=plus(mult(B[u][i],B[v][j]),
                                 mult(B[v][i],B[u][j]))
    return S
def pair(x): return [str(x[0]),str(x[1])]
def unpack(raw):
    if not isinstance(raw,list) or len(raw)!=12 or any(
       not isinstance(r,list) or len(r)!=12 for r in raw):
        raise ValueError("12x12 rational-pair matrix required")
    A=[]
    for row in raw:
        out=[]
        for x in row:
            if not isinstance(x,list) or len(x)!=2 or any(
                 not isinstance(v,str) for v in x):
                raise ValueError('entry must be two rational strings [a,b] for a+b*zeta')
            out.append((Q(x[0]),Q(x[1])))
        A.append(out)
    return A
def pack(A): return [[pair(v) for v in row] for row in A]
def block(A,S):
    n,m=len(A),len(S)
    return [r+[O]*m for r in A]+[[O]*n+r for r in S]
def build(data,outpath):
    if data.get("schema")!=SCHEMA: raise ValueError("source12 schema mismatch")
    source=data.get("source")
    if not isinstance(source,dict) or source.get("url")!=URL or not re.fullmatch(
       "[a-f0-9]{64}",str(source.get("sha256",""))):
        raise ValueError("original Steel URL and SHA256 mandatory")
    if data.get("field_polynomial")!=[1,1,1]:
        raise ValueError("Q(zeta3) field polynomial must be [1,1,1]")
    if data.get("matrix_convention")!="left_action_column_vectors":
        raise ValueError("explicit left-action column-vector convention required")
    if data.get("selected_6Suz_12_irr_position") not in (153,154):
        raise ValueError("selected GAP 6.Suz 12 Irr must be 153 or154")
    genes=data.get("generators")
    if not isinstance(genes,dict) or not genes:
        raise ValueError("explicit ordinary source12 generator matrices required")
    result={
       "schema":"monster3b-ordinary12-dual-sym2-90-v1",
       "source":source,"field":"Q(zeta3), zeta3^2+zeta3+1=0",
       "claimed_6Suz_12_irr":data["selected_6Suz_12_irr_position"],
       "source_generator_to_6Suz_original_GAP_class_verified":False,
       "source_generator_to_Monster_mmgroup_word_verified":False,
       "actual_Monster_Hom_intertwiner_verified":False,
       "central_C2_Hom_projector":{"trace":66,"rank_12":12,"rank_78":78,
          "Pi12":"(I-J)/2","Pi78":"(I+J)/2",
          "on_actual_90D_Hom_only_after_729_Weil_factor":True},
       "generators":{}}
    for name,src in genes.items():
        if not isinstance(name,str) or not name or len(name)>96:
            raise ValueError("bad generator name")
        A=unpack(src)
        B=transpose(inverse_matrix(A))
        S=symmetric_square(B)
        L=block(A,S)
        symtrace=mult(H,plus(mult(tr(B),tr(B)),tr(product(B,B))))
        if tr(S)!=symtrace:
            raise ValueError("Sym2 trace identity failed")
        # Finite group ordinary representation: dual character equals
        # complex conjugation of source character in Q(zeta3).
        source=tr(A); source2=tr(product(A,A))
        target=plus(source,mult(H,plus(mult(conjugate(source),conjugate(source)),
                                             conjugate(source2))))
        if tr(L)!=target:
            raise ValueError("source character does not match finite-group dual trace")
        result["generators"][name]={
            "source12":pack(A),"derived_dual_sym2_78":pack(S),
            "derived_90":pack(L),"trace_12":pair(source),
            "trace_78":pair(tr(S)),"trace_90":pair(tr(L))}
    outpath.parent.mkdir(parents=True,exist_ok=True)
    outpath.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    return result
def acquire(dest):
    dest.mkdir(parents=True,exist_ok=True)
    target=dest/"d12.6Suz.nfdeg2.M"
    if not target.exists():
        request=urllib.request.Request(URL,headers={
          "User-Agent":"Monster3B-source-study (original-author-attributed)"})
        with urllib.request.urlopen(request,timeout=35) as response:
            raw=response.read(16000001)
        if len(raw)>16000000: raise ValueError("unexpectedly large source")
        raw.decode("utf-8")
        if not raw.strip() or b"html" in raw[:100].lower():
            raise ValueError("download is empty or HTML, not original Magma")
        target.write_bytes(raw)
    raw=target.read_bytes()
    source=raw.decode("utf-8")
    if len(source)<100: raise ValueError("truncated Magma source")
    receipt={
       "source":{"url":URL,"sha256":hashlib.sha256(raw).hexdigest(),
                 "length":len(raw),"file":str(target)},
       "original_author":"Allan Steel (2012; updated 2024)",
       "source_executed":False,"source_republication_permission_assumed":False,
       "source_generator_GAP_class_verified":False,
       "Magma_module_variable_definitions":re.findall(
           r"(?m)^\s*([A-Za-z][A-Za-z0-9_]*)\s*:?=\s*[^;\n]{0,120}",source)[:30],
       "Magma_constructs":[x for x in ("AtlasGroup(","GModule(","ActionGenerators(",
                       "Matrix(","NumberField(") if x in source]}
    (dest/"source_inventory.json").write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--schema",action="store_true")
    p.add_argument("--acquire",action="store_true")
    p.add_argument("--source-root",type=Path,
       default=Path(".dashi/monster3b-steel-ordinary12"))
    p.add_argument("--matrix-json",type=Path)
    p.add_argument("--out",type=Path,
       default=Path(".dashi/monster3b-steel-ordinary12/ordinary12-derived90.json"))
    a=p.parse_args()
    if a.schema:
        print(json.dumps({"schema":SCHEMA,
          "source":{"url":URL,"sha256":"<actual original Magma file SHA256>"},
          "field_polynomial":[1,1,1],
          "matrix_convention":"left_action_column_vectors",
          "selected_6Suz_12_irr_position":153,
          "generators":{"label":"12x12 array of [rational_a,rational_b] pairs"}},
          indent=2))
        return
    if not a.acquire and not a.matrix_json:
        p.error("choose --acquire and/or --matrix-json")
    if a.acquire:
        receipt=acquire(a.source_root)
        print("STEEL_ORIGINAL_SHA256:",receipt["source"]["sha256"])
        print("STEEL_SOURCE:",receipt["source"]["file"])
        print("INVENTORY:",a.source_root/"source_inventory.json")
    if a.matrix_json:
        result=build(json.loads(a.matrix_json.read_text()),a.out)
        print("DERIVED_QZETA3_12_78_90:",a.out)
        print("GENERATORS:",len(result["generators"]))
        print("SAME_MONSTER_HOM_AND_WORDS_PAID:",False)
if __name__=="__main__":
    main()
