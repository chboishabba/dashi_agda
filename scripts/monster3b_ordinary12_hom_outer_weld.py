#!/usr/bin/env python3
"""M3B-L10B/L12R exact Q(zeta3) intertwiner and outer automorphism solver.

There is NO way to compute numerical characteristic-zero Monster Hom vectors
from an MMV(7) sample. This module accepts an *actual source-backed* 12D
Hom action as a separate input, solves F A_g = B_g F over Q(zeta3),
checks source word identities, and constructs the paired outer transport
once the actual 6.Suz outer action word map is specified. It never calls a
synthetic chart 'the Monster Hom' by fiat.

  --source     genuine Steel 12-generator JSON from original Magma export
  --hom        12x12 characteristic-zero actual Hom action JSON, compatible
               labels; file must retain original Monster provenance/Weil gauge
  --outer-map  optional finite source outer automorphism word map JSON
  --out        output exact F, and outer semilinear intertwiner if supplied

Without --hom it writes an honest NEEDS_CHAR0_HOM_ACTION ledger. A matrix
intertwiner is only a genuine Monster identification if that source Hom
action is independently extracted from the actual W_s, not merely relabelled.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from sympy import Rational, sqrt, simplify, re, im, conjugate
from sympy.polys.domains import QQ
from sympy.polys.matrices import DomainMatrix

K=QQ.algebraic_field(sqrt(-3))
Z=K.from_sympy((-1+sqrt(-3))/2)
ZERO,ONE=K.zero,K.one
def to_field(cell):
    if not isinstance(cell,list) or len(cell)!=2: raise ValueError("expected [a,b] Q(zeta3)")
    return K.from_sympy(Rational(cell[0])+Rational(cell[1])*(-1+sqrt(-3))/2)
def from_field(x):
    s=K.to_sympy(x)
    b=simplify(2*im(s)/sqrt(3))
    a=simplify(re(s)+b/2)
    if a.is_Rational is not True or b.is_Rational is not True:
        raise ValueError("element not in rational ζ3 coordinates")
    return [str(a),str(b)]
def readmatrix(raw,n=12):
    if (not isinstance(raw,list) or len(raw)!=n or
        any(not isinstance(row,list) or len(row)!=n for row in raw)):
        raise ValueError(f"expected {n}x{n} matrix")
    return [[to_field(x) for x in row] for row in raw]
def matmul(A,B):
    return [[sum((A[i][k]*B[k][j] for k in range(len(A))),ZERO)
             for j in range(len(B[0]))] for i in range(len(A))]
def unit(n): return [[ONE if i==j else ZERO for j in range(n)] for i in range(n)]
def inv(A):
    D=DomainMatrix(A,(len(A),len(A)),K)
    return D.inv().to_list()
def sigma(A):
    return [[K.from_sympy(conjugate(K.to_sympy(x)))
             for x in row] for row in A]
def transpose(A): return [list(row) for row in zip(*A)]
def sym_square(B):
    # Exact polynomial basis e_i e_j (i<=j) over Q(zeta3).
    n=len(B); pairs=[(i,j) for i in range(n) for j in range(i,n)]
    S=[[ZERO for _ in pairs] for _ in pairs]
    for col,(i,j) in enumerate(pairs):
        for row,(u,v) in enumerate(pairs):
            if i==j:
                z=B[u][i]*B[v][i]
                S[row][col]=z if u==v else K.from_sympy(Rational(2))*z
            elif u==v: S[row][col]=B[u][i]*B[u][j]
            else: S[row][col]=B[u][i]*B[v][j]+B[v][i]*B[u][j]
    return S
def block(A,B):
    n,m=len(A),len(B)
    return [list(row)+[ZERO]*m for row in A] + [
        [ZERO]*n+list(row) for row in B]
def word_value(word,gens):
    if not isinstance(word,list): raise ValueError("word must be list of generator tokens")
    if not gens: raise ValueError("no source generators")
    n=len(next(iter(gens.values())))
    total=unit(n)
    for token in word:
        if not isinstance(token,str) or not token:
            raise ValueError("empty word token")
        invert=token.endswith("^-1"); label=token[:-3] if invert else token
        if label not in gens:raise ValueError(f"source word generator absent: {label}")
        A=inv(gens[label]) if invert else gens[label]
        total=matmul(total,A)
    return total
def hom_nullspace(pairs):
    """Rows solve F A - B F = 0 with row-major variables over K."""
    n=len(pairs[0][0])
    rows=[]
    for A,B in pairs:
        for i in range(n):
            for j in range(n):
                row=[ZERO]*(n*n)
                for k in range(n):
                    row[i*n+k]+=A[k][j]
                    row[k*n+j]-=B[i][k]
                rows.append(row)
    null=DomainMatrix(rows,(len(rows),n*n),K).nullspace().to_list()
    matrices=[[[v[i*n+j] for j in range(n)] for i in range(n)] for v in null]
    return matrices
def find_weld(pairs):
    bases=hom_nullspace(pairs)
    if not bases:
        raise ValueError("NO intertwiner over Q(zeta3); source/target mismatch")
    if len(bases)!=1:
        raise ValueError(f"Hom dimension {len(bases)}; no canonical unique weld")
    F=bases[0]
    # Normalize first nonzero entry to 1. This fixes one scalar gauge but
    # NOT the source Monster Heisenberg/normalizer central-cover gauge.
    pivot=next((x for row in F for x in row if x!=ZERO),None)
    if pivot is None: raise ValueError("zero Hom witness")
    F=[[x*(ONE/pivot) for x in row] for row in F]
    invert=inv(F)
    for A,B in pairs:
        if matmul(F,A)!=matmul(B,F):
            raise AssertionError("intertwiner equation failed exact field check")
    return F, len(bases),invert
def run(src,hom,outer):
    if src.get("schema")!="monster3b-steel6suz-ordinary12-v1":
        raise ValueError("not the original Steel ordinary12 source export")
    genes={k:readmatrix(v) for k,v in src["generators"].items()}
    out={"schema":"monster3b-ordinary12-Hom-outer-weld-v1",
         "original_steel_source":src["source"],
         "selected_6Suz_12_irr_position":src.get("selected_6Suz_12_irr_position"),
         "actual_MM_complex_Monster_Hom_source_produced_here":False,
         "source_group_word_to_MM_4D_identified":False}
    if hom is None:
        out["status"]="NEEDS_CHARACTERISTIC_ZERO_MONSTER_HOM12_ACTION"
        out["missing_exact_source"]=[
            "original W_s complex 196884D action / characteristic-zero 12D Hom extraction",
            "same E and source 729 Weil extension gauge",
            "genuine 6.Suz generators matched to source words"]
        return out
    if hom.get("schema")!="monster3b-original-Wzeta-Hom12-generator-action-v1":
        raise ValueError("Hom packet must name actual characteristic-zero Monster source contract")
    hg={k:readmatrix(v) for k,v in hom.get("generators",{}).items()}
    if not genes or set(genes)!=set(hg):
        raise ValueError("Steel and true Monster Hom generator names do not match")
    pairs=[(genes[k],hg[k]) for k in genes]
    F,dimension,Finv=find_weld(pairs)
    out.update(status="CONDITIONAL_EXACT_HOM12_INTERTWINER",
        original_Hom_source_metadata=hom.get("source"),
        one_dimensional_intertwiner=True,
        source_to_Hom_F=[[from_field(x) for x in row] for row in F],
        Hom_to_source_F_inv=[[from_field(x) for x in row] for row in Finv],
        hom_source_input_authenticated_against_Monster_here=False)
    if outer is not None:
        if outer.get("schema")!="monster3b-6Suz-outer-word-map-v1":
            raise ValueError("wrong outer source word map")
        words=outer.get("alpha_on_generators",{})
        if set(words)!=set(genes):raise ValueError("outer automorphism missing source generator")
        # Opposite-phase module is σ(V). Outer transport is semilinear:
        # U σ(A_g) = A_{alpha(g)} U; this is a Qζ-linear problem for U.
        twisted=[(sigma(genes[k]),word_value(words[k],genes)) for k in genes]
        U,udim,Uinv=find_weld(twisted)
        # Derived 78 and 90 *semilinear* maps automatically follow the
        # source 12 map, but their common outer-square central scalar is
        # not fixed until the authentic 6.Suz.2 / Monster word is attached.
        U78=sym_square(transpose(Uinv))
        U90=block(U,U78)
        outer_square12=matmul(U,sigma(U))
        outer_square90=matmul(U90,sigma(U90))
        out["outer_phase_exchange"]={
            "status":"CONDITIONAL_OUTER_SEMILINEAR_INTERTWINER",
            "U12_rows_Qzeta3":[[from_field(x) for x in row] for row in U],
            "derived_U78_rows_Qzeta3":[[from_field(x) for x in row] for row in U78],
            "derived_U90_rows_Qzeta3":[[from_field(x) for x in row] for row in U90],
            "alpha_source_words":words,
            "source_MM_4D_generator_identified":False,
            "actual_729_Weil_outer_gauge_identified":False,
            "outer_square_source12":[
                [from_field(x) for x in row] for row in outer_square12],
            "outer_square_source90":[
                [from_field(x) for x in row] for row in outer_square90],
            "outer_square_central_cover_scalar_attached":False}
    return out
def selftest():
    # Toy noncommuting GL2 rep with identical target: Hom space = scalars.
    A=[[ZERO,ONE],[ONE,ZERO]]
    B=[[ONE,ONE],[ZERO,ONE]]
    F,d,_=find_weld([(A,A),(B,B)])
    assert F==unit(2) and d==1
    # The C3 phase of faithful ζI12 remains ζ on dual Sym²: -2=1 mod3.
    assert (Z**(-2))==Z
    return {"toy_GL2_noncommuting_unique_Hom":"PASS",
            "dual_C3_same_phase":"PASS",
            "actual_196884D_Monster_Hom_tested":False}
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source",type=Path)
    p.add_argument("--hom",type=Path)
    p.add_argument("--outer-map",type=Path)
    p.add_argument("--out",type=Path,default=Path(
        ".dashi/monster3b-steel-ordinary12/ordinary12_hom_outer_weld.json"))
    p.add_argument("--selftest",action="store_true")
    a=p.parse_args()
    if a.selftest: result=selftest()
    else:
        if a.source is None:p.error("--source genuine Steel 12 JSON required")
        result=run(json.loads(a.source.read_text()),
                   json.loads(a.hom.read_text()) if a.hom else None,
                   json.loads(a.outer_map.read_text()) if a.outer_map else None)
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(result["status"] if "status" in result else "SELFTEST",a.out)
if __name__=="__main__":main()
