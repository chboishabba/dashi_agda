#!/usr/bin/env python3
"""Monster 3B P2/L10B/L12R: remove ALL E/Z(E) affine lift defects together.

Consumes the authentic symplectic-basis manifest from
monster_3b_mmgroup_source_symplectic_basis.py. It does not synthesize
Monster words and does not infer an ordinary complex representation from MMV(7).

The Heisenberg section is A^a B^b z^t with B_i A_j=z^delta A_j B_i.
Changing to the symmetric section t'=t-(a.b)/2 gives the canonical
normalizer action (v,t')->(M v,lambda*t'+ell(v)).
For an actual group word w, solve ell(v)+omega(u,Mv)=0 over F3 and
replace w by e(u)w. This determines an E-corrected word with zero
affine defect for EVERY v, not merely the 12 basis generators.
All relator residuals of coherent lifts then centralize E; their
literal remaining Z(E) scalars are reported without forcing them to 1.

Prerequisites: authentic manifest, mmgroup==1.0.8, original pinned ATLAS
matrices from the existing cross-source gate.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path

P=3
N=12
def dot(a,b): return sum(x*y for x,y in zip(a,b))%3
def mat_cols(cols): return [[cols[j][i] for j in range(N)] for i in range(N)]
def rref_solve(m,r):
    rows=[[v%3 for v in row]+[b%3] for row,b in zip(m,r)]
    if len(rows)!=N or any(len(row)!=N+1 for row in rows):
        raise ValueError("need 12x12 E-conjugation correction system")
    piv=[]
    for col in range(N):
        i=next((j for j in range(len(piv),N) if rows[j][col]),None)
        if i is None: continue
        k=len(piv); rows[i],rows[k]=rows[k],rows[i]
        inv=rows[k][col]
        rows[k]=[x*inv%3 for x in rows[k]]
        for j in range(N):
            if j!=k:
                coef=rows[j][col]
                rows[j]=[(x-coef*y)%3 for x,y in zip(rows[j],rows[k])]
        piv.append(col)
    if len(piv)!=N: raise ValueError("noninvertible E inner-correction system")
    return [rows[i][N] for i in range(N)]
def omega(a,b):
    return (dot(a[6:],b[:6])-dot(b[6:],a[:6]))%3
def sym_q(v):
    return 2*dot(v[:6],v[6:])%3
def correction_rows(cols):
    """Rows of u -> omega(u,v) with v=[a,b]; preserve the signed halves."""
    if len(cols)!=N or any(len(v)!=N for v in cols):
        raise ValueError("need 12 symplectic image columns")
    return [[(-x)%3 for x in v[6:]]+list(v[:6]) for v in cols]

def signed_relator_rephase():
    """Track z-twists of the fixed ATLAS word in the NONCENTRAL outer cover.

    C z C^-1=z^-1, D z D^-1=z; C'=z^a C and D'=z^b D.
    The inverse letters c,d contribute +a and -b, transported by the
    signed prefix multiplier (-1)^(# previous c).
    """
    exponents=[]
    for a in range(3):
        for b in range(3):
            prefix=1
            shift=0
            for letter in "cdcdcddcdd":
                shift=(shift+prefix*(a if letter=="c" else -b))%3
                if letter=="c":
                    prefix=-prefix
            if prefix!=1:
                raise AssertionError("ATLAS relator must preserve centre")
            if shift!=0:
                raise AssertionError("source cover relator changes under central twist")
            exponents.append([a,b,shift])
    return exponents

def relator(c,d):
    # Exact ATLAS semipresentation lower-case inverses, source gate.
    invc,invd=c**-1,d**-1
    out=c**0
    for k in "cdcdcddcdd":
        out=out*(invc if k=="c" else invd)
    return out
def selftest():
    # For any invertible matrix M, map u -> omega(u,M e_i) is invertible.
    # Check at least a genuinely mixed signed permutation M.
    cols=[[int(i==j) for i in range(N)] for j in range(N)]
    cols[0],cols[7]=cols[7],cols[0]
    rows=correction_rows(cols)
    ell=[(2*j+1)%3 for j in range(N)]
    u=rref_solve(rows,[(-x)%3 for x in ell])
    assert all((ell[i]+omega(u,cols[i]))%3==0 for i in range(N))
    assert sym_q([1]*N)==2*6%3
    assert len(signed_relator_rephase())==9
    return {"pure_F3_linear_affine_section":"PASS",
            "actual_Monster_word_identity":False}
def full(manifest,root):
    from mmgroup import MM
    from monster3b_atlas_mmgroup_cross_source_intertwiner_gate import (
        atlas,check_pair,form_monster,monster_matrix)
    if manifest.get("source_blob_sha")!="c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2":
        raise ValueError("wrong original MonsterSubgroups source SHA")
    lifts={x["name"]:x for x in manifest["normalizer_lifts"]}
    if set(lifts)!={"g3b","h3b"}: raise ValueError("not original 3B two-lift manifest")
    z=MM(manifest["center_word"])
    A=[MM(x) for x in manifest["translation_words"]]
    B=[MM(x) for x in manifest["modulation_words"]]
    if len(A)!=6 or len(B)!=6 or z.order()!=3:
        raise ValueError("noncanonical source Heisenberg generators")
    one=z**0
    def exp_comm(a,b):
        for i in range(3):
            if a*b==z**i*b*a: return i
        raise ValueError("not a source E commutator")
    for i in range(6):
        for j in range(6):
            if (exp_comm(B[i],A[j])!=int(i==j) or
                exp_comm(A[i],A[j])!=0 or exp_comm(B[i],B[j])!=0):
                raise ValueError("source symplectic E generator mismatch")
    def eword(v):
        out=one
        for a,k in zip(A,v[:6]): out=out*(a**k)
        for b,k in zip(B,v[6:]): out=out*(b**k)
        return out
    def coordinates(e):
        a=[(-exp_comm(e,B[i]))%3 for i in range(6)]
        b=[exp_comm(e,A[i]) for i in range(6)]
        v=a+b
        t=next((i for i in range(3) if e==eword(v)*z**i),None)
        if t is None: raise ValueError("normalizer image is outside actual E")
        return v,t
    def action(w):
        lam=next((i for i in (1,2) if w*z*w**-1==z**i),None)
        if lam is None: raise ValueError("group word does not normalize centre")
        coords=[coordinates(w*x*w**-1) for x in A+B]
        cols=[v for v,t in coords]
        ell=[(t-sym_q(v))%3 for v,t in coords]
        return lam,mat_cols(cols),cols,ell
    g,h=(MM(lifts[k]["word"]) for k in ("g3b","h3b"))
    # The source search identifies the chosen hit at quotient level.
    # Compute it in the FULL literal Monster group.
    c=(g*(h**-1))**15
    d=(h*(g**3))**8
    lc,mc,cc,ec=action(c)
    ld,md,cd,ed=action(d)
    if (lc,ld)!=(2,1):
        raise ValueError("Hit0 centre multipliers not the selected C/D orientation")
    att=check_pair(atlas(root),(mc,md),actual_forms=True)
    if (att["status"]!="ALGEBRAIC_CANDIDATE_ONLY" or
        not att.get("form_transport_passed") or
        att["intertwiner_dimension"]!=1):
        raise ValueError("Hit0 no longer matches original ATLAS GF3 source")
    def normalize(word,cols,ell):
        matrix=correction_rows(cols)
        u=rref_solve(matrix,[(-x)%3 for x in ell])
        if any((ell[i]+omega(u,cols[i]))%3 for i in range(N)):
            raise AssertionError("affine E correction not solved")
        correction=eword(u)
        fixed=correction*word
        l,m,c,eps=action(fixed)
        if any(eps): raise AssertionError("corrected word has nonzero affine E action")
        return fixed,u,{"central_multiplier_mod3":l,"matrix_F3":m,"affine_ell_F3":eps}
    C,u,ca=normalize(c,cc,ec)
    D,v,da=normalize(d,cd,ed)
    def zclass(w):
        return next((k for k in range(3) if w==z**k),None)
    # Central COVER relators: a nontrivial exponent is NOT a failed
    # quotient relation. The selected 6.Suz.2 complement may be nonsplit.
    rels={
      "C4":C**4,
      "D3":D**3,
      "CD56":(C*D)**56,
      "ATLAS_R7":relator(C,D)**7,
      "ATLAS_Q7":(C*D*C*D*D)**7,
      "C2_vs_CD28":C**2*((C*D)**28)**-1,
    }
    out={
      "schema":"monster3b-full-MM-Heisenberg-canonical-lifts-v1",
      "original_source_blob_sha":manifest["source_blob_sha"],
      "actual_mmgroup_used":True,"ATLAS_GF3_intertwiner":att,
      "candidate_C_word":str(c),"candidate_D_word":str(d),
      "original_affine_ell_C_F3":ec,"original_affine_ell_D_F3":ed,
      "inner_E_correction_C_F3":u,"inner_E_correction_D_F3":v,
      "canonical_C_word":str(C),"canonical_D_word":str(D),
      "canonical_C":ca,"canonical_D":da,
      "ATLAS_R_central_rephasing_invariance":True,
      "ATLAS_R_central_rephasing_signed_cases_F3":signed_relator_rephase(),
      "ATLAS_R_word_length":10,
      "ATLAS_R_c_inverse_count":4,
      "ATLAS_R_d_inverse_count":6,
      "ATLAS_R_actual_order_if_R7_equals_nontrivial_z":21 if zclass(rels["ATLAS_R7"]) in (1,2) else None,
      "central_cover_relators":{
          k:{"word":str(w),"central_z_power":zclass(w),
             "belongs_to_ZE":zclass(w) is not None}
          for k,w in rels.items()},
      "C_exact_order":C.order(),"D_exact_order":D.order(),
      "source_4D_fusion_target":"4D",
      "source_class_selected_by_GAP":True,
      "literal_candidate_C_Monster_class_4D_identified":False,
      "original_complex_12D_Hom_intertwiner_identified":False,
      "original_6Suz_standard_generator_word_equivalence_identified":False,
      "note":"Canonical E-conjugation fixes the affine gauge; central cover and source class are separate."
    }
    return out
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--manifest",type=Path,
        default=Path(".dashi/monster3b-mmgroup/monster3b-authentic-manifest.json"))
    ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[1])
    ap.add_argument("--out",type=Path,default=Path(
        ".dashi/monster3b-mmgroup/monster3b-canonical-cover-hit0.json"))
    ap.add_argument("--selftest",action="store_true")
    args=ap.parse_args()
    if args.selftest:
        print(json.dumps(selftest(),indent=2,sort_keys=True))
        return
    result=full(json.loads(args.manifest.read_text()),args.root)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"output":str(args.out),
       "source_group_word":result.get("canonical_C_word"),
       "actual_MM_group_run":result.get("actual_mmgroup_used",False)}))
if __name__=="__main__": main()
