#!/usr/bin/env python3
"""M3B-L10A/B/C: exact SAME Monster D/E 12->dual-Sym²78 modular identity.

SOURCE producers (no new synthetic 729 or 78 representations):
  - monster3b_original729_weil_source_cocycle_weld.py (existing TOE kernel);
  - monster3b_actual_mmv31_hom_projector.py (original MMV31, actual E/B vacuum,
    original signed C² eigenblocks of dimension 12+78, actual D and CDC^-1);
  - existing CTblLib source selection (faithful 12, dual-Sym² 78).

For an honest g in the actual Monster with g³=1 and a CHOSEN 729 Weil
section K_g³=gamma I, the projective multiplicity B_g on the same actual
90D carrier must obey B_g³=gamma^-1 I on both 12 and 78 blocks. If the
selected 6.Suz type is V12 + Sym²(V12^vee), there is a *scalar-gauge
independent* trace identity:
    2 tr(B78) = tr(B12) + gamma [tr(B12²)]².

Proof: choose ANY c with c³=gamma and set A12=c B12, A78=c B78.
Then A12³=A78³=I. Because V78=Sym²(V12^vee),
2 tr A78 = (tr A12^-1)^2+tr A12^-2.
Using B12^-1=gamma B12² and B12^-2=gamma B12, divide by c
and substitute c³=gamma. The c ambiguity disappears identically.
Thus THIS TEST IS DEFINED EVEN WHEN ALL THREE CUBIC REPHASINGS SURVIVE.

The invariant checks genuine source matrices and original group words.
A pass certifies a modular projective SAME-SOURCE character consistency,
not the ordinary complex 6.Suz representation/normalizer gauge. Failure
retains the original signed residual, does not select a convenient root.
NO Steel/Magma/GAP or unrequested workstation rerun required to write it.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
from fractions import Fraction
import numpy as np
from monster3b_original729_actual_vacuum_weld import eval31,ratio_if_needed
from monster3b_quadratic12_character_lift import lift_character

P=31
def modmul(a,b):return np.asarray(a,dtype=np.int64)@np.asarray(b,dtype=np.int64)%P
def trace(a):return int(np.trace(np.asarray(a,dtype=np.int64)))%P
def scalar_matrix(a,value):
    n=a.shape[0]
    return bool(np.array_equal(a%P,(int(value)%P)*np.eye(n,dtype=np.int64)%P))
def cubic(a):
    return modmul(modmul(a,a),a)

INPUTS=(
 ("D","actual_D_12_78_vacuum_sandwich_mod31.npz","D12","D78"),
 ("E","actual_CDCinv_12_78_vacuum_sandwich_mod31.npz","E12","E78")
)
def original_phase(model,folder,phase):
    root=5 if phase==1 else 25
    state=json.loads((Path(folder)/"mmv31_hom_status.json").read_text())
    if (state.get("p"),state.get("zeta_mod_p"),
        state.get("number_independent_B_fixed_vectors"))!=(P,root,90):
        raise ValueError("actual original MMV31 centre/Heisenberg rank/prime mismatch")
    if state.get("selected_12_plus_78_dimensions_found") is not True:
        raise ValueError("original C² actual 12/78 eigenspaces not source-selected")
    if not state.get("actual_C2_mod31_matrix_generated"):
        raise ValueError("missing original Monster literal C² 12/78 owner")
    # Preserve original source identity. Legacy receipts lack literal
    # canonical word IDs; they can yield conditional projective results,
    # never silently certify SAME-word provenance.
    word_status="EXACT_SOURCE_WORD_TEXT_MATCH"
    for key in ("canonical_C_word","canonical_D_word"):
        expected=model.get(key)
        observed=state.get(key)
        if observed is None or expected is None:
            word_status="LEGACY_SOURCE_WORD_FINGERPRINT_NOT_PRESENT"
        elif expected!=observed:
            raise ValueError("original MMV receipt canonical Monster word mismatch "+key)
    rows={}
    for name,file,k12,k78 in INPUTS:
        source=Path(folder)/file
        if not source.is_file():
            rows[name]={"status":"MISSING_ORIGINAL_MM_12_78_BLOCK","source":str(source)}
            continue
        if name=="D" and not state.get("D_vacuum_sandwich_commutes_with_C2"):
            raise ValueError("original D does not preserve actual C² eigenspaces")
        if name=="E" and not state.get("CDCinv_vacuum_sandwich_commutes_with_C2"):
            raise ValueError("original E does not preserve actual C² eigenspaces")
        with np.load(source,allow_pickle=False) as files:
            A=np.asarray(files[k12],dtype=np.int64)%P
            B=np.asarray(files[k78],dtype=np.int64)%P
        if A.shape!=(12,12) or B.shape!=(78,78):
            raise ValueError("wrong SAME-MONSTER source eigenspace dimensions")
        vac=ratio_if_needed(model,phase,name)
        if vac is None or vac==0:
            rows[name]={"status":"ZERO_WEIL_VACUUM_COEFFICIENT",
                "ordinary_character_claimed":False}
            continue
        L12=A*pow(vac,-1,P)%P
        L78=B*pow(vac,-1,P)%P
        g=model["phases"][str(phase)]["order3_model_cubic_scalars"][name]
        gamma=eval31(g["K_g_cube_scalar_Qzeta3"],root)
        if gamma==0:raise AssertionError("noninvertible projective Weil gamma")
        inverse_gamma=pow(gamma,-1,P)
        cubic12=scalar_matrix(cubic(L12),inverse_gamma)
        cubic78=scalar_matrix(cubic(L78),inverse_gamma)
        t12,t12sq,t78=trace(L12),trace(modmul(L12,L12)),trace(L78)
        predicted=(t12+gamma*t12sq*t12sq)*pow(2,-1,P)%P
        consistent=t78==predicted
        rows[name]={
          "status":("PROJECTIVE_DUAL_SYM2_CHARACTER_WELD_CONSISTENT"
                 if cubic12 and cubic78 and consistent
                 else "SAME_SOURCE_CUBIC_OR_DUAL_SYM2_OBSTRUCTION"),
          "word":("D" if name=="D" else "C D C^-1"),
          "source_phase":phase,"original_Monster_projected_blocks":True,
          "source_word_provenance":word_status,
          "chosen_729_model_k0_mod31":vac,
          "chosen_729_model_K_g_cubed_gamma_mod31":gamma,
          "forced_90D_inverse_cube_mod31":inverse_gamma,
          "L12_cube_matches_inverse_gamma":cubic12,
          "L78_cube_matches_inverse_gamma":cubic78,
          "trace_projective_12_mod31":t12,
          "trace_projective_12_squared_matrix_mod31":t12sq,
          "trace_projective_78_mod31":t78,
          "dual_sym2_predicted_78_mod31":predicted,
          "projective_dual_sym2_character_consistent":consistent,
          "three_cubic_rephasings_NOT_independently_resolved":True,
          "ordinary_complex_character_attached":False}
    return {"original_Monster_phase":phase,"root_zeta3_mod31":root,
        "provenance":word_status,"source_manifest":state.get("source_manifest"),
        "words":rows}

def run(model,plus=None,minus=None):
    if model.get("schema")!="monster3b-reused-toe-original729-weil-cochain-v1":
        raise ValueError("wrong source original 729 Weil model")
    if not all("order3_model_cubic_scalars" in model.get("phases",{}).get(str(s),{})
               for s in (1,2)):
        raise ValueError("model lacks actual original D/E 729 cubic scalar producers")
    result={"schema":"monster3b-actual-MMV31-order3-projective-12-to-dualsym2-78-v1",
       "source":"actual MMV31 E/B source + reused exact 729 Weil compiler",
       "ordinary_6Suz_character_claimed":False,
       "global_Monster_Suz_normalizer_gauge_claimed":False,
       "phases":{},"same_word_quadratic_ordinary12_candidates":{}}
    for s,folder in ((1,plus),(2,minus)):
        if folder is not None:
            result["phases"][str(s)]=original_phase(model,folder,s)
    if plus is not None and minus is not None:
        if result["phases"]["1"]["source_manifest"]!=result["phases"]["2"]["source_manifest"]:
            raise ValueError("opposite phases do not originate from same Monster E manifest")
        for name in ("D","E"):
            p=result["phases"]["1"]["words"].get(name,{})
            q=result["phases"]["2"]["words"].get(name,{})
            if (p.get("status")=="PROJECTIVE_DUAL_SYM2_CHARACTER_WELD_CONSISTENT"
                and q.get("status")=="PROJECTIVE_DUAL_SYM2_CHARACTER_WELD_CONSISTENT"
                and p["chosen_729_model_K_g_cubed_gamma_mod31"]==1
                and q["chosen_729_model_K_g_cubed_gamma_mod31"]==1):
                ch=lift_character(p["trace_projective_12_mod31"],
                                  q["trace_projective_12_mod31"])
                result["same_word_quadratic_ordinary12_candidates"][name]={
                   "candidate":ch,"status":("BOUNDED_CHARACTER_CANDIDATE_NOT_GROUP_GAUGE"
                             if ch is not None else "NO_BOUNDED_ORDINARY12_VALUE"),
                   "original_genuine_Monster_group_word":name,
                   "phase_galois_intertwiner_identified":False}
    statuses=[row["status"] for phase in result["phases"].values()
              for row in phase["words"].values()]
    if any(x=="SAME_SOURCE_CUBIC_OR_DUAL_SYM2_OBSTRUCTION" for x in statuses):
        result["status"]="FAIL_CLOSED_ORIGINAL_SOURCE_SYM2_OR_CUBIC_MISMATCH"
    elif statuses and all(x=="PROJECTIVE_DUAL_SYM2_CHARACTER_WELD_CONSISTENT"
                          for x in statuses):
        result["status"]="CONSISTENT_PROJECTIVE_SOURCE_CHARACTERS_NOT_ORDINARY"
    else:result["status"]="PARTIAL_ORIGINAL_SOURCE_PROJECTIVE_COMPARISON"
    return result

def selftest():
    # Exact 12+78 eigenvalue model, NOT a substitute for real Monster data.
    z=5; zi=25
    vals=[1]*5+[z]*4+[zi]*3
    full=[pow(vals[i]*vals[j]%P,-1,P)
          for i in range(12) for j in range(i,12)]
    assert len(full)==78
    out=[]
    for unit in (1,z,zi):
        A=np.diag([v*pow(unit,-1,P)%P for v in vals])
        B=np.diag([v*pow(unit,-1,P)%P for v in full])
        gamma=pow(unit,3,P)
        t12=trace(A);t12sq=trace(modmul(A,A));t78=trace(B)
        expected=(t12+gamma*t12sq*t12sq)*pow(2,-1,P)%P
        if not (t78==expected and scalar_matrix(cubic(A),pow(gamma,-1,P))
                and scalar_matrix(cubic(B),pow(gamma,-1,P))):
            raise AssertionError("gauge-independent dual-Sym² trace identity failed")
        out.append({"cube_root_gauge":unit,"trace_78":t78,"prediction":expected})
    return {"status":"PASS_EXACT_GAUGE_INVARIANT_12_TO_78_TOY",
       "three_unresolved_rephasings_preserved":True,
       "checks":out,"actual_Monster_receipts_executed_here":False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--model",type=Path)
    p.add_argument("--plus",type=Path)
    p.add_argument("--minus",type=Path)
    p.add_argument("--out",type=Path,default=Path(
      ".dashi/monster3b-mmgroup/actual_projective_12_to_78.json"))
    p.add_argument("--selftest",action="store_true")
    a=p.parse_args()
    if a.selftest:result=selftest()
    else:
        if a.model is None or (a.plus is None and a.minus is None):
            p.error("--model and at least --plus or --minus required")
        result=run(json.loads(a.model.read_text()),a.plus,a.minus)
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"output":str(a.out),"status":result["status"],
       "actual_char0_Hom_identified":False}))
    return 2 if result["status"].startswith("FAIL_CLOSED") else 0
if __name__=="__main__":raise SystemExit(main())
