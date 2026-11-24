#!/usr/bin/env python3
"""Reconcile the ORIGINAL 729 Weil kernel with actual MMV31 vacuum receipts.

Imports the committed original exact 729 model cocycle receipt produced by
monster3b_original729_weil_source_cocycle_weld.py. For each nonzero model
vacuum coefficient k0 in the same phase/generator convention, compare
the MMV31 raw right-action multiplication cocycle against the one forced
by the chosen 729 scalar gauge:

     beta_MM(DE) = (k0_D * k0_E) / (alpha_729(D,E) * k0_DE).

The MMV31 columns represent a RIGHT action; the chosen transposed
Schr representation has H_E H_D = alpha_729(D,E) H_DE, so this is the
correct ordering. If actual source convention differs, FAIL rather than
invent a phase/gauge.  Requires an actual 90D module and the exact
matching mmgroup E-coordinates/polarization.

Also divides raw D/E 12D and 78D sandwiches by their model Weil
vacuum coefficient, generating exact F31 matrices in that *projective
model gauge*. This is not automatically an honest 6.Suz linear
representation or characteristic-zero Monster-Hom equivalence.

A ZERO model k0 is a genuine obstruction to vacuum normalization in
this chosen polarization. Keep the original residual and use another
point projector or model chart; never invert zero.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import numpy as np

P=31
def qpair(v):
    if not isinstance(v,list) or len(v)!=2:raise ValueError("expected Q(zeta3) pair")
    return F(v[0]),F(v[1])
def fp(a):
    num,den=int(a.numerator),int(a.denominator)
    if den%P==0:raise ValueError("Weil model scalar denominator divisible by 31")
    return num*pow(den,-1,P)%P
def eval31(value,zeta):
    a,b=qpair(value)
    return (fp(a)+zeta*fp(b))%P
def ratio_if_needed(model,phase,name):
    rec=model["phases"][str(phase)]["vacuum"][name]
    if not rec.get("k0_nonzero"):return None
    return eval31(rec["k0_unitary_model_Qzeta3"],5) # phase already encoded by compile_shape
def predicted(model,phase,word):
    data=model["phases"][str(phase)]
    left,right,prod=(
        ("D","E","DE") if word=="DE" else
        ("E","D","ED"))
    coeff=[ratio_if_needed(model,phase,x) for x in (left,right,prod)]
    if None in coeff or any(x==0 for x in coeff):
        return {"status":"ZERO_VACUUM_COEFFICIENT","k0":[str(x) for x in coeff]}
    alpha=eval31(data["pairs"]["D_E" if word=="DE" else "E_D"][
         "unitary_gauge_multiplier_Qzeta3"],5)
    if alpha==0:raise AssertionError("unitary model cannot have zero cocycle")
    kleft,kright,kprod=coeff
    beta=kleft*kright*pow(alpha*kprod%P,-1,P)%P
    return {"status":"NONZERO_MODEL_COEFFICIENT",
            "predicted_projected_right_action_beta_mod31":beta,
            "source_729_multiplier_mod31":alpha,
            "source_model_vacuum_coefficients_mod31":{
                left:kleft,right:kright,prod:kprod},
            "chosen_model_gauge":"Delta^-r, transpose/right, as in original 729 compiler"}

def normalize_blocks(model,phase,folder,outdir):
    outputs={}
    zeta=5 if phase==1 else 25
    for word,npzname,block in [
        ("D","actual_D_12_78_vacuum_sandwich_mod31.npz","D"),
        ("E","actual_CDCinv_12_78_vacuum_sandwich_mod31.npz","E")]:
        k=ratio_if_needed(model,phase,word)
        source=Path(folder)/npzname
        if k is None or k==0:
            outputs[word]={"status":"VACUUM_ZERO_MODEL_NO_NORMALIZATION"}
            continue
        if not source.is_file():
            outputs[word]={"status":"ACTUAL_MM_SANDWICH_SOURCE_MISSING"}
            continue
        with np.load(source) as r:
            mat12=np.asarray(r[block+"12"],dtype=np.int64)%P
            mat78=np.asarray(r[block+"78"],dtype=np.int64)%P
        if mat12.shape!=(12,12) or mat78.shape!=(78,78):
            raise ValueError("actual modular 12/78 source block has wrong dimensions")
        inverse=pow(k,-1,P)
        norm12=(mat12*inverse)%P
        norm78=(mat78*inverse)%P
        np.savez_compressed(
            outdir/f"source_normalized_{word}_12_78_zeta{zeta}.npz",
            L12=norm12,L78=norm78,
            actual_raw_12=mat12,actual_raw_78=mat78,
            k0_model_mod31=k)
        outputs[word]={"status":"ACTUAL_MM_MOD31_BLOCK_DIVIDED_BY_CHOSEN_729_K0",
            "normalization_is_honest_6Suz_linear_representation":False,
            "model_k0_mod31":k,
            "normalized_trace12_mod31":int(np.trace(norm12))%P,
            "normalized_trace78_mod31":int(np.trace(norm78))%P,
            "source_12_78_matrix_file":str(outdir/
              f"source_normalized_{word}_12_78_zeta{zeta}.npz")}
    return outputs

def run(model,phase,folder,outdir):
    if model.get("schema")!="monster3b-reused-toe-original729-weil-cochain-v1":
        raise ValueError("wrong original 729 kernel source receipt")
    state=json.loads((Path(folder)/"mmv31_hom_status.json").read_text())
    if (state.get("p"),state.get("zeta_mod_p"),
        state.get("number_independent_B_fixed_vectors"))!=(
            31,5 if phase==1 else 25,90):
        raise ValueError("wrong original actual Monster vacuum phase / rank")
    out={"schema":"monster3b-original729-to-actual-MMV31-vacuum-weld-v1",
         "status":"SOURCE_PROJECTIVE_729_GAUGE_COMPARISON",
         "actual_Monster_MM_mod31":True,"source_phase":phase,
         "source_weil_compiler":"toe_cyclotomic_operator.py",
         "model_to_actual_729_orientation_not_inferred_from_quotient":True,
         "ordinary_6Suz_honest_representation_identified":False,
         "source_projective_pair":{}}
    for word,key in [("DE","original_MM31_vacuum_pair_DE_cocycle"),
                     ("ED","original_MM31_vacuum_pair_ED_cocycle")]:
        eq=predicted(model,phase,word)
        obs=state.get(key)
        if obs and obs.get("is_scalar") is True and obs.get("scalar") is not None:
            eq["actual_MM31_reported_beta"]=int(obs["scalar"])
            if eq["status"]=="NONZERO_MODEL_COEFFICIENT":
                eq["actual_source_matches_model_W_polarization_and_scalar"]=(
                    eq["predicted_projected_right_action_beta_mod31"]
                    ==int(obs["scalar"]))
                eq["status"]=("PROJECTIVE_SOURCE_MODEL_COCYCLE_MATCHED"
                    if eq["actual_source_matches_model_W_polarization_and_scalar"]
                    else "SOURCE_W_MODEL_POLARIZATION_OR_GAUGE_MISMATCH")
        else:
            eq["actual_source_cocycle_missing_or_nonscalar"]=True
        out["source_projective_pair"][word]=eq
    out["normalized_projective_source_blocks"]=normalize_blocks(
        model,phase,folder,outdir)
    return out

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--model",type=Path,required=True)
    ap.add_argument("--phase1",type=Path)
    ap.add_argument("--phase2",type=Path)
    ap.add_argument("--outdir",type=Path,required=True)
    a=ap.parse_args()
    if a.phase1 is None and a.phase2 is None:
        ap.error("at least one genuine original MMV31 phase input required")
    a.outdir.mkdir(parents=True,exist_ok=True)
    model=json.loads(a.model.read_text())
    result={"schema":"monster3b-729-actual-vacuum-two-phase-source-match-v1",
            "source_729_model_receipt":str(a.model),"phases":{},
            "actual_monster_char0_representation_declared":False}
    for phase,path in ((1,a.phase1),(2,a.phase2)):
        if path is not None:
            result["phases"][str(phase)]=run(
                model,phase,path,a.outdir)
    output=a.outdir/"original729_to_actual_MMV31_weld.json"
    output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"output":str(output),
       "source_phase_comparisons":list(result["phases"]),
       "genuine_ordinary_Hom_instantiated":False}))
if __name__=="__main__":main()
