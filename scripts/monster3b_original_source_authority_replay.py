#!/usr/bin/env python3
"""Original E -> literal cover -> exact signed Weil authority replay.

No active char0 checkpoint dependencies or output directories modified.
Requires the genuine native manifest/cover/model, not a synthesized fixture.
The source authority for the published normalizer structure remains explicit.
"""
import argparse, hashlib, json
from pathlib import Path
import numpy as np
from monster3b_atlas_generation_certificate import source, verify, attach, require, sha
from monster3b_exact_weil_covariance import run as exact_weil
from monster_3b_mmgroup_source_symplectic_basis import run as original_E

UPSTREAM_BLOB="c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2"
PRODUCER_BLOB="290f6643f8bd1f842cf1c4591c0e68597d6d5b61"

def git_blob(path):
    b=path.read_bytes()
    return hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()

def run(a):
    require(__debug__,"native original producer has assert checks; do not use python -O")
    producer=Path(__file__).with_name("monster_3b_mmgroup_source_symplectic_basis.py")
    require(git_blob(producer)==PRODUCER_BLOB,"original E producer changed since literal source audit")
    if a.upstream:
        require(git_blob(a.upstream)==UPSTREAM_BLOB,"wrong pinned external source bytes")
    old=json.loads(a.manifest.read_text())
    fresh,receipt=original_E()
    require(fresh==old,"original literal source manifest differs from fresh producer")
    require(receipt["observed_actual_mmgroup_execution"] is True and receipt["rank_commutator_form"]==12,"original E replay incomplete")
    from mmgroup import MM
    z=MM(old["center_word"]);chi=int(z.chi_G_x0()[0])
    require(z.order()==3 and z.in_G_x0() and chi==53,"literal 3B character marking")
    full_trace=chi+1
    m=(196884-full_trace)//3
    require(3*m==196884-full_trace and m%729==0 and m//729==90,"original phase/vacuum dimensions")
    gs=source(a.root);r=verify(gs)
    r["literal_attachment"]=attach(a.root,a.manifest,a.cover,gs)
    c=json.loads(a.cover.read_text());k=json.loads(a.model.read_text())
    require(k.get("status")=="CANONICAL_MODEL_SIGNED_SECTION" and k.get("source_chart")=="literal corrected MM quotient" and all(k[x]==c[x] for x in ("canonical_C_word","canonical_D_word","central_cover_relators")) and k.get("original_E_source_blob_sha")==UPSTREAM_BLOB,"literal model identity mismatch")
    C,D=(np.asarray(c["canonical_"+g]["matrix_F3"],dtype=np.int64) for g in ("C","D"))
    r["exact_weil_covariance"]=exact_weil(C,D,k)
    r.update(original_E_replayed=True, original_E_receipt=receipt,
             original_source_blob=UPSTREAM_BLOB,original_E_producer_blob=PRODUCER_BLOB,
             upstream_bytes_rechecked_here=a.upstream is not None,
             original_literal_source_words_previously_compared=14,
             original_full_trace=full_trace,phase_dimensions=[196884-2*m,m,m],
             vacuum_dimension_each_nontrivial_phase=m//729,
             input_sha256={str(p):sha(p) for p in (a.manifest,a.cover,a.model)},
             published_normalizer_structure_remains_source_premise=True,
             BW_character_descent_authenticated=False,actual_char0_Hom_intertwiner_executed=False,
             formal_kernel_accepted=False)
    return r

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for k in ("manifest","cover","model","out"):p.add_argument("--"+k,type=Path,required=True)
    p.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[1])
    p.add_argument("--upstream",type=Path,help="optional original subgroups.py bytes for pinned Git blob recheck")
    a=p.parse_args()
    if a.out.exists():p.error("use fresh output path; never overwrite an original receipt")
    r=run(a);a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(r,indent=2)+"\n")
    print("ORIGINAL_E_LITERAL_GENERATION_EXACT_WEIL_REPLAY_COMPLETE")
if __name__=="__main__":main()
