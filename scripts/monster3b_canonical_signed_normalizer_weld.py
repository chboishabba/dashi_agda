#!/usr/bin/env python3
"""Consume exact canonical Weil vacuum coefficients and original signed MMV31 packets.

This joins, rather than rebuilds, the 729/12/78 sources. It checks a
genuine modular packet when supplied, not a numeric characteristic-zero lift.
"""
import argparse, hashlib, json
from pathlib import Path
import numpy as np
from monster3b_actual_projective_sym2_intertwiner import inverse, symmetric_square
from monster3b_quadratic12_character_lift import lift_character
from monster3b_singer_cyclic_hom import direct_signed_compare
P=31

def readj(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def block(p,key):
    with np.load(p,allow_pickle=False) as f:return np.asarray(f[key],dtype=np.int64)%P
def mul(A,B):return A@B%P
def power(A,n):
    R=np.eye(len(A),dtype=np.int64)
    while n:
        if n&1:R=mul(R,A)
        A=mul(A,A);n//=2
    return R
def norm(A,k):
    if not k:raise ValueError("zero canonical vacuum; alternate chart required")
    return A*pow(k,-1,P)%P

def relators(C,D,z):
    I=np.eye(len(C),dtype=np.int64)
    ci=power(C,3);di=power(D,2)
    R=I
    # coefficient columns implement right action, literal letters act first
    for c in "cdcdcddcdd":R=mul({"c":ci,"d":di}[c],R)
    CD=mul(D,C)
    return {"C4":np.array_equal(power(C,4),I),
            "D3":np.array_equal(power(D,3),I),
            "CD56":np.array_equal(power(CD,56),I),
            "C2_vs_CD28":np.array_equal(power(C,2),power(CD,28)),
            "ATLAS_R7":np.array_equal(power(R,7),z)}

def signed_matrix(ops,n,outer=False):
    Z=np.zeros((n,n),dtype=np.int64)
    return np.block([[Z,ops[2]],[ops[1],Z]]) if outer else np.block([[ops[1],Z],[Z,ops[2]]])

def run(a):
    model=readj(a.model);outer=readj(a.outer/"actual_MM31_outer_phase_result.json")
    if model.get("source_chart")!="literal corrected MM quotient" or model.get("status")!="CANONICAL_MODEL_SIGNED_SECTION":
        raise ValueError("actual quotient canonical model required, not ATLAS donor")
    if not all(model.get("quotient_relators_mod31",{}).values()) or len(model["quotient_relators_mod31"])!=10:
        raise ValueError("missing canonical quotient relators")
    if outer.get("status")!="ACTUAL_MM31_OUTER_VACUUM_PROJECTIVE_ACTION":
        raise ValueError("outer producer not successful")
    for key in ("canonical_C_word","canonical_D_word","original_E_source_blob_sha"):
        if not model.get(key) or model[key]!=outer.get(key):raise ValueError("literal source mismatch "+key)
    A={};H={};D={12:{},78:{}};E={12:{},78:{}};F={}
    for s,label,direction,folder in ((1,"plus","plus_to_minus",a.plus),(2,"minus","minus_to_plus",a.minus)):
        state=readj(folder/"mmv31_hom_status.json")
        for key in ("canonical_C_word","canonical_D_word","original_E_source_blob_sha"):
            if state.get(key)!=model[key]:raise ValueError("phase source mismatch "+key)
        if (state.get("p"),state.get("zeta_mod_p"),state.get("number_independent_B_fixed_vectors"))!=(31,5 if s==1 else 25,90):
            raise ValueError("wrong source phase/prime/rank")
        for fn in ("mmv31_hom_status.json","actual_C2_12_78_mod31.npz","actual_C2_on_90_mod31.npz","actual_D_12_78_vacuum_sandwich_mod31.npz","actual_CDCinv_12_78_vacuum_sandwich_mod31.npz"):
            if sha(folder/fn)!=outer["source_packet_sha256"][label+"/"+fn]:
                raise ValueError("outer/inner packet changed "+fn)
        for n,outer_ops in ((12,A),(78,H)):
            for g,target,fn in (("D",D,"actual_D_12_78_vacuum_sandwich_mod31.npz"),("E",E,"actual_CDCinv_12_78_vacuum_sandwich_mod31.npz")):
                k=model["generators"][f"{g}:{s}"]["normalized_vacuum_mod31"]
                target[n][s]=norm(block(folder/fn,g+str(n)),k)
                if not np.array_equal(power(target[n][s],3),np.eye(n,dtype=np.int64)):
                    raise ValueError("canonical inner cube fails "+g)
            # Right-action coefficient columns transpose the left model:
            # the left C kernel has source phase -s for this right map.
            k=model["generators"][f"C:{3-s}"]["normalized_vacuum_mod31"]
            outer_ops[s]=norm(block(a.outer/f"actual_MM31_C_{direction}_eig{n}.npz","matrix"),k)
    # Source-first: construct both positive-phase transports in 12 and
    # 78 seed variables, then derive the negative phase through literal C.
    # This checks against the ordinary source, not merely actual-vs-actual.
    data=readj(a.source)
    directA={g:signed_matrix(M[12] if g!="C" else A,12,g=="C")
        for g,M in (("C",D),("D",D),("E",E))}
    directH={g:signed_matrix(M[78] if g!="C" else H,78,g=="C")
        for g,M in (("C",D),("D",D),("E",E))}
    q,transport12,transport78,G,orbit_receipts=direct_signed_compare(directA,directH,data)
    loop={"beta":{1:1,2:1},"method":"source_indexed_positive_C13_seed_then_outer"}
    for s,t in ((1,2),(2,1)):
        if not np.array_equal(mul(G[t],H[s]),mul(symmetric_square(inverse(A[s]).T),G[s])):
            raise ValueError("ordinary outer covariance fails")
        for name,ops in (("D",D),("E",E)):
            if not np.array_equal(mul(G[s],ops[78][s]),mul(symmetric_square(inverse(ops[12][s]).T),G[s])):
                raise ValueError("ordinary inner symmetric square covariance fails "+name)
    results={}
    matrices={}
    zr=model["central_cover_relators"]["ATLAS_R7"]["central_z_power"]
    for n,ops in ((12,A),(78,H)):
        c=signed_matrix(ops,n,True);d=signed_matrix(D[n],n);e=signed_matrix(E[n],n)
        z=np.diag([pow(5,zr,P)]*n+[pow(25,zr,P)]*n)
        results[str(n)]=relators(c,d,z)
        results[str(n)]["E=CDCinv"]=np.array_equal(e,mul(inverse(c),mul(d,c)))
        if not all(results[str(n)].values()):raise ValueError("literal source relator obstruction "+str(results))
        matrices.update({f"C{n}":c,f"D{n}":d,f"E{n}":e})
    # Fixed embedding of the canonical Weil model makes these paired
    # trace lifts free of the earlier independent cubic gauge choices.
    # Their ordinary interpretation still requires the same integral
    # Monster lattice and the source-selected quadratic character.
    c,d,e=(matrices[g+"12"] for g in ("C","D","E"))
    R=np.eye(24,dtype=np.int64)
    for x in "cdcdcddcdd":R=mul({"c":power(c,3),"d":power(d,2)}[x],R)
    chars={}
    for name,M in (("D",d),("E",e),("C2",power(c,2)),("R",R),("DE",mul(e,d))):
        if np.any(M[:12,12:]) or np.any(M[12:,:12]):
            raise ValueError("inner word changes phase "+name)
        a1=int(np.trace(M[:12,:12]))%P;a2=int(np.trace(M[12:,12:]))%P
        lift=lift_character(a1,a2)
        if lift is None:raise ValueError("quadratic trace bound obstruction "+name)
        chars[name]={"plus":a1,"minus":a2,"conditional_ordinary_character":lift}
    np.savez_compressed(a.outdir/"canonical_signed_normalizer_mod31.npz",Fplus=G[1],Fminus=G[2],
        source_transport12=transport12,source_transport78=transport78,**matrices)
    return {"status":"SOURCE_BOUND_MOD31_SIGNED_GENERATOR_WELD","relators":results,
            "outer_loop":loop,"paired_quadratic_character_lifts":chars,"model_sha256":sha(a.model),
            "ordinary_source_sha256":sha(a.source),"ordinary_source_D_phase":q,
            "source_C13_orbits":orbit_receipts,
            "outer_receipt_sha256":sha(a.outer/"actual_MM31_outer_phase_result.json"),
            "operator_packet_sha256":sha(a.outdir/"canonical_signed_normalizer_mod31.npz"),
            "characteristic_zero_numeric_matrices":False,
            "full_presentation_authenticated":False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ("model","plus","minus","outer","outdir"):p.add_argument("--"+name,type=Path,required=True)
    p.add_argument("--source",type=Path,default=Path(__file__).resolve().parents[1]/"Docs/support/reference/Monster3BLindseyOrdinaryCD20261124.json")
    a=p.parse_args();a.outdir.mkdir(parents=True,exist_ok=True)
    try:r=run(a)
    except Exception as exc:r={"status":"BLOCKED_OR_RESIDUAL","error":repr(exc)}
    (a.outdir/"canonical_signed_normalizer_report.json").write_text(json.dumps(r,indent=2)+"\n")
    print(json.dumps(r))
    return 0 if r["status"]=="SOURCE_BOUND_MOD31_SIGNED_GENERATOR_WELD" else 2
if __name__=="__main__":raise SystemExit(main())
