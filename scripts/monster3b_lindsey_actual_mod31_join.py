#!/usr/bin/env python3
"""Original Lindsey ordinary source -> actual canonical MMV31 signed blocks.
Use original source compact matrices and the existing signed Monster packet.
The 12D simultaneous Hom plus outer transport induces the 78D transport;
no independent 6084-variable solve. Modular source weld, not char0 MMV.
"""
import argparse, hashlib, json
from pathlib import Path
import numpy as np
from monster3b_actual_projective_sym2_intertwiner import (
    inverse as inv, symmetric_square as sym, singleton_nullspace,
)
P=31
def eye(n):return np.eye(n,dtype=np.int64)
def mm(A,B):return A@B%P
def power(A,k):
    R=eye(len(A))
    while k:
        if k&1:R=mm(R,A)
        A=mm(A,A);k//=2
    return R
def bd(A,B):return np.block([[A,np.zeros_like(B)],[np.zeros_like(A),B]])
def outer(A,B):return np.block([[np.zeros_like(A),B],[A,np.zeros_like(B)]])
def dual(M,outer_action=False):
    if outer_action:return outer(sym(inv(M[12:,:12]).T),sym(inv(M[:12,12:]).T))
    return bd(sym(inv(M[:12,:12]).T),sym(inv(M[12:,12:]).T))
def hom12(S,T):
    R=np.vstack([np.kron(eye(12),S[g].T)-np.kron(T[g],eye(12)) for g in ("D","E")])%P
    v=singleton_nullspace(R)
    if v is None:raise ValueError("source inner Hom nullity != 1")
    F=v.reshape(12,12);inv(F)
    if not all(np.array_equal(mm(F,S[g]),mm(T[g],F)) for g in S):
        raise ValueError("inner Hom equation")
    return F
def source_matrices(data,q):
    if data.get("schema")!="monster3b-lindsey-ordinary-CD-compact-v1":
        raise ValueError("original Lindsey source matrix schema")
    def ev(g,z):
        raw=data[g];A=np.asarray(raw["numerator_rows"],dtype=np.int64)
        if A.shape!=(12,24):raise ValueError("ordinary source dimensions")
        return (A[:,::2]+z*A[:,1::2])*pow(raw["denominator"],-1,P)%P
    # Full left-action matrices transpose to coefficient columns for
    # the actual right MMV action. This also reverses outer block indices.
    C=outer(ev("C",25),ev("C",5)).T
    D=bd(ev("D",5)*pow(5,q,P)%P,ev("D",25)*pow(25,q,P)%P).T
    return {"C":C,"D":D,"E":mm(inv(C),mm(D,C))}
def compare(A,H,G,data):
    z=np.diag([5]*12+[25]*12)
    C,D=A["C"],A["D"]
    Q=power(mm(D,mm(D,mm(C,mm(D,C)))),7)
    q=next((k for k in range(3) if np.array_equal(Q,power(z,k))),None)
    if q is None:raise ValueError("actual canonical Q7 noncentral")
    T=source_matrices(data,q)
    Fp=hom12({g:A[g][:12,:12] for g in ("D","E")},
             {g:T[g][:12,:12] for g in ("D","E")})
    Fm=mm(mm(T["C"][12:,:12],Fp),inv(C[12:,:12]))
    F=bd(Fp,Fm);inv(F)
    if not all(np.array_equal(mm(F,A[g]),mm(T[g],F)) for g in A):
        raise ValueError("full signed 12 source weld")
    U={g:dual(T[g],g=="C") for g in T}
    Gp,Gm=G
    J=bd(mm(sym(inv(Fp).T),Gp),mm(sym(inv(Fm).T),Gm));inv(J)
    if not all(np.array_equal(mm(J,H[g]),mm(U[g],J)) for g in H):
        raise ValueError("full signed 78 source weld")
    return q,F,J
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def readj(p):return json.loads(p.read_text())
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source",type=Path,default=Path(__file__).resolve().parents[1]/"Docs/support/reference/Monster3BLindseyOrdinaryCD20261124.json")
    for name in ("cover","model","packet-dir","outdir"):p.add_argument("--"+name,type=Path,required=True)
    a=p.parse_args();a.outdir.mkdir(parents=True,exist_ok=True)
    result={"actual_characteristic_zero_Hom_matrices":False}
    try:
        data,cover,model=map(readj,(a.source,a.cover,a.model))
        report=readj(a.packet_dir/"canonical_signed_normalizer_report.json")
        packet=a.packet_dir/"canonical_signed_normalizer_mod31.npz"
        if (report.get("status")!="SOURCE_BOUND_MOD31_SIGNED_GENERATOR_WELD"
            or report.get("model_sha256")!=sha(a.model)
            or report.get("operator_packet_sha256")!=sha(packet)):
            raise ValueError("canonical signed packet missing verified receipt/hash")
        if not cover.get("actual_mmgroup_used") or cover["central_cover_relators"]["ATLAS_R7"]["central_z_power"]!=1:
            raise ValueError("actual corrected source R7 required")
        if not cover.get("ATLAS_GF3_intertwiner",{}).get("form_transport_passed"):
            raise ValueError("original quotient chart unverified")
        for key in ("canonical_C_word","canonical_D_word","original_source_blob_sha"):
            if not cover.get(key) or cover[key]!=model.get(key):
                raise ValueError("literal cover/model mismatch "+key)
        with np.load(packet,allow_pickle=False) as f:
            A={g:np.asarray(f[g+"12"],dtype=np.int64)%P for g in ("C","D","E")}
            H={g:np.asarray(f[g+"78"],dtype=np.int64)%P for g in ("C","D","E")}
            G=tuple(np.asarray(f[k],dtype=np.int64)%P for k in ("Fplus","Fminus"))
        if not all(x.shape==(24,24) for x in A.values()) or not all(x.shape==(156,156) for x in H.values()):
            raise ValueError("original source signed dimensions")
        q,F,J=compare(A,H,G,data)
        explicit=cover["central_cover_relators"].get("ATLAS_Q7",{}).get("central_z_power")
        if explicit is not None and q!=explicit:raise ValueError("literal Q7 contradicts normalized source packet")
        np.savez_compressed(a.outdir/"lindsey_to_actual_MM31_signed_intertwiners.npz",transport12=F,transport78=J)
        result.update(status="ORIGINAL_ORDINARY_SOURCE_TO_ACTUAL_MM31_SIGNED_OPERATOR_WELD",
            D_relative_to_standard_phase=q,source_sha256=sha(a.source),
            cover_sha256=sha(a.cover),model_sha256=sha(a.model),packet_sha256=sha(packet),
            transport_sha256=sha(a.outdir/"lindsey_to_actual_MM31_signed_intertwiners.npz"),
            signed_12_generator_equations=3,signed_78_generator_equations=3)
    except Exception as exc:result.update(status="BLOCKED_OR_SOURCE_RESIDUAL",error=repr(exc))
    (a.outdir/"lindsey_actual_MM31_report.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result))
    return 0 if result["status"].startswith("ORIGINAL_ORDINARY_SOURCE") else 2
if __name__=="__main__":raise SystemExit(main())
