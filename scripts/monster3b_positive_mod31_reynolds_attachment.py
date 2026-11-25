#!/usr/bin/env python3
"""Same-object positive MMV31 generator replay -> local-lattice char0 witness.

No dependence on the in-progress characteristic-zero checkpoint directory.
Read the original DIRECT positive probe packet, replay its actual vectors and
literal D/E/J operators, derive the negative chart by the honest signed action.
A successful result supplies the good-prime premise of the Reynolds lift;
it does not independently prove the source cover or the native action contract.
"""
import argparse, hashlib, json
from fractions import Fraction
from pathlib import Path
import numpy as np
from monster3b_actual_mmv31_hom_projector import row_span_coefficients, nullspace31, coordinates_in_columns
from monster3b_actual_projective_sym2_intertwiner import inverse
from monster3b_lindsey_actual_mod31_join import bd, outer, source_matrices, dual
from monster3b_singer_cyclic_hom import direct_signed_compare

P=31
DIM=196884
SOURCE="c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2"
ORDINARY_BLOB="b0f96b37494cfca56f116b991d350352d3a493f2"
H_ORDER=5380145971200

def require(ok,msg):
    if not ok:raise ValueError(msg)
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def mm(A,B):return np.asarray(A,dtype=np.int64)@np.asarray(B,dtype=np.int64)%P
def eye(n):return np.eye(n,dtype=np.int64)
def scalar_mod(pair):
    a,b=map(Fraction,pair)
    def red(x):return x.numerator*pow(x.denominator,-1,P)%P
    return (red(a)+5*red(b))%P

def load_positive(folder,manifest,m):
    statefile=folder/"mmv31_hom_status.json";st=read(statefile)
    require((st.get("p"),st.get("zeta_mod_p"),st.get("number_independent_B_fixed_vectors"))==(31,5,90),"wrong original marked positive rank")
    require(st.get("status")=="COMPLETE_RANK90" and not st.get("derived_from_plus"),"direct complete original positive receipt required")
    require(st.get("actual_Monster_modular_vectors") is True or st.get("actual_Monster_mod31_vectors") is True,"original actual vector status absent")
    # The v1 receipt does not assert literal C/D fields. Its positive vacuum
    # depends only on the E-manifest; never manufacture historical C/D metadata.
    # Replay every D/E/J on the newly supplied literal cover below instead.
    if st.get("original_E_source_blob_sha") is not None:
        require(st["original_E_source_blob_sha"]==m["source_blob_sha"],"original E source mismatch")
    old=Path(st["source_manifest"])
    require(old.is_file() and sha(old)==sha(manifest),"original positive manifest bytes must match")
    path=folder/"ambient_basis_rows_mod31.npz"
    if not path.is_file():path=folder/"ambient_basis_rows.npz"
    with np.load(path,allow_pickle=False) as f:
        raw=np.asarray(f["rows"]);piv=[int(x) for x in f["pivots"]];probes=[int(x) for x in f["source_probes"]]
    require(raw.shape==(90,DIM) and raw.dtype.kind in ("i","u") and not np.any(raw<0) and not np.any(raw>=P),"original canonical residue shape")
    rows=raw.astype(np.int16)
    require(len(piv)==len(probes)==len(set(piv))==len(set(probes))==90 and all(0<=i<DIM for i in piv+probes),"original bounded independent indices")
    require(piv==st["pivots"] and probes==st.get("source_E_basis_probe_indices"),"original probe ledger mismatch")
    require(all(rows[i,p]==1 and not np.any(rows[i,piv[:i]]) for i,p in enumerate(piv)),"original echelon rows malformed")
    return st,rows,piv,probes,path

def run(a):
    from mmgroup import MM,MMV
    from monster3b_mm31_outer_phase_pair import reconstruct
    from monster3b_literal_standard_D_phase import run as literal_phase
    from importlib.metadata import version
    m,c,k,data=map(read,(a.manifest,a.cover,a.model,a.source))
    original=a.source.read_bytes()
    require(hashlib.sha1(b"blob "+str(len(original)).encode()+b"\0"+original).hexdigest()==ORDINARY_BLOB,"ordinary source bytes mismatch")
    require(m.get("source_blob_sha")==c.get("original_source_blob_sha")==k.get("original_E_source_blob_sha")==SOURCE,"original E source mismatch")
    require(k.get("status")=="CANONICAL_MODEL_SIGNED_SECTION" and k.get("source_chart")=="literal corrected MM quotient" and k.get("fixed_zeta_embedding")==5,"original canonical Weil section required")
    require(all(c.get(t) and c[t]==k.get(t) for t in ("canonical_C_word","canonical_D_word")) and k.get("central_cover_relators")==c.get("central_cover_relators"),"canonical model literal cover mismatch")
    require(len(k.get("quotient_relators_mod31",{}))==10 and all(k["quotient_relators_mod31"].values()),"canonical quotient relator receipt")
    phase=literal_phase(a.manifest,a.cover)
    require(phase.get("raw_wheel_has_order13") is True,"raw Singer word mismatch")
    st,rows,piv,probes,ambient=load_positive(a.plus,a.manifest,m)
    for t in ("canonical_C_word","canonical_D_word"):
        if st.get(t) is not None:require(st[t]==c[t],"recorded literal source mismatch")
    z=MM(m["center_word"]);C=MM(c["canonical_C_word"]);D=MM(c["canonical_D_word"])
    T=[MM(x) for x in m["translation_words"]];B=[MM(x) for x in m["modulation_words"]]
    require(len(T)==len(B)==6 and z.order()==3 and C*z*C**-1==z**-1 and D*z==z*D,"original signed E chart")
    require(all(g.order()==3 and g*z==z*g for g in T+B) and all(g*h==h*g for axes in (T,B) for g in axes for h in axes),"original commuting order-three axes")
    A=np.asarray([[next((i for i in range(3) if t*b*t**-1*b**-1==z**i),-1) for b in B] for t in T],dtype=np.int64)
    require(np.all(A>=0),"original E commutator not central")
    pairing=A.copy().tolist()
    for i in range(6):
        j=next((j for j in range(i,6) if A[j,i]),None)
        require(j is not None,"degenerate original E pairing")
        A[[i,j]]=A[[j,i]];A[i]=A[i]*A[i,i]%3
        for j in range(i+1,6):A[j]=(A[j]-A[j,i]*A[i])%3
    V=MMV(P);basis,project=reconstruct(rows,piv,probes,5,V,z,B)
    Jword=C**2
    require(all(Jword*b*Jword**-1==b**-1 for b in B),"literal C2 does not stabilize vacuum")
    pos={}
    for g,word in (("D",D),("E",C*D*C**-1),("J",Jword)):
        if g=="J":kappa=1
        else:
            rec=k["generators"][g+":1"]
            require(rec.get("zero_affine_vacuum_unit_verified") is True,"canonical vacuum unit missing")
            kappa=scalar_mod(rec["normalized_vacuum_Qzeta3"])
            require(kappa and kappa==rec["normalized_vacuum_mod31"],"exact/modular vacuum scalar mismatch")
        cols=[]
        for v in basis:
            w=v*word if g=="J" else project(v*word)
            r,x=row_span_coefficients(w["E"],rows,piv)
            require(not np.any(r),"actual positive ambient generator closure")
            cols.append(np.asarray(x,dtype=np.int64)*pow(kappa,-1,P)%P)
        pos[g]=np.column_stack(cols)
    J=pos["J"];I=eye(90)
    require(np.array_equal(mm(J,J),I) and all(np.array_equal(mm(J,pos[g]),mm(pos[g],J)) for g in ("D","E")),"actual positive parity laws")
    blocks={}; eig={}
    for n,sgn in ((12,-1),(78,1)):
        Q=nullspace31((J-sgn*I)%P)
        require(Q.shape==(90,n),"actual signed constituent dimension")
        eig[n]=Q.astype(np.int64)
        M=coordinates_in_columns(Q,mm(pos["D"],Q)).astype(np.int64)
        N=coordinates_in_columns(Q,mm(pos["E"],Q)).astype(np.int64)
        # Negative basis defined by L(C) of the positive basis. Its signed
        # action follows from the exact honest-cover theorem, not new samples.
        blocks[n]={"C":outer(eye(n),sgn*eye(n)%P),"D":bd(M,N),"E":bd(N,M)}
    q,F12,F78,G,orbit=direct_signed_compare(blocks[12],blocks[78],data)
    require(q==phase["Q7_central_z_power"],"literal/source D phase mismatch")
    A12=source_matrices(data,q);A78={g:dual(A12[g],g=="C") for g in A12}
    for n,F,src in ((12,F12,A12),(78,F78,A78)):
        Fi=inverse(F)
        for g in ("C","D","E"):
            require(np.array_equal(mm(F,blocks[n][g]),mm(src[g],F)) and np.array_equal(mm(Fi,src[g]),mm(blocks[n][g],Fi)),"signed source map inverse")
    # Preserve the actual positive 90D chart, not just the 12/78 block
    # matrices. X maps ordinary positive coordinates into the original
    # echelon vacuum basis. Its first columns give literal seed recipes.
    X={n:mm(eig[n],inverse(F[:n,:n])) for n,F in ((12,F12),(78,F78))}
    X90=np.column_stack((X[12],X[78]));Y90=inverse(X90)
    require(np.array_equal(mm(X90,Y90),I) and np.array_equal(mm(Y90,X90),I),"full positive vacuum coordinate inverse")
    for n,src,sgn in ((12,A12,-1),(78,A78,1)):
        for g in ("D","E"):
            require(np.array_equal(mm(pos[g],X[n]),mm(X[n],src[g][:n,:n])),"ambient positive seed transport")
        require(np.array_equal(mm(J,X[n]),sgn*X[n]%P),"ambient positive seed sign")
    generation=None
    if a.generation:
        r=read(a.generation);g=r.get("literal_attachment",{})
        require(r.get("order_lower_bound")==H_ORDER//3 and g.get("status")=="LITERAL_COVER_GENERATION_ATTACHED" and g.get("manifest_sha256")==sha(a.manifest) and g.get("cover_sha256")==sha(a.cover),"literal generation receipt mismatch")
        generation={"path":str(a.generation),"sha256":sha(a.generation),"status":g["status"]}
    require(H_ORDER%31!=0,"not a good prime")
    a.outdir.mkdir(parents=True,exist_ok=True)
    packet=a.outdir/"positive_reynolds_mod31.npz"
    np.savez_compressed(packet,actual_to_source12=F12,actual_to_source78=F78,
                        source_to_actual12=inverse(F12),source_to_actual78=inverse(F78),
                        positive_eig12=eig[12],positive_eig78=eig[78],
                        positive_ordinary_to_vacuum=X90,positive_vacuum_to_ordinary=Y90,
                        positive_seed12=X[12][:,0],positive_seed78=X[78][:,0],
                        positive_D=pos["D"],positive_E=pos["E"],positive_J=J,
                        **{g+str(n):M for n,ops in blocks.items() for g,M in ops.items()})
    return {"status":"ACTUAL_POSITIVE_MOD31_SIGNED_REYNOLDS_PREMISE",
            "mmgroup_version":version("mmgroup"),"source_phase":q,"pairing_F3":pairing,
            "source_hashes":{str(p):sha(p) for p in (a.manifest,a.cover,a.model,a.source,ambient,a.plus/"mmv31_hom_status.json")},
            "direct_positive_columns":270,"signed_negative_derived_not_measured":True,
            "orbit_receipts":orbit,"packet_sha256":sha(packet),"cover_order":H_ORDER,"prime":31,
            "literal_generation_receipt":generation,
            "positive_echelon_seed_coordinates":{str(n):X[n][:,0].tolist() for n in (12,78)},
            "seed_expression":"y_n = Q_L P_n P_B P_+ sum_i lift(seed_n[i]) lift(original_echelon_row_i); Q_L is the exact single-residual projector from the source recipe, never a lift of its modular coefficients",
            "coordinate_expression":"F_+=[L(w_i)y_n] B^-1; F_-=L(C) F_+ A(C)^-1; inverse by source dual orbit recovery",
            "char0_existence_conditional_on_original_honest_action_and_integral_lattices":True,
            "actual_char0_numeric_matrices":False,"full_cover_authentication_and_kernel_acceptance_separate":True}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for n in ("manifest","cover","model","plus","outdir"):p.add_argument("--"+n,type=Path,required=True)
    p.add_argument("--source",type=Path,default=Path(__file__).resolve().parents[1]/"Docs/support/reference/Monster3BLindseyOrdinaryCD20261124.json")
    p.add_argument("--generation",type=Path,help="optional independently replayed literal generation receipt")
    a=p.parse_args();a.outdir.mkdir(parents=True,exist_ok=True)
    try:r=run(a)
    except Exception as e:r={"status":"BLOCKED_OR_SOURCE_RESIDUAL","error":repr(e)}
    (a.outdir/"positive_reynolds_result.json").write_text(json.dumps(r,indent=2)+"\n")
    print(r["status"])
    return 0 if r["status"]=="ACTUAL_POSITIVE_MOD31_SIGNED_REYNOLDS_PREMISE" else 2
if __name__=="__main__":raise SystemExit(main())
