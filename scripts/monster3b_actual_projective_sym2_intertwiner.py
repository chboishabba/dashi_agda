#!/usr/bin/env python3
"""M3B-L10B/C: construct a genuine F31 78D equivariant intertwinER.

Input: actual Monster MMV31 12- and 78-dimensional C²-source
eigenblocks for the SAME D and E=CDC^-1 words, and the chosen exact
729D Weil cubic scalars, not manufactured 90D test characters.

For each actual order-three g, write B12_g=M12_g/kappa_g,
B78_g=M78_g/kappa_g, gamma_g=K729_g³. The original group relation
forces B12³=B78³=gamma^-1 I. The 78D target that uses the selected
Nebe 78=Sym²(12^vee) source is canonically, with NO cubic-root choice,

    T78_g = gamma_g * Sym²((B12_g²)^transpose).

Indeed B12^-1=gamma_g B12², hence
gamma_g^-1 Sym²((B12^-1)^transpose)=T78_g.
An intertwiner F between the original actual 78D Monster multiplicity
block and that constructed target obeys simultaneously
    F B78_D = T78_D F,  F B78_E = T78_E F.

ALGORITHM: find a common simple eigenvalue of matching small
polynomials in D/E over F31; a 1D eigenspace fixes F up to scale.
Propagate a cyclic source/target vector under the SAME literal D/E
words, building a 78-column basis with incremental F31 row reduction.
Then F=target_basis*source_basis^-1, and verify BOTH 78x78 equations
entrywise. This is constructive, finite and independent of solving a
generic 6084-variable Kronecker system. A failed simple-eigen search
is INCONCLUSIVE, never declared a negative character theorem.

This is a SAME-ACTUAL-MMV F31 operator intertwiner when successful;
it is NOT a numerical ordinary-character-zero Monster module or a
source 6Suz standard-generator equivalence. Original ATLAS/mmgroup/
Ibrahim/GAP/TOE attribution remains with the source producers.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import numpy as np
from monster3b_actual_order3_projective_sym2_weld import (
    original_phase,INPUTS,trace,scalar_matrix,cubic,modmul,
    ratio_if_needed,eval31,P
)

PAIRS=[(i,j) for i in range(12) for j in range(i,12)]
assert len(PAIRS)==78

def eye(n):return np.eye(n,dtype=np.int64)
def inverse(A):
    A=np.asarray(A,dtype=np.int64)%P
    n=len(A)
    if A.shape!=(n,n):raise ValueError("not a square source F31 operator")
    W=np.concatenate((A,eye(n)),axis=1)
    for c in range(n):
        k=next((i for i in range(c,n) if W[i,c]),None)
        if k is None:raise ValueError("original source operator singular mod31")
        W[[c,k]]=W[[k,c]]
        W[c]=W[c]*pow(int(W[c,c]),-1,P)%P
        for i in range(n):
            if i!=c and W[i,c]:
                W[i]=(W[i]-int(W[i,c])*W[c])%P
    if not np.array_equal(modmul(A,W[:,n:]),eye(n)):
        raise AssertionError("finite-field inverse incomplete")
    return W[:,n:]

def symmetric_square(A):
    """Sym² on polynomial monomials x_i x_j, i<=j; char F31 != 2."""
    A=np.asarray(A,dtype=np.int64)%P
    if A.shape!=(12,12):raise ValueError("need actual degree12 module")
    S=np.zeros((78,78),dtype=np.int64)
    for col,(i,j) in enumerate(PAIRS):
        for row,(u,v) in enumerate(PAIRS):
            S[row,col]=((int(A[u,i])*int(A[v,j])+
                (int(A[v,i])*int(A[u,j]) if u!=v else 0))%P)
    return S

def singleton_nullspace(A):
    """RREF on H-lambda I; return unique null vector only if nullity 1."""
    A=np.asarray(A,dtype=np.int64)%P
    n=A.shape[1];m=A.shape[0]
    B=A.copy();pivots=[];r=0
    for c in range(n):
        k=next((i for i in range(r,m) if B[i,c]),None)
        if k is None:continue
        B[[r,k]]=B[[k,r]]
        B[r]=B[r]*pow(int(B[r,c]),-1,P)%P
        for i in range(m):
            if i!=r and B[i,c]:
                B[i]=(B[i]-int(B[i,c])*B[r])%P
        pivots.append(c);r+=1
        if r==m:break
    free=[i for i in range(n) if i not in set(pivots)]
    if len(free)!=1:return None
    v=np.zeros(n,dtype=np.int64);v[free[0]]=1
    for i,p in enumerate(pivots):v[p]=(-B[i,free[0]])%P
    if np.any(A@v%P):raise AssertionError("simple eigenvector construction wrong")
    return v

def seed_h(A,coefs):
    D,E=A["D"],A["E"]
    c,d,e=coefs
    return (c*D+d*E+e*modmul(D,E))%P

def cyclic_basis(v,w,S,T):
    """Transport orbit words, never infer maps from matching dimensions."""
    src=[];dst=[];piv=[];red=[];words=[]
    def accept(u,t,word):
        v=np.asarray(u,dtype=np.int64).copy()%P
        for p,basisrow in zip(piv,red):
            if v[p]:v=(v-int(v[p])*basisrow)%P
        nz=np.flatnonzero(v)
        if not len(nz):return False
        p=int(nz[0]);red.append(v*pow(int(v[p]),-1,P)%P);piv.append(p)
        src.append(np.asarray(u,dtype=np.int64).copy()%P)
        dst.append(np.asarray(t,dtype=np.int64).copy()%P)
        words.append(word)
        return True
    accept(v,w,"eig")
    index=0
    while index<len(src) and len(src)<78:
        for name in ("D","E"):
            u=S[name]@src[index]%P
            t=T[name]@dst[index]%P
            accept(u,t,words[index]+name)
            if len(src)==78:break
        index+=1
    if len(src)!=78:return None,{"cyclic_span_rank":len(src),
         "status":"NONCYCLIC_SIMPLE_EIGEN_SEED"}
    base=np.column_stack(src)
    transport=np.column_stack(dst)
    F=modmul(transport,inverse(base))
    if not np.array_equal(modmul(F,base),transport):
        raise AssertionError("cyclic source/target transport mismatch")
    if not all(np.array_equal(modmul(F,S[g]),modmul(T[g],F))
               for g in ("D","E")):
        return None,{"cyclic_span_rank":78,
            "status":"ORIGINAL_SOURCE_TARGET_GENERATORS_NOT_INTERTWINED"}
    try:Finv=inverse(F)
    except ValueError:
        return None,{"cyclic_span_rank":78,
            "status":"ORIGINAL_78_SOURCE_TARGET_INTERTWINER_SINGULAR"}
    assert all(np.array_equal(modmul(S[g],Finv),modmul(Finv,T[g]))
               for g in ("D","E"))
    return F,{"status":"ACTUAL_MM_MOD31_SIMULTANEOUS_78_INTERTWINER",
       "cyclic_span_rank":78,"independent_source_words":len(words),
       "max_constructed_word_length":max(map(len,words)),
       "intertwiner_inverse_two_sided":True,
       "original_Monster_D_and_E_generator_equations":2,
       "original_6Suz_ordinary_character_zero":False}

COEFS=[(1,1,0),(1,2,0),(1,3,0),(1,5,0),(2,3,0),
       (3,7,0),(1,1,1),(1,2,1),(2,1,3),(1,3,2),
       (5,7,1),(7,11,2),(13,4,9)]

def cyclic_linear_fallback(S,T):
    """Cyclic vector transport with just 78 target-vector unknowns.
    No simple eigenvalue is required. When the source is simple, any
    nonzero seed is cyclic and any nonzero equivariant map is invertible.
    """
    n=78
    for seed_index in range(n):
        vectors=[]; operators=[]; reduced=[]; pivots=[]
        def accept(v,W):
            x=v.copy()%P
            for p,row in zip(pivots,reduced):
                x=(x-int(x[p])*row)%P
            nz=np.flatnonzero(x)
            if not len(nz):return
            p=int(nz[0]);pivots.append(p)
            reduced.append(x*pow(int(x[p]),-1,P)%P)
            vectors.append(v.copy()%P);operators.append(W.copy()%P)
        accept(eye(n)[:,seed_index],eye(n))
        j=0
        while j<len(vectors) and len(vectors)<n:
            for g in ("D","E"):
                accept(S[g]@vectors[j]%P,modmul(T[g],operators[j]))
                if len(vectors)==n:break
            j+=1
        if len(vectors)!=n:continue
        B=np.column_stack(vectors);Binv=inverse(B)
        W=np.stack(operators)
        constraints=[]
        for g in ("D","E"):
            coeff=modmul(Binv,modmul(S[g],B))
            for i in range(n):
                constraints.append((modmul(T[g],W[i])-np.tensordot(coeff[:,i],W,axes=1))%P)
        R=np.concatenate(constraints,axis=0)
        # RREF in the target-vector unknowns, not n² matrix unknowns.
        piv=[];j=0
        for col in range(n):
            nz=np.flatnonzero(R[j:,col])
            if not len(nz):continue
            k=j+int(nz[0]);R[[k,j]]=R[[j,k]]
            R[j]=R[j]*pow(int(R[j,col]),-1,P)%P
            row=R[j].copy()
            R=(R-R[:,col,None]*row)%P
            R[j]=row;piv.append(col);j+=1
        free=[i for i in range(n) if i not in piv]
        if not free:return None,{"status":"CYCLIC_SOURCE_NO_NONZERO_HOM","isomorphism_disproved":True}
        for col in free:
            w=np.zeros(n,dtype=np.int64);w[col]=1
            for k,p in enumerate(piv):w[p]=-R[k,col]%P
            F=modmul(np.column_stack([M@w%P for M in W]),Binv)
            if not all(np.array_equal(modmul(F,S[g]),modmul(T[g],F)) for g in ("D","E")):
                raise AssertionError("cyclic linear equation mismatch")
            try:inverse(F)
            except ValueError:continue
            return F,{"status":"ACTUAL_MM_MOD31_SIMULTANEOUS_78_INTERTWINER",
                "method":"cyclic_linear_target_vector","hom_nullity":len(free),
                "cyclic_span_rank":n,"original_6Suz_ordinary_character_zero":False}
        return None,{"status":"CYCLIC_HOM_BASIS_SINGULAR","hom_nullity":len(free),"isomorphism_disproved":False}
    return None,{"status":"NO_CYCLIC_STANDARD_SEED_FOUND","isomorphism_disproved":False}

def find_intertwiner(S,T):
    if not all(S[k].shape==(78,78) and T[k].shape==(78,78)
               for k in ("D","E")):
        raise ValueError("original 78D blocks not compatible")
    tried=0
    for coefs in COEFS:
        hs=seed_h(S,coefs);ht=seed_h(T,coefs)
        for lam in range(P):
            sv=singleton_nullspace((hs-lam*eye(78))%P)
            if sv is None:continue
            tv=singleton_nullspace((ht-lam*eye(78))%P)
            if tv is None:continue
            tried+=1
            F,result=cyclic_basis(sv,tv,S,T)
            if F is not None:
                return F,{"polynomial_coefficients":list(coefs),
                    "eigenvalue":lam,"number_simple_common_eigenspaces":tried,
                    **result}
            if result["status"]=="ORIGINAL_SOURCE_TARGET_GENERATORS_NOT_INTERTWINED":
                return None,{"status":"SAME_SOURCE_OPERATOR_OBSTRUCTION",
                    "simple_eigenvalue":lam,"polynomial_coefficients":list(coefs),
                    **result}
    return cyclic_linear_fallback(S,T)

def from_source(model,folder,phase,outdir):
    phase_info=original_phase(model,folder,phase)
    for name in ("D","E"):
        if phase_info["words"].get(name,{}).get("status")!=(
            "PROJECTIVE_DUAL_SYM2_CHARACTER_WELD_CONSISTENT"):
            return {"status":"SOURCE_BLOCK_CUBIC_OR_CHAR_NOT_READY",
                "phase":phase,"word":name,
                "underlying_status":phase_info["words"].get(name)}
    S={};T={};B12={}
    for name,filename,k12,k78 in INPUTS:
        with np.load(Path(folder)/filename,allow_pickle=False) as npz:
            A=np.asarray(npz[k12],dtype=np.int64)%P
            B=np.asarray(npz[k78],dtype=np.int64)%P
        k=ratio_if_needed(model,phase,name)
        if k is None or k==0:
            raise ValueError("source 729 k0 zero; cannot build genuine modular 78")
        L12=A*pow(k,-1,P)%P
        L78=B*pow(k,-1,P)%P
        gamma=eval31(model["phases"][str(phase)]
                     ["order3_model_cubic_scalars"][name]
                     ["K_g_cube_scalar_Qzeta3"],5 if phase==1 else 25)
        assert scalar_matrix(cubic(L12),pow(gamma,-1,P))
        assert scalar_matrix(cubic(L78),pow(gamma,-1,P))
        target=gamma*symmetric_square(modmul(L12,L12).T)%P
        if not scalar_matrix(cubic(target),pow(gamma,-1,P)):
            raise AssertionError("projective dual symmetric square cubic wrong")
        S[name]=L78;T[name]=target;B12[name]=L12
    F,status=find_intertwiner(S,T)
    result={"source_phase":phase,"source_word_provenance":phase_info["provenance"],
        "original_MM_mod31_same_12_78_C2_blocks":True,
        "original_symmetric_square_operator_functor":True,
        "ordinary_char0_Monster_Hom_equivalence":False,
        **status}
    if F is not None:
        output=outdir/f"actual_MM_projective_Sym2_78_intertwiner_phase{phase}.npz"
        np.savez_compressed(output,transport78=F,inverse_transport78=inverse(F),
            actual_B78_D=S["D"],actual_B78_E=S["E"],
            derived_Sym2_D=T["D"],derived_Sym2_E=T["E"],
            actual_B12_D=B12["D"],actual_B12_E=B12["E"])
        result["operator_intertwiner_file"]=str(output)
        result["source_operator_intertwiner_built_not_character_only"]=True
    return result

def selftest():
    rng=np.random.default_rng(1491)
    def invertible(n):
        for i in range(40):
            M=rng.integers(0,P,size=(n,n),dtype=np.int64)
            try:return M,inverse(M)
            except ValueError:pass
        raise AssertionError("synthetic invertible source fixture unavailable")
    vals=[1]*5+[5]*4+[25]*3
    D=eye(12)
    E=np.diag(vals).astype(np.int64)
    A,invA=invertible(12)
    B,invB=invertible(12)
    # Two different genuine order-three operators.
    ordinary={"D":modmul(modmul(A,E),invA),
              "E":modmul(modmul(B,E),invB)}
    scalar={"D":P-1,"E":1}
    source12={name:operator*pow(scalar[name],-1,P)%P
              for name,operator in ordinary.items()}
    gamma={name:pow(v,3,P) for name,v in scalar.items()}
    target={name:gamma[name]*symmetric_square(
                 modmul(source12[name],source12[name]).T)%P
            for name in ordinary}
    U,Uinv=invertible(78)
    actual={name:modmul(modmul(Uinv,M),U)
            for name,M in target.items()}
    F,receipt=find_intertwiner(actual,target)
    if F is None or receipt["status"]!="ACTUAL_MM_MOD31_SIMULTANEOUS_78_INTERTWINER":
        raise AssertionError("correct original-shaped 78D synthetic transport not found")
    if not all(np.array_equal(modmul(F,actual[g]),modmul(target[g],F))
               for g in ("D","E")):
        raise AssertionError("source symmetric-square two-generator action wrong")
    wrong=dict(actual);wrong["E"]=eye(78)
    candidate,bad=find_intertwiner(wrong,target)
    if candidate is not None:
        raise AssertionError("wrong 78 action spuriously matched selected 12 dual square")
    return {"status":"PASS_FINITE_FIELD_CONSTRUCTIVE_SYM2_INTERTWINER_FIXTURE",
        "original_MM_source_supplied":False,
        "positive_two_generator_same_source_shape":receipt,
        "wrong_78_generator_rejected":True}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--model",type=Path)
    p.add_argument("--plus",type=Path)
    p.add_argument("--minus",type=Path)
    p.add_argument("--outdir",type=Path,default=Path(
       ".dashi/monster3b-mmgroup/actual_projective_sym2_intertwiner"))
    p.add_argument("--selftest",action="store_true")
    a=p.parse_args();a.outdir.mkdir(parents=True,exist_ok=True)
    if a.selftest:res=selftest()
    else:
        if a.model is None or (a.plus is None and a.minus is None):
            p.error("--model and at least --plus/--minus are required")
        model=json.loads(a.model.read_text())
        res={"schema":"monster3b-actual-MM-78-operator-vs-dualSym2-12-intertwiner-v1",
          "original_ordinary_complex_Hom_intertwiner":False,"phases":{}}
        for phase,folder in ((1,a.plus),(2,a.minus)):
            if folder is not None:
                res["phases"][str(phase)]=from_source(
                    model,folder,phase,a.outdir)
        if any(item["status"]=="SAME_SOURCE_OPERATOR_OBSTRUCTION"
               for item in res["phases"].values()):
            res["status"]="FAIL_CLOSED_SAME_SOURCE_MODULAR_OPERATOR_OBSTRUCTION"
        elif any(item["status"]=="ACTUAL_MM_MOD31_SIMULTANEOUS_78_INTERTWINER"
                 for item in res["phases"].values()):
            res["status"]="ACTUAL_MM_MODULAR_78_INTERTWINER_CONSTRUCTED_NOT_CHAR0"
        else:res["status"]="INCONCLUSIVE_SOURCE_OPERATOR_ATTACHMENT"
    out=a.outdir/"actual_MM_78_dualSym2_intertwiner_report.json"
    out.write_text(json.dumps(res,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"output":str(out),"status":res["status"],
         "actual_char0_intertwiner_claimed":False}))
    return 2 if res["status"].startswith("FAIL_CLOSED") else 0
if __name__=="__main__":raise SystemExit(main())
