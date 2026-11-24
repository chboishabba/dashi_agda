#!/usr/bin/env python3
"""Actual Monster-vector *modular* Hom-vacuum source, not a fake char0 model.

Build the true source W[zeta]^B over F_31 via factorized idempotents:
  P_zeta = (I + zeta^-1 z + zeta^-2 z²)/3,
  P_B = product_i (I + B_i + B_i²)/3.
The genuine input is the previous mmgroup source manifest (original MM
words, 6 commuting B_i, actual order-three 3B centre).

Because 31 does not divide |E|=3^13, each nontrivial 729D E irrep
has one B-fixed vector. The ORIGINAL characteristic-zero 3B character
implies the target rank90, but actual linear independence of the 90
mod31 vectors is checked from MMV(31) ambient coordinates.

If a canonical C word receipt is provided, test C² preserves this
actual B-vacuum source and extract its full 90x90 mod31 matrix. This
may select the 12D C2 eigenspace without ever manufacturing a
characteristic-zero Monster Hom basis. It is distinctly marked as
MOD31 and never promoted to char zero / 4D / Steel word identity.

Run after authentic original manifest and canonical MM cover receipt:
  python3 scripts/monster3b_actual_mmv31_hom_projector.py \
    --manifest .dashi/monster3b-mmgroup/monster3b-authentic-manifest.json \
    --cover .dashi/monster3b-mmgroup/monster3b-canonical-cover-hit0.json \
    --outdir .dashi/monster3b-mmgroup/mmv31-hom

Only uses mmgroup MMV(31), numpy and exact finite-field row reduction.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import numpy as np

PRIME=31
INV3=pow(3,-1,PRIME)
ZETA=5  # 5^2+5+1 = 31
DIM=196884

def row_span_coefficients(array,basis,pivots):
    """Reduce an ambient vector against existing normalized F31 pivot rows."""
    x=np.asarray(array,dtype=np.int16).copy()
    if x.size!=DIM:raise ValueError("wrong original Monster ambient dimension")
    coeffs=[]
    for row,piv in zip(basis,pivots):
        k=int(x[piv])%PRIME
        coeffs.append(k)
        if k:x=(x-k*row)%PRIME
    return x,coeffs

def rank31(rows):
    A=np.asarray(rows,dtype=np.int16).copy()%PRIME
    if A.ndim!=2:return 0
    m,n=A.shape;r=0
    for j in range(n):
        nz=next((i for i in range(r,m) if A[i,j]),None)
        if nz is None:continue
        A[r],A[nz]=A[nz].copy(),A[r].copy()
        A[r]=(A[r]*pow(int(A[r,j]),-1,PRIME))%PRIME
        for i in range(m):
            if i!=r and A[i,j]:
                A[i]=(A[i]-int(A[i,j])*A[r])%PRIME
        r+=1
        if r==m:break
    return r

def nullspace31(M):
    """Exact F31 right nullspace basis, returned as n-by-nullity columns."""
    A=np.asarray(M,dtype=np.int16).copy()%PRIME
    nrows,ncols=A.shape
    pivots=[];r=0
    for col in range(ncols):
        k=next((i for i in range(r,nrows) if A[i,col]),None)
        if k is None:continue
        A[r],A[k]=A[k].copy(),A[r].copy()
        A[r]=(A[r]*pow(int(A[r,col]),-1,PRIME))%PRIME
        for i in range(nrows):
            if i!=r and A[i,col]:
                A[i]=(A[i]-int(A[i,col])*A[r])%PRIME
        pivots.append(col);r+=1
        if r==nrows:break
    free=[j for j in range(ncols) if j not in pivots]
    out=np.zeros((ncols,len(free)),dtype=np.int16)
    for idx,j in enumerate(free):
        out[j,idx]=1
        for i,p in enumerate(pivots):
            out[p,idx]=(-A[i,j])%PRIME
    return out

def coordinates_in_columns(B,images):
    """Return X s.t. B X = images, or fail exact ambient residual."""
    B=np.asarray(B,dtype=np.int16)%PRIME
    Y=np.asarray(images,dtype=np.int16)%PRIME
    m,n=B.shape
    if Y.shape[0]!=m or rank31(B.T)!=n:
        raise ValueError("invalid full-rank modular eigenbasis")
    # Pivot ROWS of B give invertible n-by-n square system.
    R=B.copy();chosen=[];r=0
    for i in range(m):
        a=R[i].copy()
        for p,row in chosen:
            if a[p]:a=(a-int(a[p])*row)%PRIME
        if not np.any(a):continue
        p=int(np.flatnonzero(a)[0])
        a=(a*pow(int(a[p]),-1,PRIME))%PRIME
        chosen.append((p,a));r+=1
        if r==n:break
    if len(chosen)!=n:raise ValueError("eigenvector coordinate basis lost full rank")
    idx=[]
    selected=[]
    for i in range(m):
        # Select original rows incrementally by rank of 12D row vectors
        if rank31(np.asarray(selected+[B[i].copy()],dtype=np.int16))>len(selected):
            selected.append(B[i].copy());idx.append(i)
        if len(selected)==n:break
    Z=np.asarray(selected,dtype=np.int16)
    W=Y[idx]
    aug=np.concatenate([Z,W],axis=1).astype(np.int16)
    for j in range(n):
        k=next((i for i in range(j,n) if aug[i,j]),None)
        if k is None:raise ValueError("source modular basis singular")
        aug[j],aug[k]=aug[k].copy(),aug[j].copy()
        aug[j]=(aug[j]*pow(int(aug[j,j]),-1,PRIME))%PRIME
        for i in range(n):
            if i!=j and aug[i,j]:
                aug[i]=(aug[i]-int(aug[i,j])*aug[j])%PRIME
    X=aug[:,n:]
    if not np.array_equal(matmul31(B,X),Y):
        raise ValueError("original modular source action fails eigenbasis closure")
    return X

def matmul31(A,B):
    return (np.asarray(A,dtype=np.int64)@np.asarray(B,dtype=np.int64))%PRIME

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--manifest",type=Path,default=Path(
      ".dashi/monster3b-mmgroup/monster3b-authentic-manifest.json"))
    ap.add_argument("--cover",type=Path)
    ap.add_argument("--outdir",type=Path,default=Path(
      ".dashi/monster3b-mmgroup/mmv31-hom"))
    ap.add_argument("--max-trials",type=int,default=480)
    ap.add_argument("--limit",type=int,default=90)
    ap.add_argument("--checkpoint-every",type=int,default=10)
    a=ap.parse_args()
    if a.limit<1 or a.limit>90 or a.max_trials<a.limit:
        ap.error("limit must be 1..90 and max-trials>=limit")
    from mmgroup import MM,MMV
    m=json.loads(a.manifest.read_text())
    if m.get("source_blob_sha")!="c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2":
        raise ValueError("wrong original E source blob")
    z=MM(m["center_word"]);B=[MM(w) for w in m["modulation_words"]]
    if len(B)!=6 or z.order()!=3 or any(
       b.order()!=3 or b*z!=z*b for b in B):
        raise ValueError("invalid original Heisenberg modulation source")
    if any(B[i]*B[j]!=B[j]*B[i] for i in range(6) for j in range(i+1,6)):
        raise ValueError("original modulation subgroup B is not abelian")
    V=MMV(PRIME)
    invz=pow(ZETA,-1,PRIME)
    za=[pow(invz,k,PRIME) for k in range(3)]
    b2=[b**2 for b in B]
    def project(v):
        out=INV3*(v+za[1]*(v*z)+za[2]*(v*(z**2)))
        for b,bb in zip(B,b2):
            out=INV3*(out+(out*b)+(out*bb))
        return out
    basis_arrays=[]; basis_mmv=[];pivots=[];probes=[]
    a.outdir.mkdir(parents=True,exist_ok=True)
    status_file=a.outdir/"mmv31_hom_status.json"
    def checkpoint(status,trial):
        record={"schema":"monster3b-actual-MMV31-B-vacuum-v1",
                "status":status,"p":PRIME,"zeta_mod_p":ZETA,
                "source_manifest":str(a.manifest),
                "actual_Monster_mod31_vectors":True,
                "actual_characteristic_zero_Monster_Hom":False,
                "number_independent_B_fixed_vectors":len(pivots),
                "target_dimension_from_original_character":90,
                "pivots":pivots,"source_E_basis_probe_indices":probes,
                "last_trial":trial}
        if pivots:
            np.savez_compressed(a.outdir/"ambient_basis_rows.npz",
                rows=np.asarray(basis_arrays,dtype=np.int16),
                pivots=np.array(pivots,dtype=np.int64),
                source_probes=np.array(probes,dtype=np.int64))
        status_file.write_text(json.dumps(record,indent=2)+"\n")
        return record
    for trial in range(a.max_trials):
        i=(7919*trial+17)%DIM
        v=project(V("E",i))
        arr=np.asarray(v["E"],dtype=np.int16)%PRIME
        reduced,coeff=row_span_coefficients(arr,basis_arrays,pivots)
        possible=np.flatnonzero(reduced)
        if len(possible)==0:continue
        pivot=int(possible[0]);k=pow(int(reduced[pivot]),-1,PRIME)
        reduced=(reduced*k)%PRIME
        # Mirror every ambient F31 elimination in the ACTUAL MMV module.
        for oldc,oldv in zip(coeff,basis_mmv):
            if oldc:v=v-oldc*oldv
        v=k*v
        if not np.array_equal(np.asarray(v["E"],dtype=np.int16)%PRIME,reduced):
            raise RuntimeError("MMV31 ambient coordinates disagree with linear F31 elimination")
        if v*z!=ZETA*v or any(v*b!=v for b in B):
            raise RuntimeError("original Monster B-vacuum projector condition failed")
        basis_arrays.append(reduced);basis_mmv.append(v)
        pivots.append(pivot);probes.append(i)
        if len(pivots)%a.checkpoint_every==0:
            checkpoint("IN_PROGRESS",trial)
        if len(pivots)>=a.limit:break
    record=checkpoint("COMPLETE_RANK90" if len(pivots)==90 else
        "PARTIAL_RANK",trial)
    if len(pivots)<a.limit:
        raise RuntimeError(f"only {len(pivots)} linearly independent actual MMV31 B-fixed vectors")
    if a.cover is not None:
        cover=json.loads(a.cover.read_text())
        c=MM(cover["canonical_C_word"])
        d=MM(cover["canonical_D_word"])
        j=c**2
        if d*z!=z*d:
            record["D_preserves_original_zeta_sector"]=False
        elif len(pivots)==90:
            # Projected phase-preserving D acts on the genuine 90D
            # B-vacuum carrier as k_0(D)*L_D, with unknown nonzero/zero
            # Weil-vacuum matrix coefficient k_0. This is an ACTUAL
            # modular operator but not yet a normalized 6.Suz word action.
            columns=[]
            for w in basis_mmv:
                t=project(w*d)
                x,coords=row_span_coefficients(
                    np.asarray(t["E"],dtype=np.int16)%PRIME,
                    basis_arrays,pivots)
                if np.any(x):
                    raise ValueError("D projected action leaves B-fixed 90D space")
                columns.append(coords)
            D0=np.asarray(columns,dtype=np.int16).T%PRIME
            np.savez_compressed(a.outdir/"actual_D_vacuum_sandwich_mod31.npz",
                                D0=D0)
            record["D_preserves_original_zeta_sector"]=True
            record["actual_D_vacuum_sandwich_mod31_rank"]=rank31(D0)
            record["D_vacuum_Weil_scalar_k0_determined"]=False
            record["source_GAP_standard_D_word_identified"]=False
        
        # Reidemeister-Schreier for the index-two centre-preserving
        # kernel in <C,D>: generators D, C D C^-1, C².
        # This second *authentic* inner group word gives an independent
        # 90D vacuum sandwich and (if J commutes) 12D/78D source blocks.
        # Its Weil-vacuum scalar is not inferred from a projective matrix.
        e=c*d*c**-1
        record["inner_kernel_generators"]="D; C D C^-1; C²"
        record["CDCinv_actual_word"]=str(e)
        if e*z!=z*e:
            raise ValueError("actual inner word C D C^-1 does not preserve centre")
        if len(pivots)==90:
            columns=[]
            for w in basis_mmv:
                t=project(w*e)
                x,coords=row_span_coefficients(
                    np.asarray(t["E"],dtype=np.int16)%PRIME,
                    basis_arrays,pivots)
                if np.any(x):
                    raise ValueError("C D C^-1 vacuum sandwich leaves the B-fixed 90D space")
                columns.append(coords)
            E0=np.asarray(columns,dtype=np.int16).T%PRIME
            np.savez_compressed(
                a.outdir/"actual_CDCinv_vacuum_sandwich_mod31.npz",E0=E0)
            record["actual_CDCinv_vacuum_sandwich_mod31_rank"]=rank31(E0)
            record["CDCinv_preserves_original_zeta_sector"]=True
            record["CDCinv_vacuum_Weil_scalar_determined"]=False
            record["CDCinv_original_6Suz_standard_word_identified"]=False
            # Source action is on the RIGHT (mmgroup MMV API):
            # for column-coordinate matrices M_(d*e)=M_e M_d.
            # Projecting after each factor inserts the B-vacuum idempotent.
            # Its exact failure to multiply is the original Weil
            # projective 2-cocycle, not numerical floating-point drift.
            if record.get("actual_D_vacuum_sandwich_mod31_rank")==90:
                D0=np.load(a.outdir/"actual_D_vacuum_sandwich_mod31.npz")["D0"]
                def projected_word(ww):
                    cols=[]
                    for vec in basis_mmv:
                        t=project(vec*ww)
                        remainder,coords=row_span_coefficients(
                            np.asarray(t["E"],dtype=np.int16)%PRIME,
                            basis_arrays,pivots)
                        if np.any(remainder):
                            raise ValueError("original product word vacuum image outside B-subspace")
                        cols.append(coords)
                    return np.asarray(cols,dtype=np.int16).T%PRIME
                DE0=projected_word(d*e)
                ED0=projected_word(e*d)
                np.savez_compressed(
                    a.outdir/"actual_inner_pair_vacuum_cocycle_mod31.npz",
                    D0=D0,E0=E0,DE0=DE0,ED0=ED0)
                def scalar_ratio(actual,expect):
                    expected=np.asarray(expect,dtype=np.int16)%PRIME
                    product=np.asarray(actual,dtype=np.int16)%PRIME
                    nz=np.argwhere(expected!=0)
                    if nz.size==0:
                        return {"is_scalar":bool(np.all(product==0)),
                                "scalar":None,"nonzero_reference":False}
                    i,j=(int(x) for x in nz[0])
                    alpha=int(product[i,j])*pow(int(expected[i,j]),-1,PRIME)%PRIME
                    return {"is_scalar":bool(np.array_equal(
                            product,(alpha*expected)%PRIME)),
                            "scalar":alpha,"nonzero_reference":True}
                record["original_MM31_vacuum_pair_DE_cocycle"]=scalar_ratio(
                    matmul31(E0,D0),DE0)
                record["original_MM31_vacuum_pair_ED_cocycle"]=scalar_ratio(
                    matmul31(D0,E0),ED0)
                record["original_MM31_projected_product_word_order"]={
                    "DE":"D then C D C^-1 (right action; E0 @ D0)",
                    "ED":"C D C^-1 then D (right action; D0 @ E0)"}
                record["Weil_projective_cocycle_original_source_computed"]=bool(
                    record["original_MM31_vacuum_pair_DE_cocycle"]["is_scalar"] and
                    record["original_MM31_vacuum_pair_ED_cocycle"]["is_scalar"])
                record["Weil_scalar_cocycle_promoted_to_complex"]=False

            E03=matmul31(matmul31(E0,E0),E0)
            cube_scalar=int(E03[0,0])
            cube_is_scalar=np.array_equal(
                E03,cube_scalar*np.eye(90,dtype=np.int16)%PRIME)
            record["actual_CDCinv_sandwich_cube_is_scalar"]=bool(cube_is_scalar)
            record["actual_CDCinv_sandwich_cube_scalar_mod31"]=(
                cube_scalar if cube_is_scalar else None)

        # This is meaningful if the canonical affine-zero -I C²
        # maps every B_i to B_i^-1 with no extra z phase.
        stabilizer=all(j*b*j**-1==b**-1 for b in B)
        record["canonical_C2_acts_as_pure_B_inversion"]=stabilizer
        if stabilizer and len(pivots)==90:
            columns=[]
            for w in basis_mmv:
                t=w*j
                x,coords=row_span_coefficients(
                    np.asarray(t["E"],dtype=np.int16)%PRIME,
                    basis_arrays,pivots)
                if np.any(x):
                    raise ValueError("C² action does not preserve 90D B-vacuum subspace")
                columns.append(coords)
            J=np.asarray(columns,dtype=np.int16).T%PRIME
            J2=matmul31(J,J)
            scalar=int(J2[0,0])
            central_square=(np.array_equal(J2,scalar*np.eye(90,dtype=np.int16)%PRIME))
            record["C2_induced_mod31_squared_is_scalar"]=central_square
            record["C2_square_scalar_mod31"]=scalar if central_square else None
            record["actual_C2_mod31_matrix_generated"]=True
            np.savez_compressed(a.outdir/"actual_C2_on_90_mod31.npz",
                                J=J,square=J2)
            if central_square:
                roots=[x for x in range(PRIME) if x*x%PRIME==scalar]
                record["C2_square_roots_mod31"]=roots
                if len(roots)==2:
                    r=roots[0];Id=np.eye(90,dtype=np.int16)
                    rankplus=rank31((J-r*Id)%PRIME)
                    rankminus=rank31((J+r*Id)%PRIME)
                    record["C2_source_block_dimensions_unordered"]=[
                        90-rankplus,90-rankminus]
                    record["selected_12_plus_78_dimensions_found"]=(sorted([
                        90-rankplus,90-rankminus])==[12,78])
                    if record["selected_12_plus_78_dimensions_found"]:
                        eig_r=nullspace31((J-r*Id)%PRIME)
                        eig_neg=nullspace31((J+r*Id)%PRIME)
                        eig12=eig_r if eig_r.shape[1]==12 else eig_neg
                        eig78=eig_neg if eig_r.shape[1]==12 else eig_r
                        np.savez_compressed(a.outdir/"actual_C2_12_78_mod31.npz",
                                           eig12=eig12,eig78=eig78)
                        record["actual_12D_Hom_eigenvectors_mod31"]=True
                        if record.get("actual_D_vacuum_sandwich_mod31_rank")==90:
                            D0=np.load(a.outdir/"actual_D_vacuum_sandwich_mod31.npz")["D0"]
                            commutes=np.array_equal(
                              matmul31(J,D0),matmul31(D0,J))
                            record["D_vacuum_sandwich_commutes_with_C2"]=commutes
                            if commutes:
                                D12=coordinates_in_columns(eig12,matmul31(D0,eig12))
                                D78=coordinates_in_columns(eig78,matmul31(D0,eig78))
                                np.savez_compressed(
                                    a.outdir/"actual_D_12_78_vacuum_sandwich_mod31.npz",
                                    D12=D12,D78=D78)
                                record["actual_mod31_D12_sandwich_matrix_extracted"]=True
                                record["D12_Weil_coefficient_normalized"]=False
                        if record.get("actual_CDCinv_vacuum_sandwich_mod31_rank")==90:
                            E0=np.load(
                                a.outdir/"actual_CDCinv_vacuum_sandwich_mod31.npz")["E0"]
                            ecomm=np.array_equal(
                                matmul31(J,E0),matmul31(E0,J))
                            record["CDCinv_vacuum_sandwich_commutes_with_C2"]=bool(ecomm)
                            if ecomm:
                                E12=coordinates_in_columns(eig12,matmul31(E0,eig12))
                                E78=coordinates_in_columns(eig78,matmul31(E0,eig78))
                                np.savez_compressed(
                                    a.outdir/"actual_CDCinv_12_78_vacuum_sandwich_mod31.npz",
                                    E12=E12,E78=E78)
                                record["actual_mod31_CDCinv12_sandwich_matrix_extracted"]=True
                                record["CDCinv12_Weil_coefficient_normalized"]=False
                                E12cube=matmul31(matmul31(E12,E12),E12)
                                candidate=int(E12cube[0,0])
                                is_scalar=np.array_equal(
                                    E12cube,candidate*np.eye(12,dtype=np.int16)%PRIME)
                                record["CDCinv12_sandwich_cube_is_scalar"]=bool(is_scalar)
                                record["CDCinv12_sandwich_cube_scalar_mod31"]=(
                                    candidate if is_scalar else None)


            status_file.write_text(json.dumps(record,indent=2)+"\n")
    print(json.dumps(record,indent=2))
    return 0
if __name__=="__main__": raise SystemExit(main())
