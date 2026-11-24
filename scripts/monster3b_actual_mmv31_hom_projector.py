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
            status_file.write_text(json.dumps(record,indent=2)+"\n")
    print(json.dumps(record,indent=2))
    return 0
if __name__=="__main__": raise SystemExit(main())
