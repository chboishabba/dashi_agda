#!/usr/bin/env python3
"""Matrix-free actual Monster W_zeta <-> Heisenberg^90 intertwiner producer.

Consumes the SAME 2026 source 3B/E/N word alignment emitted and checked by
monster_3b_mmgroup_source_symplectic_basis.py. Reuses the six Weyl A,B.
Over GF7 select 2-eigenspace of z and simultaneous 1-eigenspace of B_i;
find 90 linearly independent weight-zero vectors, then translate their orbits.

On a RIGHT MMV module, T(u,j)=s_j * product_i(A_i**(-u_i)).
Thus T(u,j)*B_i=2**u_i*T(u,j) and T(u,j)*A_i=T(u-e_i,j).
These are the source JFine HEISENBERG action with explicit right-vs-left
convention. Not the D4/Suz normalizer 12+78 identification.

An exact-head run requires mmgroup, absent here. Fail closed on every
unavailable, unsupported, or incomplete source contract.
"""
import argparse, json
from pathlib import Path

def candidates():
    for i in range(24):yield ("A",i,i)
    for tag in ("A","B","C"):
        for i in range(24):
            for j in range(i):
                yield(tag,i,j)
    for i in range(759):
        for j in range(64):yield("T",i,j)
    for tag in ("X","Y","Z"):
        for i in range(2048):
            for j in range(24):yield(tag,i,j)

def run(limit):
    from mmgroup import MM,MMV
    import numpy as np
    from monster_3b_mmgroup_source_symplectic_basis import run as source_run
    manifest,source_receipt=source_run()
    z=MM(manifest["center_word"])
    A=[MM(w) for w in manifest["translation_words"]]
    B=[MM(w) for w in manifest["modulation_words"]]
    V7=MMV(7)
    assert z.order()==3 and all(b.order()==3 for b in B)

    def zero_weight_project(v):
        w=5*(v+4*(v*z)+2*(v*(z**2)))
        for b in B:
            w=5*(w+(w*b)+(w*(b**2)))
        return w

    seed_labels=[];seed_vectors=[];basis=[];pivots=[]
    inspected=0
    for label in candidates():
        if inspected>=limit:break
        inspected+=1
        seed=zero_weight_project(V7(*label))
        if seed==0*seed:continue
        if seed*z!=2*seed or any(seed*b!=seed for b in B):
            raise RuntimeError("source weight projector not simultaneously idempotent/equivariant")
        arr=np.asarray(seed["E"],dtype=np.int16).copy()%7
        if len(arr)!=196884:
            raise RuntimeError("wrong actual Monster vector coordinate dimension")
        # Incremental exact GF7 Gaussian elimination. Rows inserted later
        # have zero values at all earlier pivots.
        for k,row in zip(pivots,basis):
            factor=int(arr[k])
            if factor:arr=(arr-factor*row)%7
        nonzero=np.flatnonzero(arr)
        if len(nonzero)==0:continue
        k=int(nonzero[0]); arr=(arr*pow(int(arr[k]),-1,7))%7
        pivots.append(k);basis.append(arr)
        seed_labels.append(list(label));seed_vectors.append(seed)
        if len(seed_labels)==90:break
    if len(seed_labels)!=90:
        raise RuntimeError(f"only {len(seed_labels)} independent weight-zero "
                           f"vectors after {inspected} original basis probes")

    def column(u,j):
        if not (len(u)==6 and all(isinstance(x,int) and 0<=x<3 for x in u)
                and isinstance(j,int) and 0<=j<90):
            raise ValueError("expected u in F3^6 and 0 <= j <90")
        v=seed_vectors[j]
        for a,t in zip(A,u):
            if t:v=v*(a**(-t))
        return v

    for j in (0,1,45,89):
        s=column([0]*6,j)
        for i in range(6):
            u=[0]*6;u[i]=1
            v=column(u,j)
            if v*z!=2*v or v*B[i]!=2*v:
                raise RuntimeError("right-module modulation eigenphase differs")
            for q in range(6):
                if v*B[q]!=(2 if i==q else 1)*v:
                    raise RuntimeError("right-module distinct weight test failed")
            if v*A[i]!=s:
                raise RuntimeError("right-module translation orientation differs")

    from importlib.metadata import version
    result=dict(
       status="actual_MMV7_weight_zero_basis_rank90_verified",
       source_url=manifest["source_url"],
       source_blob_sha=manifest["source_blob_sha"],
       source_group_certified=source_receipt["status"],
       modulus=7, zeta=2, selected_zeta_degree_by_source_character=65610,
       weight_zero_rank=90,
       scanned_196884_basis_vectors=inspected,
       seed_basis_labels=seed_labels,
       orbit_fibre_size=729,
       implicit_T_columns=729*90,
       right_module_translation_convention="T(u,j)*A_i=T(u-e_i,j)",
       right_module_modulation_convention="T(u,j)*B_i=zeta^u_i*T(u,j)",
       right_module_generator_checks=True,
       MMV_implementation_version=version("mmgroup"),
       all_65610_columns_explicitly_rank_checked=False,
       characteristic_zero_normalizer_12_78_computed=False,
       actual_normalizer_Hom_cocycle_computed=False
    )
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-candidates",type=int,default=20000)
    parser.add_argument("--receipt",type=Path)
    args=parser.parse_args()
    if args.max_candidates<=0:parser.error("max-candidates must be positive")
    try:from mmgroup import MMV
    except ImportError:parser.error("mmgroup required; cannot manufacture Monster vectors")
    data=run(args.max_candidates)
    if args.receipt:args.receipt.write_text(json.dumps(data,indent=2)+"\n")
    print(json.dumps(data,indent=2))

if __name__=="__main__":main()
