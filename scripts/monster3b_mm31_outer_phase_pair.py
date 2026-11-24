#!/usr/bin/env python3
"""L12R: genuine Monster MMV31 90+90 phase-exchange by literal corrected C.

Input is the two independently source-checked original MMV(31) B-vacuum
receipts, with ζ=5 and ζ^-1=25 and the SAME authentic E manifest.

Rebuild the 90 source vectors from the recorded original E-basis probes,
verifying each row against the saved true Monster ambient source; then
compute C:S_ζ -> S_{ζ^-1} and its inverse-direction action in MMV(31).

Because the map is a vacuum sandwich, the two compositions need not
equal C² but must equal it up to the original 729D Weil vacuum scalar
if the selected vacua have nonzero overlap. Compute, do not assume it.
Characteristic-zero 12D Hom/outer and literal 4D class are NOT inferred.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
from mmgroup import MM,MMV
from monster3b_actual_mmv31_hom_projector import (
    row_span_coefficients, matmul31, rank31, coordinates_in_columns
)

P=31
DIM=196884
RANK=90
def scalar_ratio(M,N):
    M=np.asarray(M,dtype=np.int64)%P
    N=np.asarray(N,dtype=np.int64)%P
    nz=np.argwhere(N!=0)
    if len(nz)==0:
        return {"scalar":None,"is_scalar":bool(np.all(M==0)),
                "nonzero_reference":False}
    i,j=(int(x) for x in nz[0])
    scalar=int(M[i,j])*pow(int(N[i,j]),-1,P)%P
    return {"scalar":scalar,"is_scalar":bool(np.array_equal(M,scalar*N%P)),
            "nonzero_reference":True}

def open_original(path,zeta):
    f=Path(path)
    result=json.loads((f/"mmv31_hom_status.json").read_text())
    if (result.get("p"),result.get("zeta_mod_p"),
            result.get("number_independent_B_fixed_vectors"))!=(31,zeta,90):
        raise ValueError("wrong marked source phase/p/rank from authentic receipt")
    original=f/"ambient_basis_rows_mod31.npz"
    # Old original source pre-generalization saved filename without mod31.
    if not original.is_file():original=f/"ambient_basis_rows.npz"
    if not original.is_file():raise ValueError("genuine original Monster ambient-basis archive absent")
    with np.load(original) as v:
        rows=np.asarray(v["rows"],dtype=np.int16)%P
        pivots=[int(x) for x in v["pivots"]]
        probes=[int(x) for x in v["source_probes"]]
    if rows.shape!=(90,DIM) or len(pivots)!=90 or len(probes)!=90:
        raise ValueError("original 90 Monster source vector row shape mismatch")
    if pivots!=[int(x) for x in result["pivots"]]:
        raise ValueError("source basis pivots disagree with original source ledger")
    return result,rows,pivots,probes

def reconstruct(rows,pivots,probes,zeta,V,z,B):
    inv=pow(3,-1,P)
    weights=[pow(zeta,-k,P) for k in range(3)]
    b2=[b**2 for b in B]
    def project(w):
        t=inv*(w+weights[1]*(w*z)+weights[2]*(w*z**2))
        for b,bb in zip(B,b2):
            t=inv*(t+t*b+t*bb)
        return t
    basis=[];normalized=[]
    for j,idx in enumerate(probes):
        w=project(V("E",idx))
        arr=np.asarray(w["E"],dtype=np.int16)%P
        residual,coeff=row_span_coefficients(arr,normalized,pivots[:j])
        if not np.any(residual):
            raise ValueError("recorded genuine Monster probe lost independent rank")
        if int(residual[pivots[j]])==0:
            raise ValueError("original selected pivot not recovered")
        fac=pow(int(residual[pivots[j]]),-1,P)
        reduced=(residual*fac)%P
        for c,v in zip(coeff,basis):
            if c:w=w-c*v
        w=fac*w
        if not np.array_equal(reduced,rows[j]):
            raise ValueError("original MMV31 saved true Monster vector reconstruction disagrees")
        if w*z!=zeta*w or any(w*b!=w for b in B):
            raise ValueError("source Monster reconstructed vector not in marked vacuum")
        basis.append(w);normalized.append(reduced)
    return basis,project

def source_action(domain_basis,target_project,target_rows,target_pivots,g):
    columns=[]
    for v in domain_basis:
        w=target_project(v*g)
        residue,coords=row_span_coefficients(
            np.asarray(w["E"],dtype=np.int16)%P,target_rows,target_pivots)
        if np.any(residue):
            raise ValueError("literal source outer word projection outside genuine 90D target")
        columns.append(coords)
    return np.asarray(columns,dtype=np.int16).T%P

def eigenspace_blocks(sourcepath,targetpath,U):
    names=("eig12","eig78")
    def read(folder):
        with np.load(Path(folder)/"actual_C2_12_78_mod31.npz") as f:
            return {name:np.asarray(f[name],dtype=np.int16)%P for name in names}
    src,tgt=read(sourcepath),read(targetpath)
    out={}
    for name in names:
        try:
            image=matmul31(U,src[name])
            block=coordinates_in_columns(tgt[name],image)
            out[name]={"status":"SOURCE_OUTER_BLOCK_EXTRACTED",
                       "matrix":block}
        except ValueError as exc:
            out[name]={"status":"SOURCE_OUTER_BLOCK_NOT_IN_SELECTED_EIGENSPACE",
                       "error":str(exc)}
    return out

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--plus",type=Path,required=True)
    p.add_argument("--minus",type=Path,required=True)
    p.add_argument("--manifest",type=Path,required=True)
    p.add_argument("--cover",type=Path,required=True)
    p.add_argument("--outdir",type=Path,required=True)
    a=p.parse_args()
    a.outdir.mkdir(parents=True,exist_ok=True)
    output=a.outdir/"actual_MM31_outer_phase_result.json"
    record={"schema":"monster3b-genuine-MMV31-phase-exchanging-C-v1",
            "status":"NOT_EXECUTED",
            "actual_Monster_MM_mod31":False,
            "actual_characteristic_zero_Monster_Hom":False,
            "literal_MM_C_Monster_class4D_identified":False}
    try:
        manifest=json.loads(a.manifest.read_text())
        cover=json.loads(a.cover.read_text())
        plus,Rp,Pp,sp=open_original(a.plus,5)
        minus,Rm,Pm,sm=open_original(a.minus,25)
        if (plus.get("source_manifest")!=minus.get("source_manifest")
            or manifest.get("source_blob_sha")!=
             "c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2"):
            raise ValueError("not the same authenticated original Monster 3B E")
        source_hashes={}
        for label,folder,state in (("plus",a.plus,plus),("minus",a.minus,minus)):
            for key in ("canonical_C_word","canonical_D_word"):
                if state.get(key)!=cover.get(key) or not state.get(key):
                    raise ValueError("missing or mismatched literal C/D source identity: "+key)
            if state.get("original_E_source_blob_sha")!=manifest["source_blob_sha"]:
                raise ValueError("source E identity mismatch")
            for filename in ("mmv31_hom_status.json","actual_C2_12_78_mod31.npz",
                    "actual_C2_on_90_mod31.npz","actual_D_12_78_vacuum_sandwich_mod31.npz",
                    "actual_CDCinv_12_78_vacuum_sandwich_mod31.npz"):
                source_hashes[label+"/"+filename]=hashlib.sha256((folder/filename).read_bytes()).hexdigest()
            ambient=folder/"ambient_basis_rows_mod31.npz"
            if not ambient.is_file():ambient=folder/"ambient_basis_rows.npz"
            source_hashes[label+"/"+ambient.name]=hashlib.sha256(ambient.read_bytes()).hexdigest()
        record["manifest_sha256"]=hashlib.sha256(a.manifest.read_bytes()).hexdigest()
        record["cover_sha256"]=hashlib.sha256(a.cover.read_bytes()).hexdigest()
        record["source_packet_sha256"]=source_hashes
        record["canonical_C_word"]=cover["canonical_C_word"]
        record["canonical_D_word"]=cover["canonical_D_word"]
        record["original_E_source_blob_sha"]=manifest["source_blob_sha"]
        z=MM(manifest["center_word"])
        B=[MM(s) for s in manifest["modulation_words"]]
        if len(B)!=6 or z.order()!=3:
            raise ValueError("invalid authentic original 3B E")
        C=MM(cover["canonical_C_word"])
        if C*z*C**-1!=z**-1 or C.order()!=4:
            raise ValueError("canonical original Monster C does not invert 3B centre")
        V=MMV(P)
        Bp,proj_p=reconstruct(Rp,Pp,sp,5,V,z,B)
        Bm,proj_m=reconstruct(Rm,Pm,sm,25,V,z,B)
        Upm=source_action(Bp,proj_m,Rm,Pm,C)
        Ump=source_action(Bm,proj_p,Rp,Pp,C)
        if rank31(Upm)!=90 or rank31(Ump)!=90:
            raise ValueError("source C vacuum overlap is singular in paired 90D sectors")
        with np.load(a.plus/"actual_C2_on_90_mod31.npz") as data:
            Jp=np.asarray(data["J"],dtype=np.int16)%P
        with np.load(a.minus/"actual_C2_on_90_mod31.npz") as data:
            Jm=np.asarray(data["J"],dtype=np.int16)%P
        # MMV is a RIGHT action; matrices act on coefficient columns.
        # C on plus followed by C on minus => Ump @ Upm.
        sqp=scalar_ratio(matmul31(Ump,Upm),Jp)
        sqm=scalar_ratio(matmul31(Upm,Ump),Jm)
        np.savez_compressed(a.outdir/"actual_MM31_outer_C_90_pair.npz",
            Upm=Upm,Ump=Ump,Jplus=Jp,Jminus=Jm)
        forward=eigenspace_blocks(a.plus,a.minus,Upm)
        reverse=eigenspace_blocks(a.minus,a.plus,Ump)
        block_dump={}
        for direction,parts in (("plus_to_minus",forward),
                                ("minus_to_plus",reverse)):
            for label,datum in parts.items():
                block_dump[direction+"_"+label]=datum["status"]
                if "matrix" in datum:
                    block_dump[direction+"_"+label+"_rank"]=rank31(
                        datum["matrix"])
                    np.savez_compressed(
                        a.outdir/("actual_MM31_C_"+direction+"_"+label+".npz"),
                        matrix=datum["matrix"])
        record.update({
          "status":"ACTUAL_MM31_OUTER_VACUUM_PROJECTIVE_ACTION",
          "actual_Monster_MM_mod31":True,
          "phase_plus_zeta":5,"phase_minus_zeta":25,
          "outer_plus_to_minus_rank":rank31(Upm),
          "outer_minus_to_plus_rank":rank31(Ump),
          "outer_squared_on_plus_vs_actual_C2":sqp,
          "outer_squared_on_minus_vs_actual_C2":sqm,
          "outer_projective_scalar_same_in_both_phases":(
            sqp.get("is_scalar") is True and sqm.get("is_scalar") is True and
            sqp.get("scalar")==sqm.get("scalar")),
          "12_78_outer_source_block_outcomes":block_dump,
          "outer_729_Weil_scalar_ordinary_lift_fixed":False,
          "actual_complex_180D_outer_matrix_extracted":False})
    except Exception as exc:
        record.update(status="ERROR_FAIL_CLOSED",error=repr(exc))
    output.write_text(json.dumps(record,indent=2,sort_keys=True)+"\n")
    print(json.dumps(record,indent=2,sort_keys=True))
    return 0 if record["status"]!="ERROR_FAIL_CLOSED" else 2
if __name__=="__main__": raise SystemExit(main())
