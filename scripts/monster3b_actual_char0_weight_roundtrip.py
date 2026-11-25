#!/usr/bin/env python3
"""Compose the actual exact Conway vacuum receipt with ALL signed weight coordinates.

No synthetic fallback. Original vacuum checkpoints must exist and match the
input/code identity. Per-weight coordinate and per-chunk reconstruction
checkpoints keep native execution resumable; the zero phase is retained.
"""
import argparse, json
from pathlib import Path
import numpy as np
from monster3b_actual_char0_vacuum import Checkpoint, Paused, atomic, scalar, sha
from monster3b_exact_weight_codec import OrdinaryCodec, coords
from monster3b_conway_exact_crt import ConwayNative, add, scale, linear_combination, require, DIM
from monster3b_char0_orbit_weld import K,Z,mat,col,columns,eye,serialize
from monster3b_linear_weight_frame import WeightFrame

STATUS="ACTUAL_CHAR0_SIGNED_VACUUM_GENERATOR_WELD"
DONE="ACTUAL_CHAR0_FULL_WEIGHT_ROUNDTRIP"

def read(p):return json.loads(p.read_text())
def matrix(a):return mat([[scalar(x) for x in row] for row in a])

def run(a):
    from mmgroup import MM
    from importlib.metadata import version
    r=read(a.vacuum/"actual_char0_result.json")
    require(r.get("status")==STATUS,"completed genuine exact vacuum receipt required")
    identity=r["identity"]
    require(identity["inputs"]["manifest"]==sha(a.manifest) and identity["inputs"]["cover"]==sha(a.cover),"original vacuum source mismatch")
    require(identity["mmgroup_version"]==version("mmgroup"),"native runtime changed")
    scripts=Path(__file__).resolve().parent
    for fn,digest in identity["code"].items():
        require(sha(scripts/fn)==digest,"vacuum producer code changed: "+fn)
    m,c=read(a.manifest),read(a.cover)
    require(m["source_blob_sha"]==c["original_source_blob_sha"],"original E source mismatch")
    native=ConwayNative();z=MM(m["center_word"])
    T=[MM(w) for w in m["translation_words"]];B=[MM(w) for w in m["modulation_words"]]
    require(len(T)==len(B)==6,"original six-axis chart required")
    F=WeightFrame(native.act,add,scale,Z,K.one,z,T,B)
    source_ck=Checkpoint(a.vacuum,identity,0)
    def unavailable():raise ValueError("missing source vacuum checkpoint")
    keys={s:r["basis_checkpoints"][str(s)] for s in (1,2)}
    piv={s:r["pivots"][str(s)] for s in (1,2)}
    for s in (1,2):
        require(len(keys[s])==len(piv[s])==90 and len(set(piv[s]))==90 and all(0<=j<DIM for j in piv[s]),"invalid original vacuum chart")
    def basis(s,i):return source_ck.vector(keys[s][i],unavailable)
    minor={s:columns([coords(basis(s,i),piv[s]) for i in range(90)]) for s in (1,2)}
    codec=OrdinaryCodec(F,piv,{s:minor[s].inv() for s in (1,2)},
             {s:matrix(r["actual_to_ordinary"][str(s)]) for s in (1,2)},
             {s:matrix(r["ordinary_to_actual"][str(s)]) for s in (1,2)},basis,DIM)
    probes=a.probe or [17,7936]
    require(all(0<=j<DIM for j in probes),"invalid original probe")
    v=linear_combination((K.convert(i+1) for i in range(len(probes))),
                         (native.unit(j) for j in probes),DIM)
    # All coordinate values (including zeros) and the exact centre-trivial
    # ambient component are preserved. Chunks are only execution scheduling.
    run_identity={"schema":"monster3b-original-char0-weight-roundtrip-v1",
                  "vacuum_receipt_sha256":sha(a.vacuum/"actual_char0_result.json"),
                  "source_identity":identity,"probe_indices":probes,
                  "probe_coefficients":list(range(1,len(probes)+1)),
                  "chunk_size":a.chunk_size,"consumer_sha256":sha(Path(__file__)),
                  "codec_sha256":sha(scripts/"monster3b_exact_weight_codec.py")}
    ck=Checkpoint(a.outdir,run_identity,a.max_new)
    zero=ck.vector("phase-zero",lambda:F.phase(v,0))
    require(F.phase(zero,0)==zero,"zero phase recovery discrepancy")
    # Checkpoint one column per marked phase/weight; never create a dense
    # 196884 by 65610 matrix. A zero coordinate still has a saved receipt.
    coordinate_keys={}
    for s in (1,2):
        for i,x in enumerate(F.points):
            key=f"coordinate-{s}-{i:03d}"
            def make(s=s,x=x):
                u=codec.encode(v,s,x)
                require(len(u)==90,"wrong ordinary coordinate count")
                return serialize(mat([u]))[0]
            values=ck.get(key,make)
            require(len(values)==90,"bad coordinate checkpoint")
            coordinate_keys[s,i]=key
    def get_coordinate(s,i):
        return [scalar(x) for x in ck.get(coordinate_keys[s,i],unavailable)]
    partial=[]
    for s in (1,2):
        for j in range(0,len(F.points),a.chunk_size):
            key=f"decoded-{s}-{j:03d}"
            def make(s=s,j=j):
                out=scale(K.zero,v)
                for i in range(j,min(j+a.chunk_size,len(F.points))):
                    u=get_coordinate(s,i)
                    if any(u):out=add(out,codec.decode(s,F.points[i],u))
                return out
            ck.vector(key,make);partial.append(key)
    from itertools import chain
    back=linear_combination((K.one for _ in range(1+len(partial))),
                            chain((zero,), (ck.vector(key,unavailable) for key in partial)),DIM)
    require(back==v,"full original ambient roundtrip residual")
    report={"status":DONE,"identity":run_identity,"original_ambient_dimension":DIM,
            "phase_weight_counts":[729,729],"ordinary_constituent_shapes":[[729,12],[729,78]],
            "original_zero_sector_retained":True,"actual_exact_ambient_roundtrip":True,
            "coordinate_checkpoint_keys":{str(s):[coordinate_keys[s,i] for i in range(729)] for s in (1,2)},
            "zero_checkpoint":"phase-zero","decoded_chunk_checkpoints":partial,
            "full_group_authentication_and_kernel_acceptance_separate":True}
    atomic(a.outdir/"actual_char0_weight_roundtrip.json",report)
    return DONE

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for t in ("manifest","cover","vacuum","outdir"):p.add_argument("--"+t,type=Path,required=True)
    p.add_argument("--probe",type=int,action="append",help="original ambient probe; repeat for a mixed vector")
    p.add_argument("--chunk-size",type=int,default=16)
    p.add_argument("--max-new",type=int)
    a=p.parse_args()
    if not 1<=a.chunk_size<=729 or (a.max_new is not None and a.max_new<0):p.error("invalid checkpoint budget/chunk")
    try:status=run(a)
    except Paused:print("CHECKPOINT_LIMIT_REACHED");return 3
    except Exception as exc:print("BLOCKED_OR_SOURCE_RESIDUAL",repr(exc));return 2
    print(status);return 0
if __name__=="__main__":raise SystemExit(main())
