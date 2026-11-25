#!/usr/bin/env python3
"""Actual characteristic-zero Conway vacuum and signed ordinary coordinates.

Requires genuine mmgroup, original manifest, corrected cover, canonical Weil
receipt and the saved DIRECT positive MMV31 probes. Reproject original unit
coordinates over Q(zeta); never rationally lift arbitrary modular basis rows.
Per-vector/column checkpoints allow bounded invocations. Original source
authentication and kernel acceptance are separate.
"""
import argparse, gzip, hashlib, json, os
from pathlib import Path
import numpy as np
from sympy import QQ
from monster3b_conway_exact_crt import ConwayNative, Vector, add, scale, reduce_vector, linear_combination, DIM, require
from monster3b_linear_weight_frame import WeightFrame
from monster3b_char0_orbit_weld import K,Z,mat,col,columns,serialize,source,signed_weld,signed_from_positive

SOURCE="c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2"
P=31

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def scalar(x):return K.convert(QQ(x[0]))+Z*K.convert(QQ(x[1]))
def coords(v,piv):return [(K.convert(int(v.a[j]))+Z*K.convert(int(v.b[j])))/K.convert(v.d) for j in piv]
def atomic(p,obj):
    tmp=p.with_suffix(p.suffix+".tmp")
    tmp.write_text(json.dumps(obj,indent=2)+"\n");os.replace(tmp,p)

class Paused(Exception):pass

class Checkpoint:
    def __init__(self,root,identity,budget):
        self.root,self.identity,self.budget,self.new=root,identity,budget,0
        root.mkdir(parents=True,exist_ok=True)
        p=root/"identity.json"
        if p.exists():require(read(p)==identity,"checkpoint source or code changed; use fresh directory")
        else:atomic(p,identity)
    def get(self,key,make):
        p=self.root/(key+".json.gz");h=p.with_suffix(".sha256")
        if p.is_file() and h.is_file():
            require(h.read_text().strip()==sha(p),"checkpoint hash mismatch "+key)
            with gzip.open(p,"rt") as f:obj=json.load(f)
            require(obj["identity"]==self.identity and obj["key"]==key,"checkpoint lineage mismatch")
            return obj["value"]
        if self.budget is not None and self.new>=self.budget:raise Paused()
        value=make()
        tmp=p.with_suffix(".tmp")
        with gzip.open(tmp,"wt") as f:json.dump({"identity":self.identity,"key":key,"value":value},f)
        os.replace(tmp,p);h.write_text(sha(p)+"\n")
        self.new+=1;print("CHECKPOINT",key,flush=True)
        return value
    def vector(self,key,make):
        def encode():
            v=make()
            return [str(v.d),[str(x) for x in v.a],[str(x) for x in v.b]]
        d,a,b=self.get(key,encode)
        require(len(a)==len(b)==DIM and int(d)>0,"bad vector checkpoint")
        return Vector(np.array(list(map(int,a)),dtype=object),np.array(list(map(int,b)),dtype=object),int(d))

def run(a):
    from importlib.metadata import version
    from mmgroup import MM
    from monster3b_mm31_outer_phase_pair import open_original
    from monster3b_actual_mmv31_hom_projector import row_span_coefficients
    from monster3b_literal_standard_D_phase import run as literal_phase
    from monster3b_lindsey_actual_mod31_join import source_matrices,dual
    from monster3b_single_residual_frame import source_frame
    m,c,k,data=map(read,(a.manifest,a.cover,a.model,a.source))
    source_bytes=a.source.read_bytes()
    require(hashlib.sha1(b"blob "+str(len(source_bytes)).encode()+b"\0"+source_bytes).hexdigest()=="b0f96b37494cfca56f116b991d350352d3a493f2","unrecognized original Lindsey source bytes")
    st,rows,piv,probes=open_original(a.plus,5)
    require(m.get("source_blob_sha")==c.get("original_source_blob_sha")==st.get("original_E_source_blob_sha")==k.get("original_E_source_blob_sha")==SOURCE,"original E mismatch")
    require(k.get("status")=="CANONICAL_MODEL_SIGNED_SECTION" and k.get("source_chart")=="literal corrected MM quotient","canonical original model required")
    require(k.get("central_cover_relators")==c.get("central_cover_relators"),"canonical cover mismatch")
    require(len(k.get("quotient_relators_mod31",{}))==10 and all(k["quotient_relators_mod31"].values()),"canonical model relator receipt")
    require(all(st.get(t) and st[t]==c.get(t)==k.get(t) for t in ("canonical_C_word","canonical_D_word")) and not st.get("derived_from_plus"),"literal direct source words")
    phase=literal_phase(a.manifest,a.cover)
    require(phase["raw_wheel_has_order13"],"literal wheel mismatch")
    q=phase["Q7_central_z_power"]
    native=ConwayNative()
    z=MM(m["center_word"]);C=MM(c["canonical_C_word"]);D=MM(c["canonical_D_word"])
    T=[MM(w) for w in m["translation_words"]];B=[MM(w) for w in m["modulation_words"]]
    require(len(T)==len(B)==6 and all(t.order()==3 and t*z==z*t for t in T+B),"original order-three axes")
    require(all(x*y==y*x for axes in (T,B) for x in axes for y in axes),"original polarization")
    pairing=[[next((j for j in range(3) if t*b*t**-1*b**-1==z**j),None) for b in B] for t in T]
    require(all(x is not None for r in pairing for x in r),"noncentral commutator")
    A=np.asarray(pairing,dtype=np.int64)
    for i in range(6):
        j=next((j for j in range(i,6) if A[j,i]),None);require(j is not None,"degenerate original pairing")
        A[[i,j]]=A[[j,i]];A[i]=A[i]*A[i,i]%3
        for j in range(i+1,6):A[j]=(A[j]-A[j,i]*A[i])%3
    F=WeightFrame(native.act,add,scale,Z,K.one,z,T,B)
    def coefficient(g,s):
        if g=="J":return K.one
        t=3-s if g=="C" else s
        rec=k["generators"][f"{g}:{t if g=='C' else s}"]
        require(rec.get("zero_affine_vacuum_unit_verified") is True,"missing canonical vacuum unit")
        value=scalar(rec["normalized_vacuum_Qzeta3"])
        require(value!=K.zero,"zero canonical vacuum")
        return value
    cp=coefficient("C",1)
    amb=a.plus/"ambient_basis_rows_mod31.npz"
    if not amb.is_file():amb=a.plus/"ambient_basis_rows.npz"
    code=Path(__file__).parent
    identity={"inputs":{t:sha(getattr(a,t)) for t in ("manifest","cover","model","source")},
              "plus_ambient_sha256":sha(amb),"plus_status_sha256":sha(a.plus/"mmv31_hom_status.json"),
              "code":{t:sha(code/t) for t in ("monster3b_actual_char0_vacuum.py","monster3b_conway_exact_crt.py","monster3b_linear_weight_frame.py","monster3b_char0_orbit_weld.py","monster3b_literal_standard_D_phase.py","monster3b_mm31_outer_phase_pair.py","monster3b_actual_mmv31_hom_projector.py","monster3b_lindsey_actual_mod31_join.py","monster3b_actual_projective_sym2_intertwiner.py","monster3b_single_residual_frame.py","monster3b_singer_cyclic_hom.py")},
              "mmgroup_version":version("mmgroup"),"D_phase":q}
    ck=Checkpoint(a.outdir,identity,a.max_new)
    pivots={1:list(piv),2:[]};negrows=[];positive=[];negative=[]
    # Preserve the original coordinate probes. Exact raw projections, not
    # echelon-normalized residue vectors, are the characteristic-zero basis.
    for i,j in enumerate(probes):
        v=ck.vector(f"plus-{i:02d}",lambda j=j:F.vacuum(native.unit(j),1))
        r,_=row_span_coefficients(reduce_vector(v,31,5),rows[:i],piv[:i])
        require(r[piv[i]]!=0 and np.array_equal(r*pow(int(r[piv[i]]),-1,31)%31,rows[i]),"original probe reduction disagreement")
        positive.append(f"plus-{i:02d}")
        w=ck.vector(f"minus-{i:02d}",lambda v=v:F.hom(v,1,2,C,cp))
        r,_=row_span_coefficients(reduce_vector(w,31,5),negrows,pivots[2])
        nz=np.flatnonzero(r);require(len(nz)>0,"negative exact projection rank loss at marked prime")
        p=int(nz[0]);pivots[2].append(p);negrows.append(r*pow(int(r[p]),-1,31)%31)
        negative.append(f"minus-{i:02d}")
    keys={1:positive,2:negative}
    def load(key):return ck.vector(key,lambda:(_ for _ in ()).throw(ValueError("missing completed basis")))
    minor={s:columns([coords(load(key),pivots[s]) for key in keys[s]]) for s in (1,2)}
    inv={s:minor[s].inv() for s in (1,2)}
    words={"C":C,"D":D,"E":C*D*C**-1,"J":C**2}
    def actual_column(g,s,i):
        t=3-s if g=="C" else s
        v=load(keys[s][i]);w=F.hom(v,s,t,words[g],coefficient(g,s))
        x=(inv[t]*col(coords(w,pivots[t]))).transpose().to_list()[0]
        # Stream the original full ambient recomposition, normalizing once.
        nz=[(b,h) for b,h in zip(x,keys[t]) if b]
        out=linear_combination((b for b,h in nz),(load(h) for b,h in nz),DIM)
        require(out==w,"exact original ambient closure residual")
        return serialize(mat([x]))[0]
    positive_ops={}
    for g in ("D","E","J"):
        xs=[]
        for i in range(90):
            xs.append([scalar(x) for x in ck.get(f"op-{g}-1-{i:02d}",lambda g=g,i=i:actual_column(g,1,i))])
        positive_ops[g]=columns(xs)
    # The negative basis is L(C) times the positive basis by construction.
    # This uses the authenticated honest signed Weil-action and cover laws.
    operators=signed_from_positive(positive_ops["D"],positive_ops["E"],positive_ops["J"])
    for g in ("C","D","E","J"):
        expected=positive_ops["J"] if g=="J" else operators[g][2]
        for i in range(a.negative_audit):
            actual=[scalar(x) for x in ck.get(f"audit-{g}-2-{i:02d}",lambda g=g,i=i:actual_column(g,2,i))]
            require(col(actual)==expected.extract(list(range(90)),[i]),"negative derived generator audit mismatch "+g)
    A=source_matrices(data,q);U={g:dual(A[g],g=="C") for g in A}
    orbits={}
    for n,src in ((12,A),(78,U)):
        r=source_frame({g:src[g][:n,:n] for g in ("D","E")})
        orbits[n]=(r["words"],r["index"])
    maps=signed_weld(operators,source(data,q),orbits)
    result={"status":"ACTUAL_CHAR0_SIGNED_VACUUM_GENERATOR_WELD",
            "identity":identity,"literal_phase":phase,"pivots":pivots,"basis_checkpoints":keys,
            "operators":{g:{s:serialize(M) for s,M in d.items()} for g,d in operators.items()},
            "actual_to_ordinary":{s:serialize(maps[s][0]) for s in (1,2)},
            "ordinary_to_actual":{s:serialize(maps[s][1]) for s in (1,2)},
            "source_dimension_hypothesis":"actual 3B phase dimension 65610 and nondegenerate Heisenberg chart imply vacuum dimension 90",
            "full_group_authentication_and_kernel_acceptance_separate":True,
            "positive_direct_operator_columns":270,
            "negative_generator_columns_independently_replayed":4*a.negative_audit,
            "negative_generator_maps_derived_from_honest_signed_action":True,
            "whole_ambient_weight_roundtrip_executed":False}
    atomic(a.outdir/"actual_char0_result.json",result)
    return result["status"]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for t in ("manifest","cover","model","plus","outdir"):p.add_argument("--"+t,type=Path,required=True)
    p.add_argument("--source",type=Path,default=Path(__file__).resolve().parents[1]/"Docs/support/reference/Monster3BLindseyOrdinaryCD20261124.json")
    p.add_argument("--max-new",type=int,help="maximum newly evaluated vector/column checkpoints this invocation")
    p.add_argument("--negative-audit",type=int,default=1,help="independently replay this many columns per negative C/D/E/C2 (0..90)")
    a=p.parse_args()
    if not 0<=a.negative_audit<=90:p.error("negative audit must be 0..90")
    if a.max_new is not None and a.max_new<0:p.error("negative checkpoint limit")
    try:status=run(a)
    except Paused:print("CHECKPOINT_LIMIT_REACHED");return 3
    except Exception as e:print("BLOCKED_OR_SOURCE_RESIDUAL",repr(e));return 2
    print(status);return 0

if __name__=="__main__":raise SystemExit(main())
