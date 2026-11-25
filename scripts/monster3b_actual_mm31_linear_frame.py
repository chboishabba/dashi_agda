"""Bind the full signed linear frame to genuine MMV31 source words and rows.

This is the numerical good-prime realization of the actual-carrier formula,
not characteristic-zero matrix reconstruction.  No synthetic rows accepted.
The centre-trivial vector is retained unchanged.  Stream one weight at a time:
two 729 x 90 coordinate arrays rather than 1458 ambient vectors.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
from sympy import GF
from monster3b_linear_weight_frame import WeightFrame

P = 31
SOURCE = "c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2"

def require(ok, msg):
    if not ok:
        raise ValueError(msg)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

class ActualFrame31:
    def __init__(self, manifest, cover, plus):
        from mmgroup import MM, MMV
        from monster3b_mm31_outer_phase_pair import open_original, reconstruct
        from monster3b_actual_mmv31_hom_projector import row_span_coefficients
        m = json.loads(manifest.read_text())
        c = json.loads(cover.read_text())
        st, rows, piv, probes = open_original(plus,5)
        require(m.get("source_blob_sha")==c.get("original_source_blob_sha")==st.get("original_E_source_blob_sha")==SOURCE,
                "original E source mismatch")
        require(c.get("actual_mmgroup_used") is True and c.get("ATLAS_GF3_intertwiner",{}).get("form_transport_passed") is True,
                "actual cover chart missing")
        require(all(st.get(k) and st[k]==c.get(k) for k in ("canonical_C_word","canonical_D_word")),
                "original literal word mismatch")
        require(not st.get("derived_from_plus"),"positive original probe basis required")
        require(all(not any(c["canonical_"+g]["affine_ell_F3"]) for g in ("C","D")),
                "nonzero affine residual")
        V = MMV(P); z = MM(m["center_word"]); C = MM(c["canonical_C_word"])
        T = [MM(w) for w in m["translation_words"]]
        B = [MM(w) for w in m["modulation_words"]]
        require(len(T)==len(B)==6 and z.order()==3 and C.order()==4 and C*z*C**-1==z**-1,
                "wrong original group/centre words")
        require(all(g.order()==3 and g*z==z*g for g in T+B),"E axes must commute with centre and have order3")
        require(all(a*b==b*a for axes in (T,B) for a in axes for b in axes),
                "original polarization is not commuting")
        # Either sign convention for the Weyl generators is permitted, but
        # the full pairing matrix must be nondegenerate; no labels guessed.
        from monster3b_actual_mmv31_hom_projector import rank31
        pairing=[]
        for t in T:
            row=[]
            for b in B:
                q=next((i for i in range(3) if t*b*t**-1*b**-1==z**i),None)
                require(q is not None,"noncentral E commutator")
                row.append(q)
            pairing.append(row)
        # Exact F3 elimination (rank31 is NOT valid for this step).
        A=np.asarray(pairing,dtype=np.int64)%3
        for i in range(6):
            j=next((j for j in range(i,6) if A[j,i]),None)
            require(j is not None,"degenerate original E pairing")
            A[[i,j]]=A[[j,i]]
            A[i]=A[i]*int(A[i,i])%3
            for j in range(i+1,6): A[j]=(A[j]-A[j,i]*A[i])%3
        self.V,self.C,self.row_span=V,C,row_span_coefficients
        self.F=WeightFrame(lambda v,g:v*g,lambda v,w:v+w,lambda a,v:int(a)*v,
                           GF(P)(5),GF(P).one,z,T,B)
        vp,_=reconstruct(rows,piv,probes,5,V,z,B)
        self.basis={1:vp,2:[]};self.rows={1:rows,2:[]};self.piv={1:piv,2:[]}
        # Derived opposite phase, with exact source-vector echelon recovery.
        for v in vp:
            w=self.F.vacuum(v*C,2)
            r,coeff=self.row_span(w["E"],self.rows[2],self.piv[2])
            nz=np.flatnonzero(r)
            require(len(nz)>0,"opposite-phase source rank loss")
            j=int(nz[0]);fac=pow(int(r[j]),-1,P)
            for k,u in zip(coeff,self.basis[2]):
                if k:w=w-k*u
            w=fac*w;r=r*fac%P
            require(np.array_equal(np.asarray(w["E"],dtype=np.int16)%P,r),"opposite phase row replay")
            self.basis[2].append(w);self.rows[2].append(r);self.piv[2].append(j)
        require(len(self.basis[2])==90,"opposite phase rank")
        self.J={s:np.column_stack([self.coefficients(self.F.hom(v,s,s,C**2,GF(P).one),s)
                                   for v in self.basis[s]]) for s in (1,2)}
        for s in (1,2):
            J=self.J[s].astype(np.int64);I=np.eye(90,dtype=np.int64)
            require(np.array_equal(J@J%P,I) and rank31((I-J)%P)==12 and rank31((I+J)%P)==78,
                    "actual C2 constituent rank/sign mismatch")
        ambient=plus/"ambient_basis_rows_mod31.npz"
        if not ambient.is_file():ambient=plus/"ambient_basis_rows.npz"
        self.provenance={"manifest_sha256":sha(manifest),"cover_sha256":sha(cover),
                         "plus_ambient_sha256":sha(ambient),
                         "plus_status_sha256":sha(plus/"mmv31_hom_status.json"),
                         "pairing_F3":pairing}

    def coefficients(self,v,s):
        r,c=self.row_span(v["E"],self.rows[s],self.piv[s])
        require(not np.any(r),"nonzero original ambient recovery residual")
        return np.asarray(c,dtype=np.int64)%P

    def vector(self,c,s):
        require(np.asarray(c).shape==(90,),"wrong vacuum coordinates")
        v=self.V()
        for k,u in zip(c,self.basis[s]):
            if int(k)%P:v=v+(int(k)%P)*u
        return v

    def recover(self,v):
        zero=self.F.phase(v,0)
        parts={}
        for s in (1,2):
            a=np.stack([self.coefficients(self.F.recover_weight(v,s,x),s) for x in self.F.points])
            j=a@self.J[s].T%P
            parts[s]=((a-j)*pow(2,-1,P)%P,(a+j)*pow(2,-1,P)%P)
        return zero,parts

    def evaluate(self,zero,parts):
        require(zero==self.F.phase(zero,0),"not original centre-trivial sector")
        require(set(parts)=={1,2},"missing phase")
        v=zero
        for s in (1,2):
            a,b=(np.asarray(x,dtype=np.int64)%P for x in parts[s])
            require(a.shape==b.shape==(729,90),"wrong indexed constituent shape")
            require(np.array_equal(a@self.J[s].T%P,-a%P) and np.array_equal(b@self.J[s].T%P,b),
                    "wrong C2 constituent coordinates")
            for x,c in zip(self.F.points,(a+b)%P):
                if np.any(c):v=v+self.F.translate(self.vector(c,s),x)
        return v

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ("manifest","cover","plus","out"):p.add_argument("--"+name,type=Path,required=True)
    p.add_argument("--probe",type=int,default=17)
    a=p.parse_args()
    result={"status":"BLOCKED","actual_characteristic_zero":False}
    try:
        F=ActualFrame31(a.manifest,a.cover,a.plus)
        require(0<=a.probe<196884,"invalid original Conway probe")
        v=F.V("E",a.probe)+2*F.V("E",(a.probe+7919)%196884)
        # The probe is a genuine arbitrary original ambient linear combination.
        zero,parts=F.recover(v)
        require(F.evaluate(zero,parts)==v,"actual forward/reverse discrepancy")
        result.update(status="ACTUAL_MM31_LINEAR_FRAME_ROUNDTRIP",**F.provenance,
                      probe=a.probe,phase_weight_counts=[729,729],
                      actual_constituent_ranks=[12,78],centre_trivial_retained=True)
    except Exception as exc:
        result["error"]=repr(exc)
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(result,indent=2)+"\n")
    print(result)
    return 0 if result["status"]=="ACTUAL_MM31_LINEAR_FRAME_ROUNDTRIP" else 2

if __name__=="__main__":raise SystemExit(main())
