#!/usr/bin/env python3
"""Recover the literal standard D from a saved genuine cover, no E search.
Keep the original D and Q^7 residual, not just its chosen representative.
"""
import argparse, hashlib, json
from pathlib import Path

SOURCE="c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2"
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def require(b,msg):
    if not b:raise ValueError(msg)
def run(manifest,cover):
    from mmgroup import MM
    m,c=read(manifest),read(cover)
    require(c.get("actual_mmgroup_used") is True and
            m.get("source_blob_sha")==c.get("original_source_blob_sha")==SOURCE,
            "original source mismatch")
    att=c.get("ATLAS_GF3_intertwiner",{})
    require(att.get("form_transport_passed") is True and
            att.get("intertwiner_dimension")==1,"original quotient chart absent")
    require(all(not any(c["canonical_"+g]["affine_ell_F3"]) for g in ("C","D")),
            "nonzero affine defect")
    C,D,z=map(MM,(c["canonical_C_word"],c["canonical_D_word"],m["center_word"]))
    I=z**0
    def Q(d):return C*d*C*d*d
    def R(d):
        letters={"c":C**-1,"d":d**-1}
        a=I
        for x in "cdcdcddcdd":a=a*letters[x]
        return a
    require(z.order()==3 and C*z*C**-1==z**-1 and D*z==z*D,"signed centre")
    u=Q(D)**7
    q=next((i for i in range(3) if u==z**i),None)
    require(q is not None,"Q7 outside original central C3")
    if "ATLAS_Q7" in c["central_cover_relators"]:
        require(c["central_cover_relators"]["ATLAS_Q7"]["central_z_power"]==q,
                "stored Q7 differs from actual word")
    d=u**-1*D
    checks={"original_R7":R(D)**7==z,"C4":C**4==I and C**2!=I,
            "standard_D3":d**3==I and d!=I,"standard_CD56":(C*d)**56==I,
            "standard_C2_CD28":C**2==(C*d)**28,
            "standard_Q7":Q(d)**7==I and Q(d)!=I,
            "standard_R7":R(d)**7==z,"reverse_original_D":u*d==D,
            "central_rephase_commutes_E":all(u*MM(w)==MM(w)*u for w in
                         m["translation_words"]+m["modulation_words"])}
    require(all(checks.values()),"standard cover relation failure "+str(checks))
    # Literal source wheel, retain any central order defect. The word
    # itself must be executed, not inferred from an ordinary source matrix.
    e=C*D*C**-1
    letters={"D":D,"E":e,"d":D**-1,"e":e**-1}
    w=I
    for letter in "DEdeDeDEDEdedEd":w=w*letters[letter]
    g=w**3
    defect=g**13
    k=next((j for j in range(3) if defect==z**j),None)
    require(k is not None and g*z==z*g,"literal wheel has noncentral order defect")
    g13=defect**-1*g
    require(g13**13==I and g13!=I and defect*g13==g,"literal order13 correction")
    return {"status":"LITERAL_MM_STANDARD_D_PHASE_RECOVERED",
            "actual_mmgroup_used":True,"manifest_sha256":digest(manifest),
            "cover_sha256":digest(cover),"original_source_blob_sha":SOURCE,
            "canonical_C_word":str(C),"canonical_D_word":str(D),
            "standard_D_word":str(d),"Q7_word":str(u),"Q7_central_z_power":q,
            "standard_Q_word":str(Q(d)),"checks":checks,
            "literal_wheel_word":str(g),"literal_wheel_13_defect_word":str(defect),
            "literal_wheel_13_defect_z_power":k,"literal_order13_word":str(g13),
            "raw_wheel_has_order13":k==0,
            "characteristic_zero_numeric_Hom_extracted":False}
def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ("manifest","cover","out"):p.add_argument("--"+name,type=Path,required=True)
    a=p.parse_args();a.out.parent.mkdir(parents=True,exist_ok=True)
    try:r=run(a.manifest,a.cover)
    except Exception as exc:r={"status":"BLOCKED_OR_SOURCE_RESIDUAL","error":repr(exc)}
    a.out.write_text(json.dumps(r,indent=2)+"\n");print(json.dumps(r))
    return 0 if r["status"]=="LITERAL_MM_STANDARD_D_PHASE_RECOVERED" else 2
if __name__=="__main__":raise SystemExit(main())
