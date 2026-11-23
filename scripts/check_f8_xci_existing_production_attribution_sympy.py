"""F8 XCI — original LV/LVI production receipt curvature attribution.

Read the ACTUAL master-owned LVI compact receipt; preserve its provenance.
This is a source-grounded algebraic diagnostic, not another propagation.
All receiver algebra is EXACT SymPy rational arithmetic on receipt decimal
lexemes; the receipt itself is a compact transcription, not original NPZ.
No GitHub CI. No physical/Agda/TOE promotion.
"""
from pathlib import Path
import argparse,json
import sympy as S

KEYS=("H","E4","E5","E4t","E5t","lap","farE4","farE5")
ELL=(0,2,4)
T=S.Integer(12)

def rational(value):
    assert isinstance(value,(float,int)) and not isinstance(value,bool)
    return S.Rational(str(value))

def vectors(row,key):
    vals=row[key]
    assert isinstance(vals,list) and len(vals)==3
    return [rational(x) for x in vals]

def sumv(row,key):
    return sum(vectors(row,key),S.Integer(0))

def diff(a,b,key,i=None):
    if i is None:
        return sumv(b,key)-sumv(a,key)
    return vectors(b,key)[i]-vectors(a,key)[i]

def attribution(a,c,i=None):
    de4=diff(a,c,"E4",i)
    de5=diff(a,c,"E5",i)
    dL=diff(a,c,"lap",i)
    da=-4*T*T*de4-dL
    db=dL-T*T*(de5-2*de4)
    spatial=-dL/(4*T*T)
    acceleration=-da/(4*T*T)
    assert S.simplify(spatial+acceleration-de4)==0
    assert S.simplify((-(da+2*db-dL)/(2*T*T))-de5)==0
    return dict(delta_E4=float(de4),delta_E5=float(de5),
        delta_spatial_laplacian=float(dL),
        delta_temporal_acceleration= float(da),
        delta_H_eta=float(db),
        spatial_E4_contribution=float(spatial),
        acceleration_E4_contribution=float(acceleration),
        spatial_signed_share=float(spatial/de4) if de4 else None,
        acceleration_signed_share=float(acceleration/de4) if de4 else None)

def check(path):
    j=json.loads(Path(path).read_text())
    assert j["schema"]=="LVI-corrected-finite-refinement-compact-receipt"
    assert j["physical_acceptance"] is False
    assert "Transcribed from locally executed complete native JSON" in j["provenance"]
    assert j["multipoles"]==[0,2,4]
    assert j["geometry"]["normal_order"]==3
    assert j["geometry"]["intrinsic_4D_weyl_spatial_operator"]=="full_reconstructed_Delta3"
    rows=j["rows"]
    names=("coarse","medium","fine","factorial-A","factorial-B","factorial-C",
           "medium-dt-half","fine-dt-half")
    assert all(k in rows for k in names)
    for name in names:
        row=rows[name]
        for key in KEYS:
            vectors(row,key)
        assert int(row["steps_to_physical_receiver"])>0
        assert len(row["requested_dr_dy_dt"])==3
    A,B,C,D=(rows[k] for k in ("factorial-A","factorial-B","factorial-C","fine"))
    assert rows["factorial-A"]["requested_dr_dy_dt"]==[.008,.012,.0012]
    assert rows["factorial-B"]["requested_dr_dy_dt"]==[.008,.009,.0012]
    assert rows["factorial-C"]["requested_dr_dy_dt"]==[.006,.012,.0012]
    assert D["requested_dr_dy_dt"]==[.006,.009,.0012]
    ratios={}
    factorial={}
    for key in KEYS:
        ar,an,interaction,total=(diff(A,C,key),
            diff(A,B,key),diff(B,D,key)-diff(A,C,key),diff(A,D,key))
        assert S.simplify(ar+an+interaction-total)==0
        factorial[key]=dict(radial=float(ar),normal=float(an),
            interaction=float(interaction),total=float(total))
    radial={"total":attribution(A,C)}
    for i,ell in enumerate(ELL): radial[str(ell)]=attribution(A,C,i)
    for metric in ("E4","E5","E4t","E5t"):
        assert abs(sum(radial[str(ell)]["delta_"+metric] for ell in ELL)
                   -factorial[metric]["radial"])<1e-14 if metric in ("E4","E5") else True
    time_pairs={}
    for name,first,last in (("medium","medium","medium-dt-half"),
                             ("fine","fine","fine-dt-half")):
        time_pairs[name]={key:float(diff(rows[first],rows[last],key))
                          for key in ("E4","E5","H","lap","farE4")}
    return dict(status="PASS",source_receipt=str(path),
        original_production_solver_blob=j["solver_blob"],
        compact_not_full_production_json=True,
        physical_acceptance=False,
        factorial=factorial,radial_receipt_attribution=radial,
        temporal_controls=time_pairs,
        observed_radial_to_fine_time_E4_ratio=float(
            abs(S.Rational(str(factorial["E4"]["radial"]))/
                S.Rational(str(time_pairs["fine"]["E4"])))),
        scope="Exact algebra conditional on compact original native receipt; no independent field-jet observations, numerical convergence or production rerun")

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--receipt",default=str(Path(__file__).resolve().parents[1]/
       "Artifacts/ksw668/ads5_f8_LVI_corrected_refinement_compact_20261120.json"))
    args=p.parse_args()
    print(json.dumps(check(args.receipt),indent=2))
