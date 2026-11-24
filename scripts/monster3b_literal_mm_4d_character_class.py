#!/usr/bin/env python3
"""Identify the LITERAL corrected Monster Hit0 C class, without Magma.

The original GAP main->MN3B->Monster class fusion chose source 4D.
That is NOT a proof the user's corrected MM word C is 4D.

mmgroup.MM.chi_powers() can compute the genuine 196883D Monster
character of actual group words whose half-order power is 2B.
Here the original canonical MM C has order 4; compare its chi(C),
chi(C²), and order against every ORIGINAL Monster class in the
GAP CTblLib table. Declare C=4D only for a unique original table row
at SOURCE position 10, with printed class label 4D.

Usage:
 python3 scripts/monster3b_literal_mm_4d_character_class.py \
   --cover build/monster3b-p5-endpoint/run-.../mmgroup_canonical_cover_hit0.json \
   --outdir build/monster3b-p5-endpoint/class4d

Requires existing original mmgroup 1.0.8 and GAP+CTblLib, but not Magma,
not Steel matrices, and no 196884-dimensional trace scan.

The partial receipt survives if chi_powers probabilistically fails.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import traceback

SOURCE_MONSTER_4D_CLASS_POSITION=10
def gap_source(trace,trace2,output):
    def filterpart(e, power):
        return "" if e is None else (
            " and chi[j]="+str(e) if power==1 else
            " and chi[pow2[j]]="+str(e))
    conditions="ord[j]=4"+filterpart(trace,1)+filterpart(trace2,2)
    path=json.dumps(str(output.resolve()))
    return fr'''if LoadPackage("ctbllib") <> true then Error("CTblLib required"); fi;
m:=CharacterTable("M");;
ord:=OrdersClassRepresentatives(m);;
classes:=ClassNames(m);;
pow2:=PowerMap(m,2);;
irr:=Irr(m);;
rows:=Filtered([1..Length(irr)],i->irr[i][1]=196883);;
if Length(rows) <> 1 then Error("no unique genuine Monster 196883 ordinary row"); fi;
chi:=irr[rows[1]];;
if classes[10] <> "4D" or ord[10] <> 4 then
 Error("original source Monster class 10 not labelled 4D");
fi;
candidates:=Filtered([1..NrConjugacyClasses(m)],
    j->{conditions});;
AsList := function(xs)
 local out,i;
 out:="[";
 for i in [1..Length(xs)] do
  if i>1 then Append(out,",");fi;
  Append(out,String(xs[i]));
 od;
 Append(out,"]");return out;
end;
labels:=List(candidates,j->classes[j]);;
lit:=Length(candidates)=1 and candidates[1]=10;;
out:=Concatenation(
 "{{\\"schema\\":\\"monster3b-literal-MM-C-196883-character-class-v1\\",",
 "\\"source_monster_4D_position\\":10,",
 "\\"source_4D_reference_character\\":",String(chi[10]),",",
 "\\"source_4D_reference_square_character\\":",String(chi[pow2[10]]),",",
 "\\"source_4D_reference_square_class\\":\\"",classes[pow2[10]],"\\",",
 "\\"candidates\\":",AsList(candidates),",",
 "\\"candidate_labels\\":[");
for j in [1..Length(labels)] do
 if j>1 then Append(out,","); fi;
 Append(out,"\\"",labels[j],"\\"");
od;
Append(out,"],\\"literal_MM_C_is_4D\\":");
if lit then Append(out,"true");else Append(out,"false");fi;
Append(out,"}}");
PrintTo({path},out);
if Length(candidates)=0 then
 Error("original MM class fingerprint matches no Monster class");
fi;
Print("MONSTER3B_LITERAL_MM_C_4D_SOURCE_RESULT",lit,"\\n");
QUIT;
'''
def compute_cover(cover):
    from mmgroup import MM
    if not isinstance(cover,dict) or cover.get("actual_mmgroup_used") is not True:
        raise ValueError("original source actual-mmgroup receipt is mandatory")
    word=cover.get("canonical_C_word")
    if not isinstance(word,str) or not word.startswith("M<"):
        raise ValueError("missing canonical FULL MM element word")
    c=MM(word)
    if c.order()!=4:raise ValueError("corrected Monster C not exact order4")
    if cover.get("canonical_C",{}).get("central_multiplier_mod3")!=2:
        raise ValueError("C does not invert original 3B centre")
    try:
        order,chars,h=c.chi_powers(ntrials=180)
        if order!=4:raise ValueError("MM character order mismatch")
        char1=chars.get(1)
        char2=chars.get(2)
        return {"status":"MM_CHARACTER_COMPUTED" if char1 is not None else
            "MM_CHARACTER_PARTIAL",
            "source":"actual corrected Monster MM word from canonical cover",
            "C_word":word,"actual_C_order":order,
            "character_196883_C":int(char1) if char1 is not None else None,
            "character_196883_C2":int(char2) if char2 is not None else None,
            "mmgroup_chi_powers_success":char1 is not None,
            "source_monster_4D_position":SOURCE_MONSTER_4D_CLASS_POSITION,
            "original_MM_C_4D_confirmed":False}
    except Exception as exc:
        return {"status":"MM_CHARACTER_NOT_AVAILABLE",
            "error":repr(exc),"C_word":word,"actual_C_order":4,
            "character_196883_C":None,"character_196883_C2":None,
            "original_MM_C_4D_confirmed":False}
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--cover",type=Path,required=True)
    ap.add_argument("--outdir",type=Path,default=Path(
        ".dashi/monster3b-mmgroup/literal-C-4D"))
    ap.add_argument("--timeout",type=int,default=900)
    ap.add_argument("--skip-gap",action="store_true")
    a=ap.parse_args()
    a.outdir.mkdir(parents=True,exist_ok=True)
    rec=a.outdir/"literal_MM_C_4D_status.json"
    try:
        data=json.loads(a.cover.read_text())
        output=compute_cover(data)
        if output["character_196883_C"] is not None:
            source=a.outdir/"stage_literal_C_Monster_character.g"
            expected=a.outdir/"literal_MM_C_GAP_source_class.json"
            source.write_text(gap_source(
                output["character_196883_C"],
                output["character_196883_C2"],expected))
            output["GAP_source_stage"]=str(source)
            if a.skip_gap:
                output["status"]="GAP_CLASS_MATCH_STAGED"
            else:
                gap=shutil.which("gap")
                if gap is None:
                    output["status"]="GAP_EXECUTABLE_UNAVAILABLE"
                else:
                    cp=subprocess.run([gap,"-q",str(source)],timeout=a.timeout,
                        stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                        text=True,errors="replace",check=False)
                    (a.outdir/"literal_MM_C_GAP.log").write_text(cp.stdout)
                    if cp.returncode==0 and expected.is_file():
                        match=json.loads(expected.read_text())
                        output["original_Monster_GAP_character_class"]=match
                        output["original_MM_C_4D_confirmed"]=(
                            match["literal_MM_C_is_4D"] is True)
                        output["status"]=(
                            "ACTUAL_MM_C_CLASS_4D_EXACT"
                            if output["original_MM_C_4D_confirmed"]
                            else "ACTUAL_MM_C_NOT_4D_OR_AMBIGUOUS")
                    else:
                        output["status"]="GAP_CHARACTER_CLASS_MATCH_FAILED"
                        output["GAP_output_tail"]=cp.stdout[-2000:]
    except Exception as exc:
        output={"status":"ERROR","error":repr(exc),
            "traceback":traceback.format_exc(limit=5),
            "original_MM_C_4D_confirmed":False}
    rec.write_text(json.dumps(output,indent=2,sort_keys=True)+"\n")
    print(json.dumps({k:output.get(k) for k in ("status",
        "actual_C_order","character_196883_C",
        "character_196883_C2","original_MM_C_4D_confirmed")},indent=2))
    print("RECEIPT:",rec)
    # Nonunique, or probabilistically missing, is an HONEST open endpoint,
    # not a fabricated source class match.
    return 2 if output["status"] in ("ERROR",
             "GAP_CHARACTER_CLASS_MATCH_FAILED") else 0
if __name__=="__main__": raise SystemExit(main())
