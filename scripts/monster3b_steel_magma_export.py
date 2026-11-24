#!/usr/bin/env python3
"""L10A: generate/run an actual Magma exporter for Steel's 6.Suz G-module.

Unlike parsing Magma representation text with regexes, this uses Magma's
documented Group(M), Representation(M), and the exact number-field Eltseq
basis. No guessed generator matrix and no GF3-to-C lift is ever used.

The Steel source must already have been downloaded with
  python3 scripts/monster3b_steel_ordinary12_to90.py --acquire

Run:
  python3 scripts/monster3b_steel_magma_export.py --magma --module M
Or omit --magma to inspect the staged original-source exporter before run.
If Steel's original file defines a different GModule variable, give --module
the literal original symbol; the original source file is never rewritten.

All output is fail-closed and labels original GAP Irr orientation UNPAID.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

SOURCE_URL="https://magma.maths.usyd.edu.au/~allan/reps/db/d12.6Suz.nfdeg2.M"
SOURCE_DEFAULT=Path(".dashi/monster3b-steel-ordinary12/d12.6Suz.nfdeg2.M")
OUT_DEFAULT=Path(".dashi/monster3b-steel-ordinary12")
SCHEMA="monster3b-steel6suz-ordinary12-v1"
def magma_quote(x):
    s=str(x)
    if "\n" in s or "\r" in s or '"' in s or "\\" in s:
        raise ValueError("unsafe Magma quoted filename; use a simple local directory")
    return '"'+s+'"'
def build_code(source,output,module,sha):
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*",module):
        raise ValueError("invalid module identifier")
    # The genuine source is evaluated by Magma, never translated or evaluated
    # as Python; the group and representation homomorphism come from the
    # ORIGINAL GModule, not a manually recreated group.
    return r"""
SetQuitOnError(true);
Read(SOURCEFILE);
Monster3BOriginalModule := MODNAME;
Monster3BOriginalGroup := Group(Monster3BOriginalModule);
Monster3BRho := Representation(Monster3BOriginalModule);
Monster3BGenerators := [
  Monster3BRho(Monster3BOriginalGroup.i)
    : i in [1..Ngens(Monster3BOriginalGroup)] ];
if #Monster3BGenerators lt 1 then
  error "Original Steel module has no source generators";
end if;
if Nrows(Monster3BGenerators[1]) ne 12 then
  error "Steel original GModule is not degree12";
end if;
Monster3BK := BaseRing(Monster3BGenerators[1]);
if Degree(Monster3BK) ne 2 then
  error "Steel representation field is not quadratic";
end if;
Monster3BR<x> := PolynomialRing(Monster3BK);
Monster3BZroots := Roots(x^2+x+1);
if #Monster3BZroots ne 2 then
  error "Original number field has no two primitive cube roots";
end if;
Monster3BZeta := Monster3BZroots[1][1];
// The Magma root ordering selects one marked orientation; it is NOT
// yet the actual Monster z versus z^-1 orientation.
Monster3BZcoords := Eltseq(Monster3BZeta);
if #Monster3BZcoords ne 2 or Monster3BZcoords[2] eq 0 then
  error "Nonprimitive ζ3 number-field basis";
end if;
Monster3BPair := function(q)
  e := Eltseq(Monster3BK!q);
  if #e eq 1 then Append(~e, Rationals()!0); end if;
  if #e ne 2 then error "Unexpected quadratic element coordinates"; end if;
  b := Rationals()!(e[2]/Monster3BZcoords[2]);
  a := Rationals()!(e[1]-b*Monster3BZcoords[1]);
  if a+Monster3BK!b*Monster3BZeta ne q then
    error "Exact number-field to ζ3 basis conversion failed";
  end if;
  return "[\"" cat Sprint(a) cat "\",\"" cat Sprint(b) cat "\"]";
end function;
Monster3BMatrixJSON := function(A)
  s := "[";
  for i in [1..Nrows(A)] do
    if i gt 1 then s cat:= ","; end if;
    s cat:= "[";
    for j in [1..Ncols(A)] do
      if j gt 1 then s cat:= ","; end if;
      s cat:= Monster3BPair(A[i,j]);
    end for;
    s cat:= "]";
  end for;
  return s cat "]";
end function;
Monster3BOut := "{\n";
Monster3BOut cat:= " \"schema\":\"monster3b-steel6suz-ordinary12-v1\",\n";
Monster3BOut cat:= " \"source\":{\"url\":\"SOURCEURL\",";
Monster3BOut cat:= "\"sha256\":\"SOURCESHA\"},\n";
Monster3BOut cat:= " \"field_polynomial\":[1,1,1],\n";
Monster3BOut cat:= " \"matrix_convention\":\"left_action_column_vectors\",\n";
Monster3BOut cat:= " \"selected_6Suz_12_irr_position\":null,\n";
Monster3BOut cat:= " \"ordinary_source_character_orientation_verified\":false,\n";
Monster3BOut cat:= " \"original_generator_to_ATLAS_standard_words_verified\":false,\n";
Monster3BOut cat:= " \"magma_GModule_symbol\":\"MODNAME\",\n";
Monster3BOut cat:= " \"magma_primitive_cube_root_coordinates\":[";
Monster3BOut cat:= Monster3BPair(Monster3BZeta) cat:= "],\n";
Monster3BOut cat:= " \"generators\":{\n";
for i in [1..#Monster3BGenerators] do
  if i gt 1 then Monster3BOut cat:= ",\n"; end if;
  Monster3BOut cat:= "  \"G." cat Sprint(i) cat "\":";
  Monster3BOut cat:= Monster3BMatrixJSON(Monster3BGenerators[i]);
end for;
Monster3BOut cat:= "\n }\n}\n";
PrintFile(OUTPUTFILE,Monster3BOut:Overwrite:=true);
print "MONSTER3B_STEEL_ORIGINAL_GMODULE_EXPORTED",#Monster3BGenerators;
QUIT;
""".replace("SOURCEFILE",magma_quote(source)).replace("OUTPUTFILE",magma_quote(output)).replace("MODNAME",module).replace("SOURCEURL",SOURCE_URL).replace("SOURCESHA",sha)
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source",type=Path,default=SOURCE_DEFAULT)
    p.add_argument("--outdir",type=Path,default=OUT_DEFAULT)
    p.add_argument("--module",default="M",help="original Steel GModule symbol (default M)")
    p.add_argument("--magma",action="store_true",help="explicitly execute downloaded Magma source")
    p.add_argument("--timeout",type=int,default=900)
    args=p.parse_args()
    if args.timeout<1: p.error("timeout must be >0")
    src=args.source.resolve()
    if not src.is_file(): p.error("original Steel .M source missing; run --acquire first")
    b=src.read_bytes(); b.decode("utf-8")
    digest=hashlib.sha256(b).hexdigest()
    args.outdir.mkdir(parents=True,exist_ok=True)
    outdir=args.outdir.resolve()
    out=outdir/"steel12_source_generators.json"
    stage=outdir/"stage_steel12_export.m"
    script=build_code(src,out,args.module,digest)
    stage.write_text(script,encoding="utf-8")
    receipt={"status":"STAGED_ONLY","steel_original_source_sha256":digest,
        "module_symbol":args.module,"source":str(src),"staged_magma":str(stage),
        "output_json":str(out),"actual_GAP_character_orientation_verified":False,
        "actual_Monster_word_to_6Suz_verified":False}
    if args.magma:
        exe=shutil.which("magma")
        if not exe: p.error("Magma not found on PATH")
        try:
            cp=subprocess.run([exe,str(stage)],stdout=subprocess.PIPE,
                 stderr=subprocess.STDOUT,text=True,errors="replace",
                 timeout=args.timeout,check=False)
            (outdir/"magma_steel12_export.log").write_text(cp.stdout)
            if cp.returncode!=0 or not out.is_file():
                raise RuntimeError(f"Magma source failed; exit={cp.returncode}, see log")
            packet=json.loads(out.read_text())
            if (packet.get("schema")!=SCHEMA or
                packet.get("source",{}).get("sha256")!=digest or
                not packet.get("generators")):
                raise ValueError("Magma original-source output schema/provenance mismatch")
            receipt["status"]="ORIGINAL_STEEL_GMODULE_EXPORTED"
            receipt["generator_names"]=list(packet["generators"])
        except Exception as exc:
            receipt["status"]="ERROR"
            receipt["error"]=repr(exc)
    report=outdir/"steel12_magma_export_status.json"
    report.write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print(json.dumps(receipt,indent=2))
    return 0 if receipt["status"]!="ERROR" else 2
if __name__=="__main__": raise SystemExit(main())
