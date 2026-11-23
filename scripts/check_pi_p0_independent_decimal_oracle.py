#!/usr/bin/env python3
"""Independent decimal-oracle lane for Paper 9 COMP5j.

This compares the exact-source, compiled GMP certificate's SHA256 with an
independent high-precision mpmath π computation. Both are implementations;
agreement is a cross-engine regression, not an analytic identity proof.
"""
import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/"scripts/check_pi_p0_power5_dyadic_certificate.cpp"
SOURCE_BLOB="be8e746a5c73ed2ec212664b68e5eceacc4420e7"
def run(argv,timeout=90):
 return subprocess.run(argv,cwd=ROOT,text=True,capture_output=True,
                       check=True,timeout=timeout).stdout
def main():
 ap=argparse.ArgumentParser()
 ap.add_argument("--digits",nargs="+",type=int,default=[100,1000,10000])
 ap.add_argument("--out",type=Path)
 args=ap.parse_args()
 if any(x<1 or x>10000 for x in args.digits):ap.error("oracle precision must be 1..10000")
 try:
  import mpmath
 except ImportError as e:
  raise SystemExit("Independent cross-engine lane needs mpmath: "+str(e))
 git_blob=run(["git","hash-object",str(SOURCE)],10).strip()
 if git_blob!=SOURCE_BLOB:raise RuntimeError("COMP5j source Git blob changed: "+git_blob)
 results=[]
 with tempfile.TemporaryDirectory(prefix="pi-independent-") as tmp:
  binary=str(Path(tmp)/"pi")
  run(["g++","-std=c++17","-O3",str(SOURCE),
       "-lgmpxx","-lgmp","-lcrypto","-o",binary],120)
  for d in args.digits:
   mpmath.mp.dps=d+40
   # Take d+1 decimal digits (leading '3' + d fractional digits)
   string=mpmath.nstr(mpmath.pi,d+39)
   digits=string.replace(".","")[:d+1]
   if len(digits)!=d+1 or not digits.startswith("314159"):
    raise AssertionError("independent decimal oracle precision unavailable")
   oracle_hash=hashlib.sha256(digits.encode("ascii")).hexdigest()
   out=run([binary,str(d),"inplace","1"],120)
   lines=[x for x in out.splitlines() if x.startswith("FIBRE ")]
   if len(lines)!=1:raise AssertionError("missing certificate receipt")
   fields=dict(v.split("=",1) for v in lines[0].split()[1:] if "=" in v)
   if fields.get("output_hash")!=oracle_hash:raise AssertionError("independent pi disagreement: "+str(d))
   if int(fields.get("digits","0"))!=d:raise AssertionError("precision mismatch")
   results.append({"digits":d,"sha256":oracle_hash,"status":"CROSS_ENGINE_PARITY",
      "independent_analytic_pi_theorem_proved":False})
 result={"schema":"paper9-pi-independent-mpmath-cross-engine-v1",
   "source_git_blob":git_blob,"oracle":"mpmath.pi with 40-digit guard",
   "results":results,"bishop_same_real_proved":False,
   "external_sota_compared":False}
 if args.out:args.out.write_text(json.dumps(result,indent=2)+"\n")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()
