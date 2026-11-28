#!/usr/bin/env python3
"""Paper 9 P0: source-byte stable GMP backend acceptance and timing ledger.

Run from the repository root: python3 scripts/check_pi_p0_consolidated_acceptance.py
Use --million to include one million places (the cross-GCD four-mode benchmark
has a substantial cost); --output to retain a machine-readable local receipt.
Compiles exact repository source bytes, checks known exact decimal-output hashes,
and never claims external SOTA or Bishop same-real closure.
"""
import argparse
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
SOURCES={
 "quotient":"scripts/check_pi_gmp_quotient_residual.cpp",
 "reuse":"scripts/check_pi_gmp_codec_memory.cpp",
}
SOURCE_GIT_BLOBS={
 "quotient":"28f4657e5bdbfc27ebb7cc3690f6144590ba2d5e",
 "reuse":"82027bc7acee4b4711f0ca1a2ed42dce1d60b8c5",
}
EXPECTED={
 10000:"ab03bf7037718e1525340a0c43f0049ddbe99c6067ad3e08a4de5c591fedc524",
 100000:"79b862cc31ceb97bb3c39d05ae74664c99f0ff7670b3e08a4b21a31ef84d7711",
 500000:"fe727f5894e072423c570402dd3948bef1f318ea957498aab06a95351e1018f9",
 1000000:"130203eb055a962b8441af76c22b75627ec18c672a485904e567f59251e8ee18",
 5000000:"09eb526274ac828a3a54614e72fac5baa8ab6b26b8484fe1b065f678b2c8dbad",
 10000000:"ae9c137083802006c204e6683c28c6727a862103d703b5e0d79a22ddaa201999",
}
def command(argv,timeout):
 return subprocess.run(argv,cwd=ROOT,capture_output=True,text=True,check=True,timeout=timeout)
def run(include_million=False,include_large=False,output=None):
 digits=[10000,100000]
 if include_million:digits.extend([500000,1000000])
 if include_large:digits.extend([5000000,10000000])
 result={"schema":"dashi.paper9.pi-p0-consolidated-gmp-v1",
         "premises":"Classical Chudnovsky analytic identity and signed alternating enclosure are external",
         "bishop_same_real_paid":False,"external_sota_compared":False,
         "compiled_original_source_git_blob_checked":{},
         "benchmarks":[]}
 with tempfile.TemporaryDirectory(prefix="pi-p0-") as folder:
  binaries={}
  for name,path in SOURCES.items():
   git_blob=command(["git","hash-object",path],10).stdout.strip()
   if git_blob!=SOURCE_GIT_BLOBS[name]:
    raise AssertionError(f"source blob changed: {path} {git_blob}")
   binary=str(Path(folder)/name)
   command(["g++","-std=c++17","-O3","-Wall","-Wextra","-pedantic",path,
            "-lgmpxx","-lgmp","-lcrypto","-o",binary],120)
   result["compiled_original_source_git_blob_checked"][name]=git_blob
   binaries[name]=binary
  for d in digits:
   # Rotating order of the two independently compiled original backends.
   for name in (["reuse"] if d>=5000000 else (["quotient","reuse"] if d%3 else ["reuse","quotient"])):
    args=[binaries[name],str(d),"3"] if name=="quotient" else [binaries[name],str(d),"inplace","3"]
    output_text=command(args,180).stdout
    rows=[line for line in output_text.splitlines() if line.startswith(("BENCH ","SUMMARY "))]
    if not rows:raise AssertionError("no benchmark result")
    for row in rows:
     m=re.search(r"(?:sha=|hash=)([0-9a-f]{64})",row)
     if not m or m.group(1)!=EXPECTED[d]:
      raise AssertionError(f"certificate regression at {d}: {row}")
     result["benchmarks"].append(dict(digits=d,backend=name,summary=row,
         exact_output_hash_matches_prior_receipt=True))
 if output:
  Path(output).write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
 return result

if __name__=="__main__":
 ap=argparse.ArgumentParser()
 ap.add_argument("--million",action="store_true")
 ap.add_argument("--large",action="store_true",help="5M and 10M; use only in-place GMP for bounded runtime")
 ap.add_argument("--output",type=Path)
 args=ap.parse_args()
 print(json.dumps(run(args.million,args.large,args.output),indent=2,sort_keys=True))
