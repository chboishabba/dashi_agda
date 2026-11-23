#!/usr/bin/env python3
"""Paper 9 P0: actual GMP allocator / path-fibre Pareto ledger.

Compiles exactly the committed instrumented C++ source. Captures independent
processes, not multiple in-process runs (their high-water RSS persists). A
Linux /proc/self/status VmHWM is the preferred process RSS; ru_maxrss can
inherit a parent high-water on fork/exec. GMP hooks count only GMP-managed
memory, excluding host heap, OpenSSL and allocator internal overhead.
The classical Chudnovsky identity and alternating tail are external premises.
"""
import argparse
import hashlib
import json
import re
import statistics
import subprocess
import tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
SOURCES={
 "retained":(ROOT/"scripts/check_pi_p0_fibre_cost_profile.cpp","078e76a0dbc603e89ac108f3d171764d4a66f247"),
 "released":(ROOT/"scripts/check_pi_p0_endpoint_lifetime.cpp","8ff286c6ec9ab23fe0d18c7d2833e1645c465b7a"),
 "scoped":(ROOT/"scripts/check_pi_p0_endpoint_scoped.cpp","4542c2a3e659c4620536a45d8df39c4cfa24e23e"),
 "shifted":(ROOT/"scripts/check_pi_p0_dyadic_quotient_shift.cpp","a8dae0366863d9d950aa8b5bd524b3503af960ed"),
}
EXPECTED={
 10000:"ab03bf7037718e1525340a0c43f0049ddbe99c6067ad3e08a4de5c591fedc524",
 100000:"79b862cc31ceb97bb3c39d05ae74664c99f0ff7670b3e08a4b21a31ef84d7711",
 500000:"fe727f5894e072423c570402dd3948bef1f318ea957498aab06a95351e1018f9",
 1000000:"130203eb055a962b8441af76c22b75627ec18c672a485904e567f59251e8ee18",
 5000000:"09eb526274ac828a3a54614e72fac5baa8ab6b26b8484fe1b065f678b2c8dbad",
 10000000:"ae9c137083802006c204e6683c28c6727a862103d703b5e0d79a22ddaa201999",
}
INTEGER_FIELDS=(
 "digits","leaf_count","merge_count","ordered_products","ordered_adds",
 "max_operand_bits","max_result_bits","max_depth",
 "peak_explicit_carrier_capacity_bytes","final_carrier_capacity_bytes",
 "endpoint_explicit_capacity_bytes","gmp_peak_live_bytes",
 "gmp_live_bytes_after_compute","gmp_alloc_calls",
 "gmp_realloc_calls","gmp_free_calls",
 "gmp_total_requested_bytes","gmp_reallocated_old_bytes",
)
def run(argv,timeout=180,cwd=None):
 return subprocess.run(argv,cwd=cwd,check=True,capture_output=True,text=True,
                       timeout=timeout).stdout

def parse(stdout,digits,mode):
 lines=stdout.splitlines()
 fibre=[line for line in lines if line.startswith("FIBRE ")]
 summary=[line for line in lines if line.startswith("SUMMARY ")]
 if len(fibre)!=1 or len(summary)!=1:
  raise AssertionError("expected exactly one fibre and one summary row")
 def words(line):return dict(token.split("=",1) for token in line.split()[1:] if "=" in token)
 data=words(fibre[0]); summ=words(summary[0])
 for field in INTEGER_FIELDS:data[field]=int(data[field])
 data["schoolbook_bitpair_proxy"]=int(data["schoolbook_bitpair_proxy"])
 data["median_ms"]=float(summ["median_ms"])
 data["proc_vmhwm_kib"]=int(summ.get("proc_vmhwm_kib","0"))
 data["raw_ru_maxrss_kib"]=int(summ["peak_rss_kib"])
 data["hash"]=data["output_hash"]
 if data["mode"]!=mode or data["digits"]!=digits or data["hash"]!=EXPECTED[digits]:
  raise AssertionError("source/output identity mismatch")
 if data["leaf_count"]!=data["merge_count"]+1:
  raise AssertionError("not a full binary split")
 if data["ordered_products"]!=4*data["merge_count"] or data["ordered_adds"]!=data["merge_count"]:
  raise AssertionError("PQT merge work not counted exactly")
 if data["gmp_peak_live_bytes"]<=0 or data["gmp_alloc_calls"]==0:
  raise AssertionError("GMP allocation hooks not running")
 if data["gmp_peak_live_bytes"]<data["final_carrier_capacity_bytes"]:
  raise AssertionError("carrier capacity exceeds GMP heap high water")
 if data["proc_vmhwm_kib"]<=0:
  raise AssertionError("Linux process-image VmHWM missing")
 if data["measured_GMP_total_live_heap"]!="true" or data["model_is_upper_bound"]!="false":
  raise AssertionError("source lost its conservative model boundary")
 return data

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument("--digits",type=int,nargs="+",default=[10000,100000])
 ap.add_argument("--reps",type=int,default=3)
 ap.add_argument("--out",type=Path)
 args=ap.parse_args()
 if args.reps<1 or args.reps%2==0:ap.error("--reps must be positive and odd")
 if any(d not in EXPECTED for d in args.digits):ap.error("unknown certified precision")
 blobs={}
 for name,(source,expected) in SOURCES.items():
  blob=run(["git","hash-object",str(source)],cwd=ROOT).strip()
  if blob!=expected:raise AssertionError("committed C++ bytes moved: "+str(source)+" "+blob)
  blobs[name]=blob
 report=dict(schema="paper9-pi-p0-cost-fibre-allocator-ledger-v1",
  exact_source_git_blobs=blobs,
  premises="classical Chudnovsky identity and alternating tail",
  certification="original GMP exact decimal floor + SHA256 output regressions",
  formal_agda_kernel_checked=False,external_sota_compared=False,
  gmp_heap_hooks_capture_non_gmp_memory=False,
  peak_explicit_carrier_model_is_heap_upper_bound=False,
  source_pinned=True,samples=[],by_precision={})
 with tempfile.TemporaryDirectory(prefix="pi-p0-fibre-") as folder:
  binaries={}
  for name,(source,_) in SOURCES.items():
   binary=str(Path(folder)/("pi-fibre-"+name))
   run(["g++","-O3","-std=c++17","-Wall","-Wextra","-pedantic",str(source),
        "-lgmpxx","-lgmp","-lcrypto","-o",binary],timeout=120,cwd=ROOT)
   binaries[name]=binary
  for d in args.digits:
   modes=["baseline","inplace","released","scoped","shifted"]
   records={name:[] for name in modes}
   for i in range(args.reps):
    for name in (modes[i%3:]+modes[:i%3]):
     variant=name if name in ("released","scoped","shifted") else "retained"
     argmode="baseline" if name=="baseline" else "inplace"
     row=parse(run([binaries[variant],str(d),argmode,"1"]),d,argmode)
     row["implementation"]=name
     row["rotation"]=i;records[name].append(row);report["samples"].append(row)
   profile={}
   for mode,rs in records.items():
    profile[mode]={name:statistics.median(x[name] for x in rs)
     for name in ("median_ms","proc_vmhwm_kib","gmp_peak_live_bytes",
       "peak_explicit_carrier_capacity_bytes","gmp_alloc_calls",
       "gmp_realloc_calls")}
    profile[mode]["times_ms"]=[r["median_ms"] for r in rs]
   dims=("median_ms","proc_vmhwm_kib","gmp_peak_live_bytes")
   for a in modes:
    profile[a]["observed_strict_dominates"]=[b for b in modes if a!=b and
      all(profile[a][x]<=profile[b][x] for x in dims) and
      any(profile[a][x]<profile[b][x] for x in dims)]
   profile["statistical_significance_established"]=False
   report["by_precision"][str(d)]=profile
 if args.out:args.out.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
 print(json.dumps(report,indent=2,sort_keys=True))
if __name__=="__main__":main()
