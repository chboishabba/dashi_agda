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
SOURCE=ROOT/"scripts/check_pi_p0_fibre_cost_profile.cpp"
SOURCE_BLOB="4b6534f31db5ae4fd3b885560a3fd9d3429460e7"
EXPECTED={
 10000:"ab03bf7037718e1525340a0c43f0049ddbe99c6067ad3e08a4de5c591fedc524",
 100000:"79b862cc31ceb97bb3c39d05ae74664c99f0ff7670b3e08a4b21a31ef84d7711",
 500000:"fe727f5894e072423c570402dd3948bef1f318ea957498aab06a95351e1018f9",
 1000000:"130203eb055a962b8441af76c22b75627ec18c672a485904e567f59251e8ee18",
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
 if data["measured_GMP_total_live_heap"]!="false" or data["model_is_upper_bound"]!="false":
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
 blob=run(["git","hash-object",str(SOURCE)],cwd=ROOT).strip()
 if blob!=SOURCE_BLOB:raise AssertionError("committed C++ bytes moved: "+blob)
 report=dict(schema="paper9-pi-p0-cost-fibre-allocator-ledger-v1",
  exact_source_git_blob=blob,
  premises="classical Chudnovsky identity and alternating tail",
  certification="original GMP exact decimal floor + SHA256 output regressions",
  formal_agda_kernel_checked=False,external_sota_compared=False,
  gmp_heap_hooks_capture_non_gmp_memory=False,
  peak_explicit_carrier_model_is_heap_upper_bound=False,
  source_pinned=True,samples=[],by_precision={})
 with tempfile.TemporaryDirectory(prefix="pi-p0-fibre-") as folder:
  binary=str(Path(folder)/"pi-fibre")
  run(["g++","-O3","-std=c++17","-Wall","-Wextra","-pedantic",str(SOURCE),
       "-lgmpxx","-lgmp","-lcrypto","-o",binary],timeout=120,cwd=ROOT)
  for d in args.digits:
   modes=["baseline","inplace"]
   records={name:[] for name in modes}
   for i in range(args.reps):
    for mode in (modes if i%2==0 else list(reversed(modes))):
     row=parse(run([binary,str(d),mode,"1"]),d,mode)
     row["rotation"]=i;records[mode].append(row);report["samples"].append(row)
   profile={}
   for mode,rs in records.items():
    profile[mode]={name:statistics.median(x[name] for x in rs)
     for name in ("median_ms","proc_vmhwm_kib","gmp_peak_live_bytes",
       "peak_explicit_carrier_capacity_bytes","gmp_alloc_calls",
       "gmp_realloc_calls")}
    profile[mode]["times_ms"]=[r["median_ms"] for r in rs]
   base=profile["baseline"];new=profile["inplace"]
   # Strict coordinatewise Pareto, not an attribution of causal speedup.
   dims=("median_ms","proc_vmhwm_kib","gmp_peak_live_bytes")
   profile["inplace_dominates_baseline_observed"]=(
      all(new[x]<=base[x] for x in dims) and any(new[x]<base[x] for x in dims))
   profile["baseline_dominates_inplace_observed"]=(
      all(base[x]<=new[x] for x in dims) and any(base[x]<new[x] for x in dims))
   profile["statistical_significance_established"]=False
   report["by_precision"][str(d)]=profile
 if args.out:args.out.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
 print(json.dumps(report,indent=2,sort_keys=True))
if __name__=="__main__":main()
