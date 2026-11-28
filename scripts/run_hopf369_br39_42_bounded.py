#!/usr/bin/env python3
"""BR39–42 bounded local acceptance, no CI, no shell or OpenBLAS requirement.

Each original checker is a separate <=90-second subprocess. Receipt identity
includes *source digests*, Python version and argument vector. Failures/timeouts
are retained, never recorded as PASS. Completed matching cases are skipped.
No script is executed merely by importing this module.

Usage:
 python scripts/run_hopf369_br39_42_bounded.py --part fast --output /tmp/hopf-receipts
 python scripts/run_hopf369_br39_42_bounded.py --part heavy --output /tmp/hopf-receipts
 python scripts/run_hopf369_br39_42_bounded.py --part all --output /tmp/hopf-receipts

The native Agda kernel must be executed separately; script PASS != kernel PASS.
"""
import argparse, hashlib, json, os, subprocess, sys, time
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
SCRIPTS=ROOT/"scripts"
PARTS={
  "fast":[
    ("BR39", "check_hopf369_br39_physical_cutoff.py",()),
    ("BR40.time","check_hopf369_br40_physical_time_weld.py",("--part","time")),
    ("BR40.trace","check_hopf369_br40_physical_time_weld.py",("--part","trace")),
    ("BR40.subsidiary","check_hopf369_br40_physical_time_weld.py",("--part","subsidiary")),
    ("BR40.graph","check_hopf369_br40_physical_time_weld.py",("--part","graph")),
    ("BR40.projector.small","check_hopf369_br40_variable_projector_transport.py",("--part","small")),
    ("BR41.work","check_hopf369_br41_signed_wall_work_budget.py",()),
    ("BR41.holonomy","check_hopf369_br41_normal_holonomy_projection.py",()),
    ("BR42.energy","check_hopf369_br42_physical_energy_restart.py",()),
    ("BR43.trace.warp","check_hopf369_br43_two_sided_trace.py",("--sector","warp")),
    ("BR43.trace.loss","check_hopf369_br43_two_sided_trace.py",("--sector","loss")),
    ("BR43.charge","check_hopf369_br43_trace_energy_weld.py",()),
  ],
  "heavy":[
    ("BR43.trace.metric","check_hopf369_br43_two_sided_trace.py",("--sector","metric")),
    ("BR43.trace.gauge","check_hopf369_br43_two_sided_trace.py",("--sector","gauge")),
    ("BR40.projector.physical","check_hopf369_br40_variable_projector_transport.py",("--part","physical")),
    *[(f"BR40.warp.covector.{k}","check_hopf369_br40_warped_connection.py",
       ("--sector","covector","--index",str(k))) for k in range(5)],
    *[(f"BR40.warp.tensor.{k}","check_hopf369_br40_warped_connection.py",
       ("--sector","tensor","--index",str(k))) for k in range(25)],
    ("BR40.warp.scalar","check_hopf369_br40_warped_connection.py",
     ("--sector","scalar","--index","0")),
  ]
}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def manifest_hash():
    # Include all directly used original operators and test sources; changes
    # anywhere relevant invalidate cached PASS. This is intentionally
    # conservative: new source commits force independent replay.
    paths=[ROOT/"DASHI/Physics/Foundations/Hopf369WarpedPhysicalBoundaryExact.agda"]
    paths+=sorted(SCRIPTS.glob("check_hopf369_br*.py"))
    paths+=sorted(SCRIPTS.glob("check_hopf369_bs*.py"))
    paths.append(Path(__file__).resolve())
    h=hashlib.sha256()
    for p in paths:
        if not p.is_file(): continue
        h.update(str(p.relative_to(ROOT)).encode());h.update(p.read_bytes())
    h.update(sys.version.encode())
    return h.hexdigest()

def atomic_json(path,obj):
    tmp=path.with_suffix(".tmp")
    with tmp.open("w") as out:
        json.dump(obj,out,indent=2,sort_keys=True)
        out.flush();os.fsync(out.fileno())
    os.replace(tmp,path)

def stage(label,script,args,receipts,identity,seconds):
    path=receipts/(label.replace("/","_")+".json")
    cmd=[sys.executable,str(SCRIPTS/script),*args]
    runid=hashlib.sha256(json.dumps([identity,cmd],sort_keys=True).encode()).hexdigest()
    if path.exists():
        previous=json.loads(path.read_text())
        if previous.get("runid")==runid and previous.get("status")=="PASS":
            return "CACHED_PASS"
    environment=dict(os.environ)
    environment.update(OPENBLAS_NUM_THREADS="1",MKL_NUM_THREADS="1",
                       OMP_NUM_THREADS="1",NUMEXPR_NUM_THREADS="1")
    begin=time.monotonic()
    try:
        result=subprocess.run(cmd,cwd=SCRIPTS,env=environment,text=True,
                   stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=seconds)
        status="PASS" if result.returncode==0 else "FAIL"
        output=result.stdout[-14000:];error=result.stderr[-14000:]
        code=result.returncode
    except subprocess.TimeoutExpired as exc:
        status="TIMEOUT"
        output=(exc.stdout or b"")
        error=(exc.stderr or b"")
        if isinstance(output,bytes):output=output.decode("utf-8","replace")
        if isinstance(error,bytes):error=error.decode("utf-8","replace")
        output=output[-14000:];error=error[-14000:]
        code=None
    receipt=dict(name=label,status=status,runid=runid,source_identity=identity,
         command=cmd,returncode=code,elapsed_seconds=round(time.monotonic()-begin,3),
         stdout=output,stderr=error,acceptance="source checker only; Agda kernel unrun")
    atomic_json(path,receipt)
    return status

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--part",choices=("fast","heavy","all"),default="fast")
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--seconds",type=int,default=90)
    args=parser.parse_args()
    if not 1<=args.seconds<=90:raise ValueError("bounded run: max 90 seconds/case")
    args.output.mkdir(parents=True,exist_ok=True)
    ident=manifest_hash()
    plans=PARTS["fast"]+PARTS["heavy"] if args.part=="all" else PARTS[args.part]
    outcome={}
    for label,script,opts in plans:
        outcome[label]=stage(label,script,opts,args.output,ident,args.seconds)
        print(label,outcome[label],flush=True)
    atomic_json(args.output/"summary.json",dict(source_identity=ident,part=args.part,
          outcomes=outcome,all_accepted=all(v in ("PASS","CACHED_PASS") for v in outcome.values()),
          native_kernel_accepted=False,physical_pde_theorem_accepted=False))
    if any(v not in ("PASS","CACHED_PASS") for v in outcome.values()):sys.exit(1)

if __name__=="__main__":main()
