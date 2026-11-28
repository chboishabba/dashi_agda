#!/usr/bin/env python3
"""BR39–66 bounded local acceptance, no CI, no shell or OpenBLAS requirement.

Each original checker is a separate <=90-second subprocess. Receipt identity
includes *source digests*, Python version and argument vector. Failures/timeouts
are retained, never recorded as PASS. Completed matching cases are skipped.
No script is executed merely by importing this module.

Usage:
 python scripts/run_hopf369_br39_42_bounded.py --part frontier --output /tmp/hopf-receipts\n python scripts/run_hopf369_br39_42_bounded.py --part fast --output /tmp/hopf-receipts
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
    ("BR44.two_level","check_hopf369_br44_two_level_energy.py",()),
    ("BR45.coefficient_growth","check_hopf369_br45_coefficient_growth.py",()),
    ("BR45.energy_ledger","check_hopf369_br45_differentiated_br4.py",("--sector","ledger")),
    ("BR48.adm_collar","check_hopf369_br48_adm_boundary_geometry.py",("--part","collar")),
    ("BR48.shift_guard","check_hopf369_br48_adm_boundary_geometry.py",("--part","shift")),
    ("BR49.graph","check_hopf369_br49_moving_wall_conormal.py",("--part","graph")),
    ("BR49.channels","check_hopf369_br49_moving_wall_conormal.py",("--part","channels")),
    ("BR50.wall_source","check_hopf369_br50_material_energy_weld.py",("--part","source")),
    ("BR51.defect_algebra","check_hopf369_br51_graph_defect_budget.py",("--part","algebra")),
    ("BR51.defect_budget","check_hopf369_br51_graph_defect_budget.py",("--part","budget")),
    ("BR51.defect_channels","check_hopf369_br51_graph_defect_budget.py",("--part","channels")),
    ("BR52.negative","check_hopf369_br52_all_order_material_flux.py",("--part","negative")),
    ("BR53.small","check_hopf369_br53_physical_bianchi_factor.py",("--part","small")),
    ("BR54.negative","check_hopf369_br54_mixed_material_tame.py",("--part","negative")),
    ("BR55.curved","check_hopf369_br55_curved_bianchi_source.py",("--part","curved")),
    ("BR55.boundary","check_hopf369_br55_curved_bianchi_source.py",("--part","boundary")),
    ("BR56.energy","check_hopf369_br56_tame_graph_energy.py",("--part","energy")),
    ("BR56.refusal","check_hopf369_br56_tame_graph_energy.py",("--part","refusal")),
    ("BR57.constants","check_hopf369_br57_curvature_normal_inverse.py",("--part","constants")),
    ("BR59.flat","check_hopf369_br59_full_moving_israel_geometry.py",("--part","flat")),
    ("BR59.warped","check_hopf369_br59_full_moving_israel_geometry.py",("--part","warped")),
    ("BR59.shift","check_hopf369_br59_full_moving_israel_geometry.py",("--part","shift")),
    ("BR60.shape_negative","check_hopf369_br60_moving_israel_frechet.py",("--part","negative")),
    ("BR61.junction","check_hopf369_br61_two_face_nonlinear_israel.py",("--part","rows")),
    ("BR61.unmatched","check_hopf369_br61_two_face_nonlinear_israel.py",("--part","refusal")),
    ("BR62.codazzi","check_hopf369_br62_israel_codazzi_rank.py",()),
    ("BR63.eta","check_hopf369_br63_nonlinear_israel_inverse.py",("--part","reference")),
    ("BR63.moving","check_hopf369_br63_nonlinear_israel_inverse.py",("--part","moving")),
    ("BR63.null","check_hopf369_br63_nonlinear_israel_inverse.py",("--part","source")),
    ("BR64.bidi","check_hopf369_br64_full_israel_optical_bidi.py",("--part","bidi")),
    ("BR64.negative","check_hopf369_br64_full_israel_optical_bidi.py",("--part","negative")),
    ("BR65.geometry","check_hopf369_br65_optical_geometric_israel_weld.py",("--part","geometry")),
    ("BR65.reference","check_hopf369_br65_optical_geometric_israel_weld.py",("--part","reference")),
    ("BR66.mean","check_hopf369_br66_nonzero_mean_israel_weld.py",()),
  ],
  "heavy":[
    *[(f"BR60.K.{i}","check_hopf369_br60_moving_israel_frechet.py",("--part","component","--index",str(i))) for i in range(10)],
    ("BR52.metric","check_hopf369_br52_all_order_material_flux.py",("--part","metric")),
    ("BR52.gauge","check_hopf369_br52_all_order_material_flux.py",("--part","gauge")),
    ("BR53.physical","check_hopf369_br53_physical_bianchi_factor.py",("--part","physical")),
    *[(f"BR54.{sector}.{multi}","check_hopf369_br54_mixed_material_tame.py",("--part",sector,"--multi",multi)) for sector in ("metric","gauge") for multi in ("2,2,2,2","8,0,0,0","0,8,0,0","0,0,0,8","4,2,1,1")],
    ("BR55.flat","check_hopf369_br55_curved_bianchi_source.py",("--part","flat")),
    ("BR56.coeff","check_hopf369_br56_tame_graph_energy.py",("--part","coeff")),
    *[(f"BR57.normal.{k}","check_hopf369_br57_curvature_normal_inverse.py",("--part","channel","--component",str(k))) for k in range(16)],
    *[(f"BR58.{sector}.{alloc}","check_hopf369_br58_material_boundary_jets.py",("--sector",sector,"--allocation",alloc)) for sector in ("metric","gauge") for alloc in ("D","E")],
    ("BR48.variable_source","check_hopf369_br48_adm_boundary_geometry.py",("--part","source")),
    *[(f"BR47.{sector}.{alloc}.{k}","check_hopf369_br47_boundary_hierarchy.py",("--sector",sector,"--allocation",alloc,"--order",str(k))) for sector in ("metric","gauge") for alloc in ("D","E") for k in range(9)],
    *[(f"BR45.metric.{k}","check_hopf369_br45_differentiated_br4.py",("--sector","metric","--component",str(k))) for k in range(15)],
    *[(f"BR45.gauge.{k}","check_hopf369_br45_differentiated_br4.py",("--sector","gauge","--component",str(k))) for k in range(5)],
    *[(f"BR46.bianchi.{k}","check_hopf369_br46_bianchi_source_weld.py",("--component",str(k))) for k in range(5)],
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
    parser.add_argument("--part",choices=("fast","heavy","frontier","all"),default="frontier")
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--seconds",type=int,default=90)
    args=parser.parse_args()
    if not 1<=args.seconds<=90:raise ValueError("bounded run: max 90 seconds/case")
    args.output.mkdir(parents=True,exist_ok=True)
    ident=manifest_hash()
    if args.part=="all":
        plans=PARTS["fast"]+PARTS["heavy"]
    elif args.part=="frontier":
        plans=[p for group in ("fast","heavy") for p in PARTS[group]
               if p[0].split(".")[0] in {"BR52","BR53","BR54","BR55","BR56","BR57","BR58","BR59","BR60","BR61","BR62","BR63","BR64","BR65","BR66"}]
    else:
        plans=PARTS[args.part]
    outcome={}
    for label,script,opts in plans:
        outcome[label]=stage(label,script,opts,args.output,ident,args.seconds)
        print(label,outcome[label],flush=True)
    atomic_json(args.output/"summary.json",dict(source_identity=ident,part=args.part,
          outcomes=outcome,all_accepted=all(v in ("PASS","CACHED_PASS") for v in outcome.values()),
          native_kernel_accepted=False,physical_pde_theorem_accepted=False))
    if any(v not in ("PASS","CACHED_PASS") for v in outcome.values()):sys.exit(1)

if __name__=="__main__":main()
