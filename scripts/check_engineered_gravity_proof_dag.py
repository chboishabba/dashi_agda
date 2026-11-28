"""Fail-closed source-qualified 12-lane proof dependency checker.
Owner existence or a successful symbolic checker NEVER pays a physical proof.
"""
import argparse,hashlib,json,os,subprocess,sys
from pathlib import Path
STAGES=("S0_source","S1_constraints","S2_interface","S3_evolution","S4_receiver","S5_certification")
LANES=("A_shielding","B_bulk","C_radion","D_active_stress_TOV","E_coherent_OCT369",
       "F_EM_GW","G_warp_junction","H_lift","I_hybrid","J_F8","G3_vacuum","G4_Einstein_RMHD")
DEFAULT=Path(__file__).resolve().parents[1]/"Artifacts/engineered-gravity/engineered_gravity_dependency_manifest_20261129.json"
def audit(m,repo=None):
    assert m["schema"]=="engineered-gravity-proof-dag-v1"
    assert tuple(m["stages"])==STAGES and tuple(m["lanes"])==LANES
    results={}
    for key,spec in m["lanes"].items():
        assert spec["owner"] and spec["unpaid"] and spec["unpaid_stages"] and spec["constructed"]
        assert len(set(spec["owner"]))==len(spec["owner"])
        assert set(spec["unpaid_stages"])<=set(STAGES)
        assert len(spec["unpaid_stages"])==len(set(spec["unpaid_stages"]))
        assert all(z.startswith("scripts/") and z.endswith(".py") for z in spec["owner"])
        owners={}
        for path in spec["owner"]:
            f=repo/path if repo else None
            owners[path]=("NOT_CHECKED" if f is None else
                hashlib.sha256(f.read_bytes()).hexdigest() if f.is_file() else "MISSING")
        results[key]={"status":"OPEN","unpaid":spec["unpaid"],
                      "unpaid_stages":spec["unpaid_stages"],"owners":owners}
    for label,p in m["cross_lane_shared_welds"].items():
        assert len(set(p))==len(p) and len(p)>1 and set(p)<=set(LANES),label
    return results

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--manifest",type=Path,default=DEFAULT)
    p.add_argument("--repo",type=Path)
    p.add_argument("--execute",action="store_true")
    p.add_argument("--owner",action="append",default=[])
    p.add_argument("--timeout",type=int,default=90)
    p.add_argument("--output",type=Path)
    args=p.parse_args()
    assert args.timeout>0
    manifest=json.loads(args.manifest.read_text())
    repo=args.repo.resolve() if args.repo else None
    result=audit(manifest,repo)
    required={x for s in manifest["lanes"].values() for x in s["owner"]}
    checks={}
    if args.execute:
        if not repo or not args.owner:raise ValueError("explicit --repo and --owner required")
        if set(args.owner)-required:raise ValueError("unregistered original owner")
        for path in args.owner:
            f=repo/path
            if not f.is_file():checks[path]={"status":"BLOCKED","reason":"source absent"};continue
            try:
                z=subprocess.run([sys.executable,str(f)],cwd=repo,text=True,capture_output=True,
                    timeout=args.timeout,env={**os.environ,"OPENBLAS_NUM_THREADS":"1","PYTHONDONTWRITEBYTECODE":"1"})
                checks[path]={"status":"PASS" if z.returncode==0 else "FAIL",
                    "exit_code":z.returncode,
                    "source_sha256":hashlib.sha256(f.read_bytes()).hexdigest(),
                    "output_sha256":hashlib.sha256((z.stdout+z.stderr).encode()).hexdigest()}
            except subprocess.TimeoutExpired:checks[path]={"status":"TIMEOUT"}
    status="BLOCKED" if repo and any("MISSING" in z["owners"].values() for z in result.values()) else "INVENTORY_ONLY"
    payload={"status":status,"lane_count":len(result),"lanes":result,"owner_checks":checks,
             "known_unpaid_count":sum(len(x["unpaid"]) for x in result.values()),
             "scope":"Source-qualified bookkeeping, not native or physical certification"}
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        t=args.output.with_suffix(".tmp")
        t.write_text(json.dumps(payload,sort_keys=True,indent=2)+"\n")
        t.replace(args.output)
    print(json.dumps({"status":status,"lanes":len(result),"unpaid":payload["known_unpaid_count"],"owner_checks":checks},sort_keys=True))
    if status=="BLOCKED" or any(v["status"]!="PASS" for v in checks.values()):raise SystemExit(1)
if __name__=="__main__":main()
