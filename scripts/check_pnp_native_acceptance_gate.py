#!/usr/bin/env python3
"""Local native acceptance gate. Stop at first failing stage; never CI.
Run on actual checkouts, with existing project dependencies installed.
"""
import argparse,json,shutil,subprocess,time
from pathlib import Path

AGDA=[
    "DASHI/Mathematics/Complexity/PNPSection32GeometryAcceptance.agda",
    "DASHI/Mathematics/Complexity/PNPSection33BarrierAcceptance.agda",
]
LEAN=[
    "Welds.PNPSection32GeometryAcceptanceExact",
    "Welds.PNPSection33BarrierAcceptanceExact",
    "Welds.PNPSection34IntegerFibreAcceptanceExact",
    "Welds.PNPSection35SeparatorAcceptanceExact",
    "Welds.PNPSection36CompressedBoundaryAcceptanceExact",
    "Welds.PNPSection36SameObligationInputVsWorkAcceptanceExact",
    "Welds.PNPSection38ObservationAcceptanceExact",
]

def main():
    p=argparse.ArgumentParser();p.add_argument("--agda-dir",type=Path);p.add_argument("--lean-dir",type=Path)
    p.add_argument("--out",type=Path,required=True);p.add_argument("--timeout",type=int,default=90)
    p.add_argument("--agda-flag",action="append",default=[]);a=p.parse_args()
    if not (a.agda_dir or a.lean_dir) or a.timeout<=0:p.error("provide checkout(s) and positive timeout")
    out=a.out.resolve();out.mkdir(parents=True,exist_ok=True);data={"status":"RUNNING","checkouts":{},"stages":[]}
    def save():
        tmp=out/"receipt.tmp";tmp.write_text(json.dumps(data,indent=2)+"\n");tmp.replace(out/"receipt.json")
    def capture(cwd,cmd):
        return subprocess.run(cmd,cwd=cwd,capture_output=True,text=True,timeout=a.timeout,check=True).stdout.strip()
    def stage(cwd,cmd):
        i=len(data["stages"]);log=out/("%03d.log"%i);start=time.monotonic()
        with log.open("w") as f:
            try:code=subprocess.run(cmd,cwd=cwd,stdout=f,stderr=subprocess.STDOUT,timeout=a.timeout).returncode
            except subprocess.TimeoutExpired:code=124
            except OSError as e:f.write(str(e));code=127
        data["stages"].append(dict(cwd=str(cwd),command=cmd,code=code,seconds=time.monotonic()-start,log=log.name))
        if code:data["status"]="BLOCKED" if code==127 else "TIMEOUT" if code==124 else "FAILED"
        save()
        return code==0
    for kind,cwd in (("agda",a.agda_dir),("lean",a.lean_dir)):
        if cwd is None:continue
        cwd=cwd.resolve()
        try:data["checkouts"][kind]=dict(path=str(cwd),head=capture(cwd,["git","rev-parse","HEAD"]),dirty=capture(cwd,["git","status","--porcelain","--untracked-files=no"]))
        except (OSError,subprocess.SubprocessError) as e:
            data["status"]="BLOCKED";data["error"]=str(e);save();return 1
        if kind=="agda":
            if not stage(cwd,["agda","--version"]):return 1
            for path in AGDA:
                if not stage(cwd,["agda",*a.agda_flag,path]):return 1
        else:
            if not stage(cwd,["lake","env","lean","--version"]):return 1
            for module in LEAN:
                # Lake builds imported dependencies; the direct invocation
                # then emits the root's #check and #print axioms output.
                if not stage(cwd,["lake","build","+"+module]):return 1
                if not stage(cwd,["lake","env","lean",module.replace(".","/")+".lean"]):return 1
    data["status"]="COMMANDS_COMPLETED";save()
    # Completion is not an axiom audit: inspect all emitted axiom lines
    # and the checkout state before claiming proof acceptance.
    return 0

if __name__=="__main__":raise SystemExit(main())
