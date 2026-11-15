#!/usr/bin/env python3
"""Run a real two-module Lean donor -> consumer proof smoke under pinned Lean.

This proves a separate imported Lean proof elaborates without sorry.
It does NOT establish hyperfabric retrieval or independent checker agreement.
Operator runs from an already pinned Nix environment. No network, no CI.
"""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import tempfile

DONOR = """namespace DASHIWorldSmoke
theorem originalIdentity (p : Prop) : p → p := by
  intro hp
  exact hp
end DASHIWorldSmoke
"""
CONSUMER = """import Donor
namespace DASHIWorldSmoke
theorem consumerIdentity (p : Prop) : p → p := by
  exact originalIdentity p
#print axioms DASHIWorldSmoke.consumerIdentity
end DASHIWorldSmoke
"""

class LeanSmokeError(ValueError):
    pass

def run(lean: Path, *, timeout=120):
    lean=Path(lean).resolve(strict=True)
    if not lean.is_file() or not os.access(lean,os.X_OK):
        raise LeanSmokeError("pinned Lean executable unavailable")
    if timeout < 1 or timeout > 1800:
        raise LeanSmokeError("invalid timeout")
    environment={k:os.environ[k] for k in (
        "PATH","HOME","LANG","LC_ALL","LEAN_SYSROOT","LEAN_PATH","TMPDIR"
    ) if k in os.environ}
    with tempfile.TemporaryDirectory(prefix="dashi-donor-consumer-") as tmp:
        directory=Path(tmp)
        environment["LEAN_PATH"]=str(directory) + (
            os.pathsep+environment["LEAN_PATH"] if environment.get("LEAN_PATH") else "")
        version=subprocess.run((str(lean),"--version"),
            capture_output=True,timeout=15,check=False,env=environment)
        if version.returncode:
            raise LeanSmokeError("Lean version probe rejected")
        for module,source in (("Donor",DONOR),("Consumer",CONSUMER)):
            (directory/(module+".lean")).write_text(source,encoding="utf-8")
            command=(str(lean),"-o",module+".olean",module+".lean")
            result=subprocess.run(command,cwd=directory,env=environment,
                capture_output=True,timeout=timeout,check=False)
            if result.returncode:
                raise LeanSmokeError(
                    module+" elaboration failed; stderr_sha256="+
                    sha256(result.stderr).hexdigest())
            if not (directory/(module+".olean")).is_file():
                raise LeanSmokeError(module+" produced no .olean")
        return {
            "schema":"dashi-lean-donor-consumer-smoke-v1",
            "status":"lean-two-module-reuse-checked",
            "lean_version":version.stdout.decode("utf-8","replace").strip(),
            "lean_binary_sha256":sha256(lean.read_bytes()).hexdigest(),
            "donor_source_sha256":sha256(DONOR.encode()).hexdigest(),
            "consumer_source_sha256":sha256(CONSUMER.encode()).hexdigest(),
            "donor_olean_sha256":sha256((directory/"Donor.olean").read_bytes()).hexdigest(),
            "consumer_olean_sha256":sha256((directory/"Consumer.olean").read_bytes()).hexdigest(),
            "second_lean_elaboration_succeeded":True,
            "retrieved_from_canonical_world":False,
            "independent_checker_certified":False,
            "world_admitted":False
        }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean",type=Path,required=True)
    p.add_argument("--timeout",type=int,default=120)
    args=p.parse_args()
    try:
        print(json.dumps(run(args.lean,timeout=args.timeout),sort_keys=True))
    except (OSError,LeanSmokeError,subprocess.TimeoutExpired) as exc:
        p.exit(2,"DONOR_CONSUMER_SMOKE_INCOMPLETE: "+str(exc)+"\n")
    return 0

if __name__=="__main__":
    raise SystemExit(main())
