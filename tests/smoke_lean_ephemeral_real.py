#!/usr/bin/env python3
"""Actual Lean compiler smoke via PINNED nix develop .#lean-world environment.

Run:
  nix develop .#lean-world --command python3 tests/smoke_lean_ephemeral_real.py

This uses the real Lean subprocess and actual output .olean, not a mock.
Proof certification/export is NOT claimed; the program uses a trivial local
example only, and the compile source is ephemeral (not a Git checkout).
"""
from __future__ import annotations
import hashlib
from pathlib import Path
import shutil
import sys
import tempfile

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from lean_ephemeral_elaboration import (
    EphemeralLeanWorker,compiled_dependency_digest)

SOURCE = b"theorem dashiWorkerSmoke : True := trivial\n"


def source_receipt(data):
    return {"repository":"dashi/local-smoke",
            "revision":"a"*40,"path":"WorkerSmoke.lean",
            "git_blob":hashlib.sha1(
                b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest(),
            "sha256":hashlib.sha256(data).hexdigest(),
            "size":len(data),"status":"source-verified-not-elaborated"}


def main():
    if not shutil.which("lean"):
        raise SystemExit("LEAN_EPHEMERAL_NOT_VALIDATED: actual Lean not on PATH")
    root=Path(__file__).resolve().parents[1]
    with tempfile.TemporaryDirectory(prefix="dashi-olean-real-smoke-") as temp:
        worker=EphemeralLeanWorker(
            flake=root,cache=Path(temp),
            closure_digest=compiled_dependency_digest(None),
            command=("lean",))
        first=worker.elaborate(source_receipt(SOURCE),SOURCE,"WorkerSmoke.lean")
        second=worker.elaborate(source_receipt(SOURCE),SOURCE,"WorkerSmoke.lean")
        changed=SOURCE+b"-- source revision changed\n"
        third=worker.elaborate(
            source_receipt(changed),changed,"WorkerSmoke.lean")
        assert first.status=="lean-compiled-not-exported" and first.olean_sha256
        assert not first.reused and second.reused
        assert first.cache_key==second.cache_key
        assert not third.reused and third.cache_key!=first.cache_key
        print("LEAN_EPHEMERAL_REAL_SMOKE_PASSED")
        print("compiler:", first.compiler_version)
        print("cached unchanged .olean:", second.reused)
        print("source change invalidated .olean:", not third.reused)
        print("kernel statement export certified: NO")


if __name__=="__main__":
    main()
