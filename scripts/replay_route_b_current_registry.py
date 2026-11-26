#!/usr/bin/env python3
"""Adapt the EXISTING Lean Route-B replay to registered current Agda names.

Historical pinned manifest is immutable. This checks seven exact root bodies,
then delegates syntax/closure generation to the original Lean scripts.
Neither a passed root check nor generated Lean is kernel acceptance.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

OLD = "c72ea464663a02333319f2254967c94bd188f5f5"
BISHOP = "240e38c7f6938f20f865b1f956c5f084da48bd54"
REGISTRY = "8259791cb9674ee212014c9ece2452809856eab5"
ROOTS = {
    "DASHI/Moonshine/BishopRound11MachinSetoidComplexInstanceExact.agda":
        ("ec132e001eeb7836078561e88fe2b3f54438facb", "104e0c3440cdd963deae79b3eb5562730cdcbf7d"),
    "DASHI/Foundations/BishopMachinArctanConstructionExact.agda":
        ("be11dee1db4eb6856346267134dcd85fed96fc2a", "be11dee1db4eb6856346267134dcd85fed96fc2a"),
    "DASHI/Foundations/BishopExponentialSeriesConvergenceExact.agda":
        ("b62d767e74c6473e31bdf86458d93445656f6978", "b62d767e74c6473e31bdf86458d93445656f6978"),
    "DASHI/Foundations/BishopConcreteTrigSeriesConvergenceExact.agda":
        ("75b8b72ea4e240bfde706272beb5ff5e5fba9af5", "0e8822ddea9a634ac2c8bc66f2bd81ecde631f51"),
    "DASHI/Analysis/BishopSetoidComplexExact.agda":
        ("739af368ced4b730225db4177529b281f4e8c493", "739af368ced4b730225db4177529b281f4e8c493"),
    "DASHI/Moonshine/JInvariantEisensteinBishopSetoidFiniteQSeriesExact.agda":
        ("4787feafbd9630dc439556543c42c6b75bf7fdbd", "4787feafbd9630dc439556543c42c6b75bf7fdbd"),
    "DASHI/Moonshine/JInvariantEisensteinBishopSetoidExtractionExact.agda":
        ("baee86e7085c9193227142eb9713df9d2e4a546e", "baee86e7085c9193227142eb9713df9d2e4a546e"),
}
DELEGATES = {
    "syntax": ("route_b_agda_replay_probe.py", "6514186fd9e3bec348b1eb90550d21f8cd1cb41e", "TARGETS"),
    "generate": ("route_b_agda_kernel_replay.py", "3dfc00c24b8c81ac63631a163b65a4445f98fbb5", "ROOTS"),
}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])


def blob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def verify(source, lean):
    require(not git(source, "status", "--porcelain", "--untracked-files=no").strip(),
            "tracked Agda checkout is dirty")
    registry = (source / "config/semantic-name-registry.json").read_bytes()
    require(blob(registry) == REGISTRY, "registry drift: review explicitly")
    reg = json.loads(registry)
    changes = sorted(reg["module_renames"] + reg["symbol_renames"],
                     key=lambda m: -len(m["from"]))
    def normalize(text):
        for m in changes:
            text = text.replace(m["from"], m["to"])
        return text
    module_renames = {m["from"]: m["to"] for m in reg["module_renames"]}
    def path_for(old):
        mod = old[:-5].replace("/", ".")
        return module_renames.get(mod, mod).replace(".", "/") + ".agda"
    rows = []
    for old, (oldsha, newsha) in ROOTS.items():
        new = path_for(old)
        historical = git(source, "show", OLD + ":" + old)
        current = (source / new).read_bytes()
        require(blob(historical) == oldsha, "historical blob mismatch: " + old)
        require(blob(current) == newsha, "current blob mismatch: " + new)
        require(current == git(source, "show", "HEAD:" + new), "checkout mismatch: " + new)
        # Exact bodies need no normalization (comments may mention old names).
        require(historical == current or normalize(historical.decode()).encode() == current,
                "non-rename semantic drift: " + new)
        rows.append({"historical": old, "current": new, "old_blob": oldsha,
                     "new_blob": newsha, "byte_identical": historical == current})
    require((source / "vendor/bishop").is_dir(), "Bishop submodule absent")
    require(git(source / "vendor/bishop", "rev-parse", "HEAD").decode().strip() == BISHOP,
            "Bishop pin mismatch")
    require(not git(source / "vendor/bishop", "status", "--porcelain").strip(), "dirty Bishop submodule")
    return normalize, path_for, {"agda_commit": git(source, "rev-parse", "HEAD").decode().strip(),
        "historical_agda_commit": OLD, "bishop_commit": BISHOP,
        "registry_blob": REGISTRY, "roots": rows,
        "lean_commit": git(lean, "rev-parse", "HEAD").decode().strip(),
        "kernel_accepted": False, "generated_replay_observed": False}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--source-root", type=Path, required=True)
    ap.add_argument("--lean-root", type=Path, required=True)
    ap.add_argument("--receipt", type=Path, required=True)
    ap.add_argument("--mode", choices=("verify", "syntax", "generate"), default="verify")
    ap.add_argument("--out", type=Path)
    ap.add_argument("--roots-file", type=Path)
    args = ap.parse_args()
    source, lean = args.source_root.resolve(), args.lean_root.resolve()
    normalize, path_for, receipt = verify(source, lean)
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(json.dumps(receipt, indent=2) + "\n")
    print("verified seven root bodies; no kernel claim")
    if args.mode == "verify":
        return 0
    require(args.out is not None, "--out is required")
    require(args.mode != "generate" or args.roots_file is not None, "--roots-file is required")
    name, sha, attr = DELEGATES[args.mode]
    script = lean / "scripts" / name
    require(blob(script.read_bytes()) == sha, "delegate drift: " + name)
    spec = importlib.util.spec_from_file_location("route_b_existing_delegate", script)
    require(spec is not None and spec.loader is not None, "delegate import failed")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    roots = getattr(module, attr)
    require(set(roots) == set(ROOTS), "delegate root set drift")
    setattr(module, attr, {path_for(p): tuple(normalize(d) for d in ds)
                           for p, ds in roots.items()})
    sys.argv = [str(script), "--source-root", str(source)]
    if args.mode == "syntax":
        sys.argv += ["--out", str(args.out.resolve())]
    else:
        sys.argv += ["--dest", str(args.out.resolve()), "--roots-file", str(args.roots_file.resolve())]
    return module.main()


if __name__ == "__main__":
    raise SystemExit(main())
