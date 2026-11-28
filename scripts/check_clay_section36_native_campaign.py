#!/usr/bin/env python3
"""Section 36 all-Clay native campaign, fail closed, exact owner checkouts.

Every source and acceptance root is committed on its OWN PR branch.
This runner checks original native Agda/Lean files in independently
provided worktrees, records actual exit codes and Git HEADs, and never
turns a symbolic Python check into a kernel receipt.

Usage:
  python scripts/check_clay_section36_native_campaign.py \\
    --ym-root /checkout/dashi_agda_ym \\
    --ns-root /checkout/dashi_lean4_ns \\
    --bsd-hodge-root /checkout/dashi_lean4_bsd \\
    --pnp-root /checkout/dashi_lean4_pnp \\
    --rh-root /checkout/dashi_lean4_rh \\
    --agda-include /checkout/stdlib \\
    --agda-include /checkout/bishop \\
    --rh-source-root /checkout/pinned_external_rh \\
    --rh-manifest /checkout/sha256_manifest.json \\
    --rh-main-sha256 <64-hex-pin> \\
    --report /checkout/dashi_agda_rollup/Docs/receipts/ClaySection36Native.json

Return 0 ONLY when every original proof root has completed native
elaboration and RH source admission. Missing inputs, dirty checkout,
wrong branches or failed source check make the overall result FAIL.
Do not claim the returned report is committed: the runner writes a
new receipt and the owner must add/commit its exact bytes afterward.
"""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

ROOTS = {
 "YM": ("ym_root", [
  "DASHI/Physics/YangMills/YMClayCMP102Section33WeightedCauchyClosureAcceptanceExact.agda",
  "DASHI/Physics/YangMills/YMClayCMP102Section34FactorialMassAcceptanceExact.agda",
  "DASHI/Physics/YangMills/YMClayCMP102Section35ThreeWingOrderAcceptanceExact.agda",
 ]),
 "NS": ("ns_root", [
  "Synthesis/ClayNSSection36FullSameFlowCompactnessAcceptanceExact.lean",
 ]),
 "BSD_HODGE": ("bsd_hodge_root", [
  "Synthesis/ClayBSDSection36AllDegreeMellinEnvelopeAcceptanceExact.lean",
  "Synthesis/ClayHodgeSection36AllPowersSaturationAcceptanceExact.lean",
 ]),
 "PNP": ("pnp_root", [
  "Welds/PNPSection36SameObligationInputVsWorkAcceptanceExact.lean",
 ]),
}

BRANCHES = {
 "YM": "agent/ym-p0-cmp119-r445-master-weld-20261121",
 "NS": "research/ns-native-proof-weld-20261127",
 "BSD_HODGE": "research/clay-bsd-hodge-moment-orientation-20261127",
 "PNP": "research/clay-p0-polynomial-coverage-endpoint-20261124",
 "RH": "fix/alpoge-original-admission-axiom-log-20261126",
}


def call(cmd: list[str], cwd: Path, seconds: int) -> dict:
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True,
                           text=True, timeout=seconds, check=False)
        return {"command": cmd, "exit": p.returncode,
                "stdout_tail": p.stdout[-5000:],
                "stderr_tail": p.stderr[-5000:]}
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {"command": cmd, "exit": None, "error": str(exc)}


def checkout_identity(root: Path, expected: str) -> dict:
    if not root.is_dir() or not (root / ".git").exists():
        return {"ok": False, "error": "checkout or .git missing"}
    branch = call(["git", "branch", "--show-current"], root, 20)
    head = call(["git", "rev-parse", "HEAD"], root, 20)
    status = call(["git", "status", "--porcelain"], root, 20)
    ok = (branch.get("exit") == 0 and head.get("exit") == 0
          and status.get("exit") == 0
          and branch.get("stdout_tail", "").strip() == expected
          and not status.get("stdout_tail", "").strip())
    return {"ok": ok, "branch": branch.get("stdout_tail", "").strip(),
            "HEAD": head.get("stdout_tail", "").strip(),
            "dirty": bool(status.get("stdout_tail", "").strip()),
            "expected_branch": expected}


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    for k in ("ym", "ns", "bsd-hodge", "pnp", "rh"):
        p.add_argument("--"+k+"-root", type=Path, required=True)
    p.add_argument("--agda-include", type=Path, action="append", default=[])
    p.add_argument("--agda", default="agda")
    p.add_argument("--lake", default="lake")
    p.add_argument("--rh-source-root", type=Path, required=True)
    p.add_argument("--rh-manifest", type=Path, required=True)
    p.add_argument("--rh-main-sha256", required=True)
    p.add_argument("--report", type=Path, required=True)
    p.add_argument("--timeout", type=int, default=90)
    args = p.parse_args()
    report = {"schema": "Clay36NativeAcceptanceV1",
              "fully_accepted": False, "roots": {}, "checks": []}
    roots = {key: Path(getattr(args, key.lower()+"_root")).resolve()
             for key in ("ym", "ns", "pnp", "rh")}
    roots["bsd_hodge"] = args.bsd_hodge_root.resolve()
    for owner, (attr, paths) in ROOTS.items():
        root = roots[attr.removesuffix("_root")]
        ident = checkout_identity(root, BRANCHES[owner])
        report["roots"][owner] = ident
        if not ident["ok"]:
            report["checks"].append({"owner": owner, "status": "NOT_RUN",
                                     "reason": "wrong branch or unclean checkout"})
            continue
        for path in paths:
            if not (root / path).is_file():
                report["checks"].append({"owner": owner, "path": path,
                                         "status": "MISSING"})
                continue
            if owner == "YM":
                cmd = [args.agda, "--safe", "-i", str(root)]
                for include in args.agda_include:
                    cmd.extend(["-i", str(include.resolve())])
                cmd.append(path)
            else:
                cmd = [args.lake, "env", "lean", path]
            result = call(cmd, root, args.timeout)
            report["checks"].append({"owner": owner, "path": path,
                     "status": "PASS" if result["exit"] == 0 else "FAIL",
                     "result": result})
    rhroot = roots["rh"]
    ident = checkout_identity(rhroot, BRANCHES["RH"])
    report["roots"]["RH"] = ident
    script = rhroot / "scripts/check_alpoge_rh_original_native_admission.py"
    if not ident["ok"] or not script.is_file():
        report["checks"].append({"owner": "RH", "status": "NOT_RUN",
                                 "reason": "wrong branch, dirty or missing native runner"})
    else:
        command = [sys.executable, str(script),
          "--external-root", str(args.rh_source_root.resolve()),
          "--tree-manifest", str(args.rh_manifest.resolve()),
          "--main-sha256", args.rh_main_sha256,
          "--lake", args.lake]
        r = call(command, rhroot, args.timeout)
        report["checks"].append({"owner": "RH",
          "status": "PASS" if r["exit"] == 0 else "FAIL", "result": r})
    report["fully_accepted"] = (len(report["checks"]) == 8
        and all(v.get("ok", False) for v in report["roots"].values())
        and all(v.get("status") == "PASS" for v in report["checks"]))
    out = args.report.resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n", encoding="utf8")
    print("ALL-CLAY SECTION36 NATIVE",
          "PASS" if report["fully_accepted"] else "FAIL",
          "checks", len(report["checks"]), "receipt", out)
    return 0 if report["fully_accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
