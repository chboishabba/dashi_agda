#!/usr/bin/env python3
"""Section43 all-Clay native campaign, fail closed, exact owner checkouts.

Every source and acceptance root is committed on its OWN PR branch.
This runner checks original native Agda/Lean files in independently
provided worktrees, records actual exit codes and Git HEADs, and never
turns a symbolic Python check into a kernel receipt.

Usage (replace placeholders with genuine original SHA pins):
  python scripts/check_clay_section36_native_campaign.py
    --ym-root /checkout/dashi_agda_ym
    --ns-root /checkout/dashi_lean4_ns
    --bsd-hodge-root /checkout/dashi_lean4_bsd
    --pnp-root /checkout/dashi_lean4_pnp
    --rh-root /checkout/dashi_lean4_rh
    --agda-include /checkout/stdlib
    --agda-include /checkout/bishop
    --rh-source-root /checkout/pinned_external_rh
    --rh-manifest /checkout/sha256_manifest.json
    --rh-main-sha256 <64-hex-main-pin>
    --rh-source-head <40-hex-external-source-commit>
    --require-head YM=<40-hex-commit>
    --require-head NS=<40-hex-commit>
    --require-head BSD_HODGE=<40-hex-commit>
    --require-head PNP=<40-hex-commit>
    --require-head RH=<40-hex-commit>
    --report /checkout/dashi_agda_rollup/Docs/receipts/ClaySection43Native.json

The arguments are shown on separate lines for readability; pass them
in ONE shell command (or put literal shell line-continuation characters
between the lines). The runner does NOT guess SHA pins from branch names.

Return 0 ONLY when every SELECTED source entrypoint completes native
elaboration and RH source admission at immutable pinned HEADs.
A PASS does NOT establish any universal Millennium conjecture. Missing inputs, dirty checkout,
wrong branches or failed source check make the overall result FAIL.
Do not claim the returned report is committed: the runner writes a
new receipt and the owner must add/commit its exact bytes afterward.
"""
from __future__ import annotations
import argparse
import json
import re
from pathlib import Path
import subprocess
import sys

ROOTS = {
 "YM": ("ym_root", [
  "DASHI/Physics/YangMills/YMClayCMP102Section33WeightedCauchyClosureAcceptanceExact.agda",
  "DASHI/Physics/YangMills/YMClayCMP102Section34FactorialMassAcceptanceExact.agda",
  "DASHI/Physics/YangMills/YMClayCMP102Section35ThreeWingOrderAcceptanceExact.agda",
  "DASHI/Physics/YangMills/YMClayCMP102Section37NoZeroPremiseAcceptanceExact.agda",
  "DASHI/Physics/YangMills/YMClayCMP102Section38LastBCoefficientAcceptanceExact.agda",
  "DASHI/Physics/YangMills/YMClayCMP102Section39TwoOuterWingsAcceptanceExact.agda",
  "DASHI/Physics/YangMills/YMClayCMP102Section42OriginalShiftedDegreeAcceptanceExact.agda",
  "DASHI/Physics/YangMills/YMClayCMP102Section43PowerFactorAcceptanceExact.agda",
 ]),
 "NS": ("ns_root", [
  "Synthesis/ClayNSSection36FullSameFlowCompactnessAcceptanceExact.lean",
  "Synthesis/ClayNSSection38EpsilonRadiusAcceptanceExact.lean",
  "Synthesis/ClayNSSection39UniformRadiusAllCutoffsAcceptanceExact.lean",
  "Synthesis/ClayNSSection42DiagonalShellPrecisionAcceptanceExact.lean",
  "Synthesis/ClayNSSection43RadiusLinearCostAcceptanceExact.lean",
 ]),
 "BSD_HODGE": ("bsd_hodge_root", [
  "Synthesis/ClayBSDSection36AllDegreeMellinEnvelopeAcceptanceExact.lean",
  "Synthesis/ClayHodgeSection36AllPowersSaturationAcceptanceExact.lean",
  "Synthesis/ClayBSDSection37SymmetricMomentFloorAcceptanceExact.lean",
  "Synthesis/ClayHodgeSection37TwoLiftSaturationAcceptanceExact.lean",
  "Synthesis/ClayBSDSection39StrictPositiveDegreeFloorAcceptanceExact.lean",
  "Synthesis/ClayHodgeSection39OriginalQ0PartnerAcceptanceExact.lean",
  "Synthesis/ClayBSDSection40MonotoneMellinAcceptanceExact.lean",
  "Synthesis/ClayHodgeSection40AllSixQ0PartnerAcceptanceExact.lean",
  "Synthesis/ClayHodgeSection41OriginalCoupledSixDeckAcceptanceExact.lean",
  "Synthesis/ClayHodgeSection42WholeEvenDeckAcceptanceExact.lean",
  "Synthesis/ClayBSDSection42OriginalCrossingSwapAcceptanceExact.lean",
  "Synthesis/ClayBSDSection43SignedMomentOrientationAcceptanceExact.lean",
  "Synthesis/ClayHodgeSection43CentralDeckQ0WeldAcceptanceExact.lean",
 ]),
 "PNP": ("pnp_root", [
  "Welds/PNPSection36SameObligationInputVsWorkAcceptanceExact.lean",
  "Welds/PNPSection37ExternalObservationAcceptanceExact.lean",
  "Welds/PNPSection38PreterminalExternalObservationAcceptanceExact.lean",
  "Welds/PNPSection39PairedPreterminalSplitAcceptanceExact.lean",
  "Welds/PNPSection40OriginalFinClockAcceptanceExact.lean",
  "Welds/PNPSection41OriginalCausalBitReadAcceptanceExact.lean",
  "Welds/PNPSection42OriginalFiniteBlockReadAcceptanceExact.lean",
  "Welds/PNPSection43AdaptiveBlockReadAcceptanceExact.lean",
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
                "stderr_tail": p.stderr[-5000:],
                "_stdout_full": p.stdout, "_stderr_full": p.stderr}
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {"command": cmd, "exit": None, "error": str(exc)}


def checkout_identity(root: Path, expected: str) -> dict:
    if not root.is_dir():
        return {"ok": False, "error": "checkout missing"}
    worktree = call(["git", "rev-parse", "--is-inside-work-tree"], root, 20)
    if worktree.get("exit") != 0 or worktree.get("stdout_tail", "").strip() != "true":
        return {"ok": False, "error": "not a Git worktree"}
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


def lean_axioms_trusted(output: str, source: str) -> tuple[bool, str]:
    """Reject Lean successes with missing, unknown or unsafe axiom audits.

    Parses the native #print axioms output for ALL explicitly requested
    declarations, not just any incidental occurrence of a familiar word.
    No proof status can be inferred from an empty or unparsable log.
    """
    requested = re.findall(
        r"(?m)^\s*#print\s+axioms\s+([\w.]+)\s*$", source)
    if not requested:
        return False, "missing #print axioms in source"
    allow = {"propext", "Classical.choice", "Quot.sound"}
    for declaration in requested:
        leaf = re.escape(declaration)
        matches = re.findall(
            r"(?m)^\s*'?" + leaf +
            r"'?\s+depends on axioms:\s*\[([^]]*)\]\s*$", output)
        empties = re.findall(
            r"(?m)^\s*'?" + leaf +
            r"'?\s+does not depend on any axioms\s*$", output)
        if len(matches) + len(empties) != 1:
            return False, "missing/ambiguous axiom audit: " + declaration
        actual = {a.strip() for a in matches[0].split(",")
                  if a.strip()} if matches else set()
        unknown = actual - allow
        if unknown:
            return False, "nontrusted axioms in " + declaration + ": " + repr(sorted(unknown))
    return True, "all native Lean axiom reports allowlisted"


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
    p.add_argument("--rh-source-head", required=True,
                   help="immutable 40-hex external original RH Git HEAD pin")
    p.add_argument("--report", type=Path, required=True)
    p.add_argument("--require-head", action="append", default=[],
        metavar="OWNER=COMMIT_SHA",
        help="Mandatory immutable Git HEAD pin, once per YM,NS,BSD_HODGE,PNP,RH")
    p.add_argument("--timeout", type=int, default=90)
    args = p.parse_args()
    report = {"schema": "Clay43NativeAcceptanceV1",
              "all_selected_roots_passed": False, "roots": {}, "checks": [],
              "meaning": "Selected finite theorem roots only; not universal Clay completion"}
    pins = {}
    for item in args.require_head:
        if "=" not in item:
            p.error("--require-head must be OWNER=40_HEX_SHA")
        owner, sha = item.split("=", 1)
        if owner not in ("YM", "NS", "BSD_HODGE", "PNP", "RH") or \
                len(sha) != 40 or any(c not in "0123456789abcdef" for c in sha):
            p.error("Invalid owner or SHA in --require-head")
        if owner in pins:
            p.error("Duplicate --require-head owner")
        pins[owner] = sha
    if set(pins) != {"YM", "NS", "BSD_HODGE", "PNP", "RH"}:
        p.error("Fail closed: all five original owner HEAD pins are REQUIRED")
    roots = {key: Path(getattr(args, key.lower()+"_root")).resolve()
             for key in ("ym", "ns", "pnp", "rh")}
    roots["bsd_hodge"] = args.bsd_hodge_root.resolve()
    for owner, (attr, paths) in ROOTS.items():
        root = roots[attr.removesuffix("_root")]
        ident = checkout_identity(root, BRANCHES[owner])
        ident["required_HEAD"] = pins[owner]
        ident["ok"] = bool(ident["ok"] and ident.get("HEAD") == pins[owner])
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
            trusted = True
            audit = "Agda --safe"
            if owner != "YM" and result["exit"] == 0:
                trusted, audit = lean_axioms_trusted(
                    result.get("_stdout_full", "") + "\n" + result.get("_stderr_full", ""),
                    (root / path).read_text(encoding="utf8"))
            result.pop("_stdout_full", None)
            result.pop("_stderr_full", None)
            report["checks"].append({"owner": owner, "path": path,
                     "status": "PASS" if result["exit"] == 0 and trusted else "FAIL",
                     "axiom_audit": audit,
                     "result": result})
    rhroot = roots["rh"]
    ident = checkout_identity(rhroot, BRANCHES["RH"])
    ident["required_HEAD"] = pins["RH"]
    ident["ok"] = bool(ident["ok"] and ident.get("HEAD") == pins["RH"])
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
          "--expected-git-head", args.rh_source_head,
          "--lake", args.lake]
        r = call(command, rhroot, args.timeout)
        r.pop("_stdout_full", None)
        r.pop("_stderr_full", None)
        report["checks"].append({"owner": "RH",
          "status": "PASS" if r["exit"] == 0 else "FAIL", "result": r})
    report["all_selected_roots_passed"] = (len(report["checks"]) == sum(len(owner_paths) for _, owner_paths in ROOTS.values()) + 1
        and all(v.get("ok", False) for v in report["roots"].values())
        and all(v.get("status") == "PASS" for v in report["checks"]))
    out = args.report.resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n", encoding="utf8")
    print("ALL-CLAY SECTION43 SELECTED ROOTS",
          "PASS" if report["all_selected_roots_passed"] else "FAIL",
          "checks", len(report["checks"]), "receipt", out)
    return 0 if report["all_selected_roots_passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
