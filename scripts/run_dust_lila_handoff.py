#!/usr/bin/env python3
"""Single fail-closed handoff for the existing Dust <-> Sovereign-LILA runner.

No trainer is reimplemented. Default preflight uses only Python stdlib.
--run-analogue requires torch; --run-real requires a user-provided upstream
checkout and executes the *existing* source-specific E8GPT runner.
Dust: Dahal/Mandal/Gülbahar/Vegesna. E8GPT: SPUTNIKAI.
DASHI owns this orchestration/audit. Not full-model training.
"""
from __future__ import annotations
import argparse
import ast
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REQUIRED = (
    "sovereign_lila_dust_projection_step.py",
    "check_sovereign_lila_dust_projection_contract.py",
    "run_sovereign_lila_e8_dust_smoke.py",
    "audit_noise_record_source_identity.py",
)
def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lila-checkout", type=Path)
    ap.add_argument("--run-analogue", action="store_true",
                    help="Run existing CPU shape-compatible Torch smoke")
    ap.add_argument("--run-real", action="store_true",
                    help="Run existing real-E8GPT synthetic-token smoke")
    ap.add_argument("--noise-checkout", type=Path,
                    help="Optionally verify both pinned Noise record sources")
    ap.add_argument("--checkpoint", type=Path,
                    help="Optional trusted E8GPT state dict for --run-real")
    args = ap.parse_args()
    failures = []
    sources = {}
    for rel in REQUIRED:
        path = HERE / rel
        if not path.is_file():
            failures.append(f"missing sibling {rel}")
            continue
        try:
            ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
            sources[rel] = "syntax-ok"
        except (SyntaxError, UnicodeError) as e:
            failures.append(f"cannot parse {rel}: {e}")
    if args.run_real and args.run_analogue:
        failures.append("select one executable target, not both")
    if args.checkpoint and not args.run_real:
        failures.append("--checkpoint requires --run-real")
    if args.run_real:
        if args.lila_checkout is None:
            failures.append("--run-real requires --lila-checkout")
        elif not (args.lila_checkout / "models" / "model.py").is_file():
            failures.append("original E8GPT checkout missing models/model.py")
        elif not (args.lila_checkout / "config" / "config.py").is_file():
            failures.append("original E8GPT checkout missing config/config.py")
        if args.checkpoint and not args.checkpoint.is_file():
            failures.append("checkpoint file not found")
    if args.noise_checkout and not args.noise_checkout.is_dir():
        failures.append("Noise checkout directory not found")
    print(json.dumps({"preflight": "PASS" if not failures else "BLOCKED",
                      "sources": sources, "failures": failures,
                      "original_model_executed": False}, indent=2))
    if failures:
        return 2
    if args.noise_checkout:
        command = [sys.executable, str(HERE / "audit_noise_record_source_identity.py"),
                   "--noise-checkout", str(args.noise_checkout)]
        if subprocess.call(command) != 0:
            return 3
    if args.run_analogue:
        return subprocess.call([sys.executable,
                                str(HERE / "check_sovereign_lila_dust_projection_contract.py")])
    if args.run_real:
        command = [sys.executable, str(HERE / "run_sovereign_lila_e8_dust_smoke.py"),
                   "--lila-checkout", str(args.lila_checkout)]
        if args.checkpoint:
            command += ["--checkpoint", str(args.checkpoint)]
        return subprocess.call(command)
    print("Preflight only. Pass --run-analogue or --run-real --lila-checkout PATH to execute.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
