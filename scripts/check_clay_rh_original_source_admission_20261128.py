#!/usr/bin/env python3
"""Fail-closed source-handoff audit for isolated RHAdmission.lean.

Does not claim RH, trust downloaded source, or replace Lean's kernel.
The original submission and exact SHA-256 must be provided independently.
"""
import argparse
import hashlib
from pathlib import Path
import re

APIS = (
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
)

def audit(main: Path, expected_hash: str) -> None:
    if not re.fullmatch(r"[a-fA-F0-9]{64}", expected_hash):
        raise ValueError("An explicit pinned 64-digit SHA-256 is required")
    if not main.is_file():
        raise FileNotFoundError(main)
    raw = main.read_bytes()
    got = hashlib.sha256(raw).hexdigest()
    if got.lower() != expected_hash.lower():
        raise ValueError(f"SHA-256 mismatch: got {got}")
    data = raw.decode("utf-8")
    # Negative lexical gate; no source inspection can establish axiom freedom.
    for name in ("sorry", "admit", "native_decide", "unsafe"):
        if re.search(r"(?<![\w])" + name + r"(?![\w])", data):
            raise ValueError(f"Manual inspection required: token {name}")
    for symbol in APIS:
        if not re.search(r"\b" + re.escape(symbol) + r"\b", data):
            raise ValueError(f"Expected original export not present: {symbol}")
    print(f"Source bytes and declared export names verified: {got}")
    print("NEXT REQUIRED: exact dependency/toolchain pins, Lean 4.33.1 build, #print axioms, kernel audit.")
    print("NOT an RH proof acceptance receipt.")

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--main", type=Path, required=True)
    ap.add_argument("--sha256", required=True)
    args = ap.parse_args()
    audit(args.main, args.sha256)
