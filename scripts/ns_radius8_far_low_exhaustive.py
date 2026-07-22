#!/usr/bin/env python3
"""Exhaustive finite Fourier-core far-low translation-matrix diagnostic."""
from __future__ import annotations
import argparse, hashlib, json
from fractions import Fraction
from pathlib import Path
from typing import Any
from ns_periodic_concrete_proof_program import hat_multiplier, modes, q, vadd, vmax, far_low_certificate

SCHEMA = "ns_radius8_far_low_exhaustive.v1"

def digest(x: Any) -> str:
    return hashlib.sha256(json.dumps(x, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

def build(K: int = 3, R: int = 2) -> dict[str, Any]:
    low = list(modes(2 ** (K - R)))
    high = list(modes(2 ** (K + 1)))
    mq = {v: hat_multiplier(K, v) for v in high}
    worst = Fraction(0); witness = None; checked = 0
    for p in low:
        wp = vmax(p)
        for v in high:
            k = vadd(p, v); checked += 1
            ratio = abs(hat_multiplier(K, k) - mq[v]) / wp
            if ratio > worst:
                worst = ratio; witness = {"p": p, "q": v, "k": k}
    slope = Fraction(1, 2 ** (K - 1))
    payload = {
        "schema": SCHEMA,
        "authority": "exhaustive_finite_core_plus_symbolic_R8_gain",
        "K": K, "R": R,
        "low_mode_count": len(low), "high_mode_count": len(high),
        "checked_pairs": checked,
        "observed_weighted_matrix_bound": q(worst),
        "analytic_hat_lipschitz_bound": q(slope),
        "row_bound": q(worst), "column_bound": q(worst),
        "enumeration_below_analytic": worst <= slope,
        "witness": witness,
        "R8_symbolic": far_low_certificate(8),
        "promotion": {"official_norm_identified": False, "universal_far_low": False},
    }
    payload["sha256"] = digest(payload)
    return payload

def main() -> None:
    ap=argparse.ArgumentParser(); ap.add_argument('--output-json',type=Path,required=True); ap.add_argument('--pretty',action='store_true'); a=ap.parse_args()
    p=build(); a.output_json.parent.mkdir(parents=True,exist_ok=True); t=json.dumps(p,sort_keys=True,indent=2 if a.pretty else None)+'\n'; a.output_json.write_text(t); print(t,end='')
if __name__=='__main__': main()
