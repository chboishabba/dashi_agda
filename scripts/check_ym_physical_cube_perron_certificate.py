#!/usr/bin/env python3
"""Exact rational weighted Dobrushin/Perron cube certificate.

This checks a claimed INFLUENCE MATRIX from one selected physical cube:
   C >= 0, w > 0, 0 <= q < 1, C w <= q w.
Then C^n w <= q^n w for every natural n follows by positivity.
A full physical result additionally requires SAME original R445 Gibbs
conditional rows, bounds C_ij on their total-variation influences,
fixed physical cube size across every UV cutoff and thermodynamic volume,
reflection-compatible block-iteration, and selected CMP116/J observables.

No sample matrix in this file is a measured/derived Wilson SU(N) matrix.
Do NOT promote numeric fixture PASS to physical mass gap or Clay.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from math import log
from pathlib import Path

def rational(x):
    if isinstance(x, float):
        raise ValueError("Float not allowed: use exact rational strings")
    return Fraction(str(x))

def validate(data, require_physical=False):
    matrix = [[rational(x) for x in row] for row in data["influence_matrix"]]
    weights = [rational(x) for x in data["positive_weights"]]
    q = rational(data["uniform_contraction"])
    side = rational(data["physical_cube_side"])
    n = len(weights)
    if n == 0 or len(matrix) != n or any(len(row) != n for row in matrix):
        raise ValueError("non-square matrix or empty weights")
    if side <= 0 or not (0 <= q < 1) or any(w <= 0 for w in weights):
        raise ValueError("physical side, strict q or Perron weights invalid")
    if any(c < 0 for row in matrix for c in row):
        raise ValueError("negative entry in influence upper-bound matrix")
    if "cutoff_schedules" not in data or not data["cutoff_schedules"]:
        raise ValueError("missing non-vacuous scale family")
    for item in data["cutoff_schedules"]:
        lattice_spacing = rational(item["lattice_spacing"])
        count = item["cube_cells"]
        if not isinstance(count, int) or count <= 0 or lattice_spacing <= 0:
            raise ValueError("invalid cube calibration")
        if lattice_spacing * count != side:
            raise ValueError("cube side NOT fixed in physical units")
    if require_physical:
        proof = data.get("source_receipt", {})
        for key in ("repository", "original_gibbs_owner", "original_holonomy_owner",
                    "source_commit", "cutoff_uniform_bound_proof", "positive_time_compatibility_proof"):
            if not proof.get(key):
                raise ValueError(f"physical source missing: {key}")
        if data.get("illustrative", True):
            raise ValueError("illustrative certificate cannot pass physical admission")
    weighted = [sum(c*w for c,w in zip(row,weights)) for row in matrix]
    ratios = [a/w for a,w in zip(weighted, weights)]
    for i,ratio in enumerate(ratios):
        if ratio > q:
            raise ValueError(f"weighted Perron inequality failed at row {i}: {ratio} > {q}")
    return matrix,weights,q,side,ratios

def matvec(matrix,vector):
    return [sum(c*w for c,w in zip(row,vector)) for row in matrix]

def check(data, *, require_physical=False, powers=12):
    matrix,w,q,side,ratios=validate(data, require_physical)
    vector=list(w)
    # Exact negative-side oscillation amplification is not allowed.
    for k in range(powers+1):
        assert all(x <= (q**k)*upper for x,upper in zip(vector,w)),("power",k)
        vector=matvec(matrix,vector)
    return {
       "status":"PASS_EXACT_RATIONAL_INFLUENCE_CERTIFICATE",
       "physical_proof_status":"NOT_ESTABLISHED_BY_MATRIX_CERTIFICATE",
       "rows":len(w),
       "uniform_q":str(q),
       "physical_cube_side":str(side),
       "max_weighted_row_ratio":str(max(ratios)),
       "max_power_checked":powers,
       "physical_mass_gap_lower_bound_illustration":(-log(float(q))/float(side)
          if q>0 else "infinite_if_exact_zero"),
       "same_original_source_attested": bool(require_physical),
       "scope":"C^k w <= q^k w (all k follows by exact induction)"
    }

def fixture():
    return {
      "illustrative":True,
      "influence_matrix":[["1/8","1/8",0,0],
                          ["1/12","1/4","1/12",0],
                          [0,"1/12","1/4","1/12"],
                          [0,0,"1/8","1/8"]],
      "positive_weights":["1","1","1","1"],
      "uniform_contraction":"1/2",
      "physical_cube_side":"1",
      "cutoff_schedules":[
          {"cube_cells":2,"lattice_spacing":"1/2"},
          {"cube_cells":4,"lattice_spacing":"1/4"},
          {"cube_cells":8,"lattice_spacing":"1/8"}]
    }

def selftest():
    good=fixture()
    out=check(good,powers=24)
    assert out["max_weighted_row_ratio"] == "5/12"
    def rejects(bad):
        try: check(bad)
        except (ValueError,AssertionError): return
        raise AssertionError("unsafe certificate passed")
    for mutation in (
       lambda a:a.update(uniform_contraction="1"),
       lambda a:a["influence_matrix"][1].__setitem__(1,"3/4"),
       lambda a:a["positive_weights"].__setitem__(0,"0"),
       lambda a:a["cutoff_schedules"][1].update(lattice_spacing="1/8"),
       lambda a:a["influence_matrix"][0].__setitem__(0,"-1/8"),
       lambda a:a.update(cutoff_schedules=[])):
        from copy import deepcopy
        bad=deepcopy(good)
        mutation(bad)
        rejects(bad)
    try: check(good,require_physical=True)
    except ValueError: pass
    else: raise AssertionError("illustrative data promoted to original physical")
    return {"selftest":"PASS", "exhaustive_negative_controls":7, **out}

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--input",type=Path)
    p.add_argument("--physical",action="store_true")
    p.add_argument("--selftest",action="store_true")
    p.add_argument("--powers",type=int,default=12)
    args=p.parse_args()
    if args.selftest or not args.input:
        print(json.dumps(selftest(),indent=2))
    else:
        print(json.dumps(check(json.loads(args.input.read_text()),
               require_physical=args.physical,powers=args.powers),indent=2))

if __name__=="__main__":
    main()
