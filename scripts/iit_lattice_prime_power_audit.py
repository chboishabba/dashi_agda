#!/usr/bin/env python3
"""DASHI prime-power lattice audit: exact finite arithmetic, not IIT Phi.

Independent of the repo's IIT scalar evaluator. Same physical coordinate law
as iit_ternary_lattice_scaling.py: (F x)(c) = sum_axis x(c+e_axis) mod prime.
Analytic identity on a periodic n=p^k lattice:
    F^n = (dimension mod p) I,
from commuting cyclic shifts and the characteristic-p Frobenius identity.
The identity has NOT been compiled into an Agda general theorem here.
"""
from __future__ import annotations
import argparse
from itertools import product
from math import comb
from hashlib import sha256
import json

def indexing(n, d):
    coords = tuple(product(range(n), repeat=d))
    return coords, {c: i for i, c in enumerate(coords)}

def sources(n, d):
    coords, lookup = indexing(n, d)
    return [[lookup[c[:a] + ((c[a]+1) % n,) + c[a+1:]]
             for a in range(d)] for c in coords]

def matrix(n, d, p):
    neighbors = sources(n, d)
    size = len(neighbors)
    result = [[0] * size for _ in range(size)]
    for i, source_indices in enumerate(neighbors):
        for j in source_indices:
            result[i][j] = (result[i][j] + 1) % p
    return result

def rank(rows, p):
    a = [row[:] for row in rows]
    m = len(a)
    r = 0
    for c in range(m):
        pivot = next((j for j in range(r, m) if a[j][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inverse = pow(a[r][c], -1, p)
        a[r] = [(v * inverse) % p for v in a[r]]
        for j in range(r + 1, m):
            fac = a[j][c]
            if fac:
                a[j] = [(v - fac * w) % p for v, w in zip(a[j], a[r])]
        r += 1
        if r == m:
            break
    return r

def step(state, neighbors, p):
    return [sum(state[j] for j in row) % p for row in neighbors]

def delta_iterate(n, d, p, steps):
    neighbors = sources(n, d)
    state = [0] * (n ** d)
    state[0] = 1
    for _ in range(steps):
        state = step(state, neighbors, p)
    return state

def operator_equals_scalar(n, d, p, steps, scalar):
    neighbors = sources(n, d)
    size = n ** d
    for column in range(size):
        state = [0] * size
        state[column] = 1
        for _ in range(steps):
            state = step(state, neighbors, p)
        if any(v != (scalar if i == column else 0)
               for i, v in enumerate(state)):
            return False
    return True

def audit():
    rows = []
    for p in (2, 3):
        for d in (2, 3):
            for n in range(2, 11 if d == 2 else 6):
                N = n ** d
                rk = rank(matrix(n, d, p), p)
                entry = dict(p=p, dim=d, n=n, sites=N, rank=rk, kernel=N-rk)
                if d == 2:
                    # Fixed two shift law: F2 kernel n at all sizes;
                    # F3 kernel n iff n even, otherwise injective.
                    assert N-rk == (n if p == 2 or n % 2 == 0 else 0), entry
                rows.append(entry)
    cases = [(2,2,2),(2,2,4),(2,2,8),(2,3,2),(2,3,4),
             (3,2,3),(3,2,9),(3,3,3)]
    certificates = []
    for p, d, n in cases:
        assert all(comb(n, j) % p == 0 for j in range(1, n))
        assert operator_equals_scalar(n, d, p, n, d % p), (p, d, n)
        certificates.append(dict(p=p, dim=d, n=n, sites=n**d,
                                 power=n, scalar=d%p, all_basis_vectors=True))
    # Counterexamples to promoting small-grid extinction to arbitrary size.
    n3_initial = delta_iterate(3, 2, 2, 1)
    assert any(n3_initial)
    assert delta_iterate(3, 2, 2, 4) == n3_initial
    assert any(delta_iterate(10, 2, 2, 128))
    result = {
        "contract": "iit_lattice_prime_power_audit",
        "scope": "rank_and_dynamics_not_phi_not_full_CES",
        "source_semantics": "periodic east+south (2D) or three-axis addition (3D)",
        "rows": rows,
        "closed_form": "2D F2 kernel n; 2D F3 kernel n for even n, 0 for odd n",
        "prime_power_operator_certificates": certificates,
        "binary_2D_n3_F4_equals_F_on_delta": True,
        "binary_2D_n10_F128_delta_is_nonzero": True,
        "not_historical_physical_grid": True,
        "analytic_million_site_landmarks_not_matrix_runs": {
            "binary_2D_side_1000": {
                "sites": 1000**2, "rank": 1000**2-1000,
                "nullity": 1000, "non_nilpotent": True,
                "same_as_2014_majority_gate_example": False,
            },
            "binary_2D_side_1024": {
                "sites": 1024**2, "rank": 1024**2-1024,
                "nullity": 1024, "all_states_zero_by_step_1024": True,
                "reason": "Frobenius for n=2^10; no million-site matrix allocated",
            },
        },
        "general_agda_kernel_receipt": False,
    }
    blob = json.dumps(result, sort_keys=True, separators=(",", ":")).encode()
    result["payload_sha256"] = sha256(blob).hexdigest()
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", default="")
    args = parser.parse_args()
    result = audit()
    print(json.dumps({k:v for k,v in result.items() if k != "rows"},
                     indent=2, sort_keys=True))
    if args.json:
        with open(args.json, "w", encoding="utf-8") as f:
            json.dump(result, f, indent=2, sort_keys=True)
