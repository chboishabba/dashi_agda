#!/usr/bin/env python3
"""Exact R815/R823 finite-Fourier feasibility witness (independent verifier).

Computes the R230 mixed-helicity commutator and its product-rule fold, the
R692 global coherent work, the R744 critical production, and the critical
viscous rate on the nonzero radius-one Fourier cube.

Interpretation uses R700/R722/R723 combined = 12 * commutator work and the
R815 identity at canonical viscosity/margin nu=delta=1:

    complete_rate = 6 * (combined - production + dissipation).

A negative value is an exact *instantaneous* Fourier calculation. Full
promotion to the live R408 trajectory and failure of the integrated universal
R823 payment requires same-object reification plus finite-dimensional ODE
short-time continuity. This diagnostic makes NO Clay conclusion.
"""
from __future__ import annotations
import json
from functools import lru_cache
from itertools import product
from sympy import I, Matrix, Rational, S, conjugate, expand, simplify, sqrt

MODES = tuple(k for k in product(range(-1, 2), repeat=3) if k != (0, 0, 0))
ZERO = Matrix([0, 0, 0])
SEEDS = {
    (1, 0, 0): Matrix([0, 2 + 2*I, -2 - I]),
    (0, 1, 0): Matrix([2 + 2*I, 0, 2 + 2*I]),
    (1, 1, 0): Matrix([3*I/2, -3*I/2, -2 + 2*I]),
}


def neg(k): return tuple(-v for v in k)
def sub(k, p): return tuple(x-y for x,y in zip(k,p))
def vec(k): return Matrix(k)


def projection(k, v):
    if k == (0, 0, 0): return ZERO
    x = vec(k)
    return v - x * (x.dot(v) / x.dot(x))


def dyadic_weight(k):
    n = max(map(abs, k))
    return S(2) ** ((n - 1).bit_length())


def exact_snapshot():
    u = {k: ZERO for k in MODES}
    for k, v in SEEDS.items():
        u[k] = v
        u[neg(k)] = v.applyfunc(conjugate)
    assert all(u[neg(k)] == u[k].applyfunc(conjugate) for k in MODES)
    assert all(vec(k).dot(u[k]) == 0 for k in MODES)

    @lru_cache(None)
    def force(k):
        out = Matrix([0, 0, 0])
        for p in MODES:
            q = sub(k, p)
            if q in u and u[p] != ZERO and u[q] != ZERO:
                out += u[p].dot(vec(q)) * u[q]
        return -I * projection(k, out)

    @lru_cache(None)
    def hel(k, force_flag, sign):
        v = force(k) if force_flag else u[k]
        if v == ZERO: return ZERO
        kv = vec(k)
        return (projection(k, v) + sign * I * kv.cross(v) / sqrt(kv.dot(kv))) / 2

    comm_work = S.Zero
    product_work = S.Zero
    for k in MODES:
        mixed = ZERO
        comm = ZERO
        product_rule = ZERO
        for p in MODES:
            q = sub(k, p)
            if q not in u: continue
            pm = hel(p, False, 1)
            qm = hel(q, False, -1)
            pf = hel(p, True, 1)
            mixed += pm.cross(qm)
            comm += pf.cross(qm) - hel(p, True, -1).cross(hel(q, False, 1))
            product_rule += pf.cross(qm) + pm.cross(hel(q, True, -1))
        if mixed != ZERO:
            comm_work += sum(conjugate(mixed[j])*comm[j] for j in range(3))
            product_work += sum(conjugate(mixed[j])*product_rule[j] for j in range(3))

    comm_work = simplify(expand(comm_work).as_real_imag()[0])
    product_work = simplify(expand(product_work).as_real_imag()[0])
    production = simplify(2 * sum(
        dyadic_weight(k) *
        sum(conjugate(u[k][j])*force(k)[j] for j in range(3)).as_real_imag()[0]
        for k in MODES
    ))
    dissipation = simplify(sum(
        dyadic_weight(k) * sum(z*z for z in k) *
        sum(conjugate(u[k][j])*u[k][j] for j in range(3))
        for k in MODES
    ))
    combined = 12 * comm_work
    signed_rate = simplify(6 * (combined - production + dissipation))
    assert simplify(comm_work - (-142 - Rational(59, 2)*sqrt(2))) == 0
    assert simplify(product_work - comm_work) == 0
    assert production == 0
    assert dissipation == 108
    assert signed_rate == -9576 - 2124*sqrt(2)
    assert signed_rate < 0
    return {
        "schema": "ns_r823_exact_sparse_snapshot.v1",
        "nonzero_initial_modes": {str(k): list(map(str, v)) for k,v in SEEDS.items()},
        "cutoff_cube_radius": 1,
        "nonzero_output_mode_count": len(MODES),
        "fourier_reality": True,
        "fourier_transversality": True,
        "r230_commutator_work": str(comm_work),
        "r230_product_rule_work": str(product_work),
        "r230_fibre_sum_agreement": bool(simplify(product_work-comm_work)==0),
        "critical_production": str(production),
        "critical_dissipation": str(dissipation),
        "viscosity": "1",
        "margin": "1",
        "r723_combined_twelve_commutator": str(combined),
        "r815_complete_instantaneous_rate": str(signed_rate),
        "strict_negative_instantaneous_rate": bool(signed_rate < 0),
        "kernel_certified": False,
        "r408_live_trajectory_reification": False,
        "integrated_falsification_certified": False,
    }


if __name__ == "__main__":
    print(json.dumps(exact_snapshot(), indent=2))
