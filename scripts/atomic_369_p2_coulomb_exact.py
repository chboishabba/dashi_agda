#!/usr/bin/env python3
"""Exact projected Coulomb matrix on the spin-polarized hydrogenic 2p^2 sector.

Attribution boundary
--------------------
* Hydrogenic 2p radial-function normalization remains the NIST-DLMF role
  already attributed by the parent atomic PR.
* The Coulomb kernel, Laplace multipole expansion and spherical-harmonic/Gaunt
  algebra are standard mathematical physics ingredients.  This script is a
  DASHI reconstruction/execution of their composition; it is not an external
  experimental result and does not identify the finite ternary carrier with
  the microscopic atom.

The selected carrier is the common-spin antisymmetric orbital basis
  |-1 ^ 0>, |-1 ^ +1>, |0 ^ +1>.
For R_21(r) = r exp(-r/2)/(2 sqrt(6)) in atomic units, the exact Slater radial
integrals are F^0=93/512 and F^2=45/512.  Exact Gaunt algebra then gives
V_ee=(21/128) I_3 on this antisymmetric p^2 sector.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp
from sympy.physics.wigner import gaunt

OUT = Path("generated/atomic_369_p2_coulomb_receipt.json")

r1, r2 = sp.symbols("r1 r2", positive=True)


def radial_density(r: sp.Symbol) -> sp.Expr:
    # r^2 |R_21(r)|^2 in a0=1, Z=1 atomic units.
    return r**4 * sp.exp(-r) / 24


def slater_radial(k: int) -> sp.Rational:
    inner = sp.integrate(radial_density(r2) * r2**k, (r2, 0, r1))
    return sp.simplify(
        2 * sp.integrate(radial_density(r1) * inner / r1 ** (k + 1), (r1, 0, sp.oo))
    )


def minus_one_pow(n: int) -> sp.Integer:
    return sp.Integer(-1) ** n


def angular_factor(a: int, k: int, q: int, c: int, conjugate_k: bool) -> sp.Expr:
    """Integral <Y_1a | Y_kq^(*) | Y_1c> using exact Gaunt coefficients."""
    phase = minus_one_pow(a)
    mq = q
    if conjugate_k:
        phase *= minus_one_pow(q)
        mq = -q
    return sp.simplify(phase * gaunt(1, k, 1, -a, mq, c))


F = {0: slater_radial(0), 2: slater_radial(2)}


def eri(a: int, b: int, c: int, d: int) -> sp.Expr:
    total = sp.Integer(0)
    for k in (0, 2):
        for q in range(-k, k + 1):
            total += (
                4 * sp.pi / sp.Integer(2 * k + 1)
                * F[k]
                * angular_factor(a, k, q, c, True)
                * angular_factor(b, k, q, d, False)
            )
    return sp.simplify(total)


BASIS = [(-1, 0), (-1, 1), (0, 1)]
V = sp.Matrix(
    3,
    3,
    lambda i, j: sp.simplify(
        eri(BASIS[i][0], BASIS[i][1], BASIS[j][0], BASIS[j][1])
        - eri(BASIS[i][0], BASIS[i][1], BASIS[j][1], BASIS[j][0])
    ),
)

# The induced wedge^2 action for e_- -> e_0 -> e_+ -> e_- in the ordered
# basis above.
U2 = sp.Matrix([[0, -1, 0], [0, 0, -1], [1, 0, 0]])
COMM = sp.simplify(V * U2 - U2 * V)
EXPECTED = sp.eye(3) * sp.Rational(21, 128)

if F[0] != sp.Rational(93, 512):
    raise RuntimeError(f"unexpected F0: {F[0]}")
if F[2] != sp.Rational(45, 512):
    raise RuntimeError(f"unexpected F2: {F[2]}")
if V != EXPECTED:
    raise RuntimeError(f"unexpected Coulomb matrix: {V}")
if COMM != sp.zeros(3):
    raise RuntimeError(f"C3 commutator not zero: {COMM}")

receipt = {
    "scope": "hydrogenic Z=1 2p^2 common-spin antisymmetric orbital sector",
    "basis": ["m=-1 wedge m=0", "m=-1 wedge m=+1", "m=0 wedge m=+1"],
    "radial_slater_integrals": {"F0": str(F[0]), "F2": str(F[2])},
    "projected_coulomb_matrix": [[str(V[i, j]) for j in range(3)] for i in range(3)],
    "induced_wedge2_c3_matrix": [[str(U2[i, j]) for j in range(3)] for i in range(3)],
    "commutator": [[str(COMM[i, j]) for j in range(3)] for i in range(3)],
    "exact_result": "V_ee = (21/128) I_3",
    "attribution": {
        "hydrogenic_radial_source_role": "NIST DLMF role inherited from parent atomic tranche",
        "gaunt_coulomb_composition": "DASHI exact symbolic reconstruction using standard multipole/Gaunt algebra",
        "experimental_authority": False,
        "full_atom_369_identity": False,
    },
}

OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps(receipt, indent=2))
