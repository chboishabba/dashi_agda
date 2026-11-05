#!/usr/bin/env python3
"""Exact F4 root-grading bracket audit for the Albert derivation algebra.

Consumes the exact Q(i) Cartan projectors from `albert_f4_exact_weight_probe.py`.
For each of the 48 one-dimensional nonzero weight/root spaces it selects one
exact derivation matrix.  Across all C(48,2)=1128 unordered root pairs it checks:

* if alpha+beta is a root, [g_alpha,g_beta] is nonzero and proportional to the
  selected generator of g_(alpha+beta);
* if beta=-alpha, the bracket is nonzero and lies in the four-dimensional
  Cartan span;
* otherwise the bracket is exactly zero.

Observed exact partition:

    408 root-sum nonzero brackets
     24 opposite-root Cartan brackets
    696 forbidden-sum zero brackets
   ----
   1128 total unordered pairs.

All arithmetic is exact SymPy Q(i); no floating point is used.
"""

from itertools import combinations
import sympy as sp
from albert_f4_exact_weight_probe import (
    build_data, representation_matrix, joint_projector,
    d4_weights, vector_weights, spin_weights,
)


def root_matrix(basis_mats, projector):
    coeff = None
    for j in range(projector.cols):
        candidate = projector[:,j]
        if any(x != 0 for x in candidate):
            coeff = candidate
            break
    if coeff is None:
        raise AssertionError('rank-one projector had no nonzero column')
    out = sp.zeros(27,27)
    for c,M in zip(coeff,basis_mats):
        out += c*M
    if out == sp.zeros(27,27):
        raise AssertionError('selected root vector vanished')
    return sp.simplify(out)


def proportional_nonzero(left, right):
    a = left.reshape(729,1)
    b = right.reshape(729,1)
    pivot = next((i for i,x in enumerate(b) if x != 0), None)
    if pivot is None:
        return False
    scale = sp.simplify(a[pivot] / b[pivot])
    if scale == 0:
        return False
    return all(sp.simplify(a[i] - scale*b[i]) == 0 for i in range(729))


def main():
    mats, Hfull = build_data()
    reps = {name:[representation_matrix(H,mats[name]) for H in Hfull]
            for name in mats}

    roots = {}
    for w in d4_weights():
        roots[tuple(map(sp.Rational,w))] = root_matrix(
            mats['so8'], joint_projector(reps['so8'],w,'so8'))
    for w in vector_weights():
        roots[tuple(map(sp.Rational,w))] = root_matrix(
            mats['V'], joint_projector(reps['V'],w,'V'))
    for w in spin_weights(+1):
        roots[tuple(w)] = root_matrix(
            mats['S+'], joint_projector(reps['S+'],w,'spin'))
    for w in spin_weights(-1):
        roots[tuple(w)] = root_matrix(
            mats['S-'], joint_projector(reps['S-'],w,'spin'))

    assert len(roots) == 48

    # Exact Cartan span solver.
    Hflat = sp.Matrix.hstack(*[H.reshape(729,1) for H in Hfull])
    _, pivots = Hflat.T.rref()
    pivots = list(pivots[:4])
    Hminor = Hflat[pivots,:]
    Hinv = Hminor.inv()

    def cartan_nonzero(A):
        if A == sp.zeros(27,27):
            return False
        flat = A.reshape(729,1)
        coeff = Hinv * sp.Matrix([flat[i] for i in pivots])
        reconstruction = Hflat * coeff
        return all(sp.simplify(reconstruction[i]-flat[i]) == 0
                   for i in range(729))

    zero = (sp.Rational(0),)*4
    root_sum_nonzero = 0
    opposite_cartan = 0
    forbidden_zero = 0

    keys = list(roots)
    for ia,alpha in enumerate(keys):
        for beta in keys[ia+1:]:
            bracket = sp.simplify(
                roots[alpha]*roots[beta] - roots[beta]*roots[alpha])
            weight_sum = tuple(sp.simplify(a+b) for a,b in zip(alpha,beta))
            if weight_sum in roots:
                root_sum_nonzero += 1
                if not proportional_nonzero(bracket, roots[weight_sum]):
                    raise AssertionError(
                        f'root-sum bracket mismatch: {alpha}+{beta}')
            elif weight_sum == zero:
                opposite_cartan += 1
                if not cartan_nonzero(bracket):
                    raise AssertionError(
                        f'opposite-root bracket missed Cartan: {alpha},{beta}')
            else:
                forbidden_zero += 1
                if bracket != sp.zeros(27,27):
                    raise AssertionError(
                        f'forbidden root sum had nonzero bracket: {alpha}+{beta}')

    assert root_sum_nonzero == 408
    assert opposite_cartan == 24
    assert forbidden_zero == 696
    assert root_sum_nonzero + opposite_cartan + forbidden_zero == 1128

    print('scalar_field=Q(i)')
    print('root_spaces=48x1')
    print('unordered_root_pairs=1128')
    print('root_sum_nonzero_brackets=408')
    print('opposite_root_cartan_brackets=24')
    print('forbidden_sum_zero_brackets=696')
    print('root_grading_exact=true')
    print('floating_point_used=false')


if __name__ == '__main__':
    main()
