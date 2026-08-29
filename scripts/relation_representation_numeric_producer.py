#!/usr/bin/env python3
"""Deterministic tiny numerical producer for relation-representation receipts.

This is an executable fixture, not an LLM experiment. It computes the same
finite spectral / SVD / rotation / affine / local-sensitivity values reified by
DASHI.Reasoning.FiniteRelationLinearAlgebraProducerExact and
DASHI.Reasoning.FiniteRelationSVDJacobianProducerExact.

No NumPy dependency is required so the receipt can run in the focused CI lane.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "Artifacts" / "relation-representation" / "numeric-producer-receipt.json"


def transpose(m):
    return [list(row) for row in zip(*m)]


def matmul(a, b):
    bt = transpose(b)
    return [[sum(x * y for x, y in zip(row, col)) for col in bt] for row in a]


def matvec(a, x):
    return [sum(c * v for c, v in zip(row, x)) for row in a]


def add_vec(a, b):
    return [x + y for x, y in zip(a, b)]


def sqerr(xs, ys):
    return sum((a - b) ** 2 for x, y in zip(xs, ys) for a, b in zip(x, y))


def gram(rows):
    return matmul(transpose(rows), rows)


def square(n):
    return n * n


def forward_difference(f, n):
    return f(n + 1) - f(n)


def build_receipt():
    residuals = [[3, 0], [0, 1]]
    gram_matrix = gram(residuals)

    # For this diagonal Gram matrix the eigensystem is exact over the integers.
    eigenpairs = [
        {"vector": [1, 0], "eigenvalue": 9},
        {"vector": [0, 1], "eigenvalue": 1},
    ]
    for pair in eigenpairs:
        assert matvec(gram_matrix, pair["vector"]) == [
            pair["eigenvalue"] * v for v in pair["vector"]
        ]

    # Literal exact SVD of X = diag(3,1): U=I, Sigma=diag(3,1), V=I.
    identity = [[1, 0], [0, 1]]
    singular_values = [3, 1]
    sigma = [[3, 0], [0, 1]]
    reconstructed = matmul(matmul(identity, sigma), transpose(identity))
    svd_reconstruction_error = sqerr(reconstructed, residuals)
    assert svd_reconstruction_error == 0
    assert singular_values[0] ** 2 == eigenpairs[0]["eigenvalue"]
    assert singular_values[1] ** 2 == eigenpairs[1]["eigenvalue"]

    rotation = [[0, -1], [1, 0]]
    rotation_inputs = [[1, 0], [0, 1], [-1, 0], [0, -1]]
    rotation_outputs = [matvec(rotation, x) for x in rotation_inputs]
    expected_rotation_outputs = [[0, 1], [-1, 0], [0, -1], [1, 0]]
    rotation_error = sqerr(rotation_outputs, expected_rotation_outputs)

    affine_matrix = [[2, 0], [0, 3]]
    affine_bias = [1, 2]
    affine_input = [2, 3]
    affine_output = add_vec(matvec(affine_matrix, affine_input), affine_bias)
    expected_affine_output = [5, 11]
    affine_error = sqerr([affine_output], [expected_affine_output])

    fd_points = [2, 3]
    fd_values = [forward_difference(square, n) for n in fd_points]

    return {
        "schema": "dashi.relation-representation.numeric-producer.v1",
        "purpose": "deterministic finite producer fixture; not an empirical LLM/ethics result",
        "spectral": {
            "residuals": residuals,
            "gram": gram_matrix,
            "eigenpairs": eigenpairs,
            "spectral_gap": eigenpairs[0]["eigenvalue"] - eigenpairs[1]["eigenvalue"],
        },
        "svd": {
            "matrix": residuals,
            "u": identity,
            "singular_values": singular_values,
            "v": identity,
            "reconstruction_error": svd_reconstruction_error,
        },
        "rotation": {
            "matrix": rotation,
            "inputs": rotation_inputs,
            "outputs": rotation_outputs,
            "squared_error": rotation_error,
        },
        "affine": {
            "matrix": affine_matrix,
            "bias": affine_bias,
            "input": affine_input,
            "output": affine_output,
            "squared_error": affine_error,
        },
        "finite_difference": {
            "map": "n -> n^2",
            "points": fd_points,
            "forward_differences": fd_values,
            "state_dependent": fd_values[0] != fd_values[1],
        },
    }


def main():
    actual = build_receipt()
    encoded = json.dumps(actual, indent=2, sort_keys=True) + "\n"

    if "--print" in sys.argv:
        sys.stdout.write(encoded)
        return 0

    expected = FIXTURE.read_text(encoding="utf-8")
    if encoded != expected:
        sys.stderr.write("numeric producer receipt differs from committed fixture\n")
        sys.stderr.write(encoded)
        return 1

    print("relation-representation numeric producer receipt: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
