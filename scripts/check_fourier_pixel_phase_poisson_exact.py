#!/usr/bin/env python3
"""Exact 4x4 finite Fourier--Poisson phase-gradient audit, no device claims.

Glauser et al., Nature 655 (2026) Methods (30)-(31): solve finite-grid
Laplacian phi = div(m), with zero frequency fixed to 0 (phase gauge).
This script is an independent finite torus Z4 x Z4 toy and does not claim to
reproduce the actual camera boundary conditions or measured noisy dataset.
"""
import json
from fractions import Fraction

N = 4
Z = (Fraction(0), Fraction(0))
ONE = (Fraction(1), Fraction(0))
I = (Fraction(0), Fraction(1))
ROOTS = [ONE, (Fraction(0), Fraction(-1)), (Fraction(-1), Fraction(0)), I]

def plus(a, b):
    return (a[0] + b[0], a[1] + b[1])

def mul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])

def scale(q, a):
    return (q * a[0], q * a[1])

def conjugate(a):
    return (a[0], -a[1])

def negate(a):
    return (-a[0], -a[1])

def sub(a, b):
    return plus(a, negate(b))

def zeros():
    return [[Z for _ in range(N)] for _ in range(N)]

def dft2(a, inverse=False):
    result = zeros()
    for ky in range(N):
        for kx in range(N):
            v = Z
            for y in range(N):
                for x in range(N):
                    phase = ROOTS[(kx * x + ky * y) % N]
                    if inverse:
                        phase = conjugate(phase)
                    v = plus(v, mul(a[y][x], phase))
            result[ky][kx] = scale(Fraction(1, N*N), v) if inverse else v
    return result

def fields_equal(a, b):
    return all(a[y][x] == b[y][x] for y in range(N) for x in range(N))

def gradient(phi):
    dx = [[sub(phi[y][(x+1)%N], phi[y][x]) for x in range(N)] for y in range(N)]
    dy = [[sub(phi[(y+1)%N][x], phi[y][x]) for x in range(N)] for y in range(N)]
    return dx, dy

def divergence(dx, dy):
    return [[plus(sub(dx[y][x], dx[y][(x-1)%N]),
                  sub(dy[y][x], dy[(y-1)%N][x])) for x in range(N)] for y in range(N)]

def curl(dx, dy):
    return [[sub(plus(dx[y][x], dy[y][(x+1)%N]),
                 plus(dx[(y+1)%N][x], dy[y][x])) for x in range(N)] for y in range(N)]

def poisson_from_gradient(dx, dy):
    spec = dft2(divergence(dx, dy))
    recovered = zeros()
    lambda_1 = [0, -2, -4, -2]  # 2*cos(2*pi*k/4)-2, exact
    for ky in range(N):
        for kx in range(N):
            lap_eigenvalue = lambda_1[kx] + lambda_1[ky]
            if lap_eigenvalue:
                recovered[ky][kx] = scale(Fraction(1, lap_eigenvalue), spec[ky][kx])
            else:
                # This fixes the unobservable global phase / constant mode.
                assert (kx, ky) == (0, 0)
                assert spec[ky][kx] == Z
    return dft2(recovered, inverse=True)

def field_minus(a, b):
    return [[sub(a[y][x], b[y][x]) for x in range(N)] for y in range(N)]

def normsquared(a):
    return sum((a[y][x][0]**2 + a[y][x][1]**2 for y in range(N) for x in range(N)), Fraction(0))

def main():
    phi = [[(Fraction((3*x+2*y+x*y) % 7)-Fraction(3, 2), Fraction(0))
            for x in range(N)] for y in range(N)]
    mean = scale(Fraction(1, N*N), tuple(sum((phi[y][x][i] for y in range(N) for x in range(N)), Fraction(0)) for i in range(2)))
    zero_mean_phi = [[sub(phi[y][x], mean) for x in range(N)] for y in range(N)]
    assert fields_equal(dft2(dft2(phi), inverse=True), phi)
    dx, dy = gradient(phi)
    reconstructed = poisson_from_gradient(dx, dy)
    assert fields_equal(reconstructed, zero_mean_phi)
    assert fields_equal(curl(dx, dy), zeros())
    # Same observed gradients after an arbitrary global phase offset:
    shifted = [[plus(phi[y][x], (Fraction(7,3), Fraction(0))) for x in range(N)] for y in range(N)]
    shift_dx, shift_dy = gradient(shifted)
    assert fields_equal(dx, shift_dx) and fields_equal(dy, shift_dy)
    assert fields_equal(poisson_from_gradient(shift_dx, shift_dy), reconstructed)
    # Non-exact edge observation: a single horizontal edge is perturbed.
    noisy_dx = [[dx[y][x] for x in range(N)] for y in range(N)]
    noisy_dx[0][0] = plus(noisy_dx[0][0], ONE)
    loop_curl = curl(noisy_dx, dy)
    assert loop_curl[0][0] == ONE
    projected_phi = poisson_from_gradient(noisy_dx, dy)
    grad_proj_x, grad_proj_y = gradient(projected_phi)
    residual_x, residual_y = field_minus(noisy_dx, grad_proj_x), field_minus(dy, grad_proj_y)
    residual_energy = normsquared(residual_x)+normsquared(residual_y)
    assert residual_energy > 0
    assert fields_equal(divergence(residual_x, residual_y), zeros())
    assert not fields_equal(noisy_dx, grad_proj_x)
    # Precise meaning: the Laplacian reconstruction commutes on exact gradients,
    # but its output is the least-squares gradient projection for inconsistent data.
    print(json.dumps({
        "scope":"exact synthetic 4x4 periodic torus, not measured optics",
        "dft2_roundtrip":True,
        "poisson_gradient_gauge_fixed_square":True,
        "global_phase_unobservable":True,
        "exact_gradient_curl_zero":True,
        "single_edge_error_curl_at_origin":str(loop_curl[0][0][0]),
        "inconsistent_edges_reproduce_exact_gradient":False,
        "inconsistent_projection_residual_energy":str(residual_energy),
        "projected_residual_is_divergence_free":True,
    },sort_keys=True,indent=2))

if __name__ == '__main__':
    main()
