#!/usr/bin/env python3
"""P01/P02/P07/P08 exact reference: original event access, rational KK
Schur/horizontal metric, and observer-unitary/Euclidean-contract no-go.

This is an independent source-convention test only; it is NOT Agda kernel
acceptance, a continuous Lorentzian metric, physical KK action, OS proof,
or a Yang--Mills Clay theorem. Another worker owns YM R443--R333.
"""
from fractions import Fraction as F
from itertools import product
import random

EVENTS = ("preparation", "intermediate", "terminal")
LEVELS = ("initial", "intermediate", "terminal")
VISIBLE = {
    "initial": (True, False, False),
    "intermediate": (True, True, False),
    "terminal": (True, True, True),
}


def precedes(a, b):
    return all(not ea or eb for ea, eb in zip(VISIBLE[a], VISIBLE[b]))


def check_original_access():
    for a, b, c in product(LEVELS, repeat=3):
        if precedes(a, b) and precedes(b, c):
            assert precedes(a, c)
    assert all(precedes(a, a) for a in LEVELS)
    assert all(
        not (precedes(a, b) and precedes(b, a))
        for a, b in product(LEVELS, repeat=2) if a != b
    )
    for a, b in (("initial", "intermediate"),
                 ("intermediate", "terminal"), ("initial", "terminal")):
        assert precedes(a, b) and not precedes(b, a)
        assert any((not ea) and eb for ea, eb in zip(VISIBLE[a], VISIBLE[b]))
    print("PASS: original 3-level causal-access 27 transitivity cases "
          "and 3 strict event witnesses")


def dot(u, v):
    return sum((x * y for x, y in zip(u, v)), F(0))


def actual_four_bilinear(u, v):
    return -u[0] * v[0] + dot(u[1:], v[1:])


def connection(u):
    return F(1, 3) * u[0] - F(2, 5) * u[2]


def d_lambda(u):
    return -F(5, 7) * u[1] + F(2, 9) * u[3]


def kk_five(g4, gauge_a, r2, u, s, v, t):
    return g4(u, v) + r2 * (s + gauge_a(u)) * (t + gauge_a(v))


def check_kk_horizontal():
    rng = random.Random(2048)
    checked = 0
    for _ in range(8000):
        u = tuple(F(rng.randint(-8, 8), rng.randint(1, 8))
                  for _ in range(4))
        v = tuple(F(rng.randint(-8, 8), rng.randint(1, 8))
                  for _ in range(4))
        s = F(rng.randint(-8, 8), rng.randint(1, 8))
        t = F(rng.randint(-8, 8), rng.randint(1, 8))
        r2 = F(rng.randint(1, 8), rng.randint(1, 8))
        g = actual_four_bilinear
        a = connection
        assert kk_five(g, a, r2, u, -a(u), v, -a(v)) == g(u, v)
        expanded = g(u, v) + r2 * (
            a(u) * a(v) + a(u) * t + s * a(v) + s * t
        )
        assert kk_five(g, a, r2, u, s, v, t) == expanded
        assert kk_five(g, a, r2, u, F(0), v, F(0)) == (
            g(u, v) + r2 * a(u) * a(v)
        )
        shifted = lambda w: a(w) + d_lambda(w)
        assert kk_five(
            g, shifted, r2, u, s - d_lambda(u), v, t - d_lambda(v)
        ) == kk_five(g, a, r2, u, s, v, t)
        assert -(a(u) + d_lambda(u)) == -a(u) - d_lambda(u)
        checked += 5

    timelike = (F(1), F(0), F(0), F(0))
    assert connection(timelike) != 0
    assert kk_five(
        actual_four_bilinear, connection, F(2),
        timelike, F(0), timelike, F(0)
    ) != actual_four_bilinear(timelike, timelike)
    print(f"PASS: {checked:,} exact rational KK horizontal/Schur, "
          "connection/gauge and non-naive-fibre cases")


def check_time_no_go():
    vacuum, positive, negative = "vacuum", "positive", "negative"
    norm = {vacuum: 0, positive: 1, negative: 1}
    real_step = {vacuum: vacuum, positive: negative, negative: positive}
    euclidean_rank_drop = {vacuum: vacuum, positive: vacuum, negative: vacuum}
    for state in (vacuum, positive, negative):
        assert norm[real_step[state]] == norm[state]
    assert norm[euclidean_rank_drop[positive]] < norm[positive]
    assert real_step[positive] != euclidean_rank_drop[positive]
    print("PASS: exact 3-state norm-preserving vs contracting "
          "step-identity negative control (not finite-time OS exponential)")




# Additional P01->P02 / P02->P08 / P03->P07 max-cut checks.
# The two-level example is a FINITE Hilbert mathematical model, NOT the
# physically selected OS-reconstructed Hilbert of Yang-Mills.
import cmath


def check_actual_diamond_visibility_nonpromotion():
    levels = {"past": "initial", "x": "intermediate",
              "y": "intermediate", "z": "intermediate",
              "future": "terminal"}
    original_edges = (
        ("past", "x"), ("past", "y"), ("past", "z"),
        ("x", "future"), ("y", "future"), ("z", "future"),
        ("past", "future")
    )
    assert all(precedes(levels[a], levels[b]) for a, b in original_edges)
    assert levels["x"] == levels["y"] == levels["z"]
    # A single-valued decoder of a level cannot return x,y,z at once.
    assert len({"x", "y", "z"}) == 3
    assert len({levels[x] for x in ("x", "y", "z")}) == 1
    print("PASS: seven original-diamond causal edges respect observer "
          "access; spatial x/y/z cannot be reconstructed from the level")


def check_kk_shear_congruence():
    rng = random.Random(1317)
    count = 0
    for _ in range(5000):
        u = tuple(F(rng.randint(-7, 7), rng.randint(1, 7))
                  for _ in range(4))
        v = tuple(F(rng.randint(-7, 7), rng.randint(1, 7))
                  for _ in range(4))
        s = F(rng.randint(-7, 7), rng.randint(1, 7))
        t = F(rng.randint(-7, 7), rng.randint(1, 7))
        b2 = F(rng.randint(1, 7), rng.randint(1, 7))
        shear_u = (u, s + connection(u))
        shear_v = (v, t + connection(v))
        unshear_u = (shear_u[0], shear_u[1] - connection(shear_u[0]))
        assert unshear_u == (u, s)
        assert (u, (s - connection(u)) + connection(u)) == (u, s)
        decoupled = (
            actual_four_bilinear(shear_u[0], shear_v[0])
            + b2 * shear_u[1] * shear_v[1]
        )
        assert decoupled == kk_five(
            actual_four_bilinear, connection, b2, u, s, v, t
        )
        assert (-connection(u)) + connection(u) == 0
        count += 4
    print(f"PASS: {count:,} exact rational invertible-KK-shear "
          "and metric-congruence checks")


def check_noncollapsed_two_level_wick_stone_reference():
    # The real-time groups are U_obs(t)=exp(-it H_obs/hbar) and
    # U_os(t)=J U_obs(t) J^-1 on C^2, with actual H=(0,3/2).
    # This provides a genuinely noncollapsed 2D Hilbert CONTROL,
    # not an OS physical 4D YM reconstruction.
    hbar = 1.4
    energy = 1.5

    def J(vec):
        return (vec[1], vec[0])

    def evolve_obs(t, vec):
        return (vec[0], cmath.exp(-1j * t * energy / hbar) * vec[1])

    def evolve_os(t, vec):
        return J(evolve_obs(t, J(vec)))

    def energy_obs(vec):
        return (0j, energy * vec[1])

    def energy_os(vec):
        return J(energy_obs(J(vec)))

    def norm2(vec):
        return sum(abs(v) ** 2 for v in vec)

    psi = (0.6+0.2j, 0.3-0.7j)
    for t in (0, 0.1, 0.3, 1.2):
        assert max(abs(x-y) for x,y in zip(
            J(evolve_obs(t, psi)), evolve_os(t, J(psi)))) < 1e-12
        assert abs(norm2(evolve_obs(t, psi)) - norm2(psi)) < 1e-12
        assert J(energy_obs(psi)) == energy_os(J(psi))

    # Strong derivative and physical H=i*hbar*K, using actual
    # difference quotients, not an independent Hamiltonian label.
    def finite_derivative(t):
        evolved = evolve_obs(t, psi)
        return tuple((e - z)/t for e,z in zip(evolved, psi))

    target = tuple(-1j*x/hbar for x in energy_obs(psi))
    errors = [
        max(abs(a-b) for a,b in zip(finite_derivative(2**(-n)),target))
        for n in range(3, 16)
    ]
    assert all(errors[i+1] < errors[i] for i in range(len(errors)-1))
    for a,b in zip(J(target),tuple(-1j*x/hbar for x in energy_os(J(psi)))):
        assert abs(a-b) < 1e-12

    tau = 0.7
    epsi = (psi[0], cmath.exp(-tau*energy/hbar)*psi[1])
    assert norm2(epsi) < norm2(psi)
    # Real time is norm-preserving and Euclidean positive time contracts.
    assert abs(norm2(evolve_obs(tau, psi))-norm2(psi)) < 1e-12
    print("PASS: noncollapsed C^2 common-H, real-time unitary, "
          "OS-side conjugation, finite derivative and Euclidean contraction "
          "(analytic numerical control, not physical YM or Agda)")




def check_kk_backward_radius_nonidentifiability():
    """SOURCE negative control: same g4 and A, distinct strictly positive
    KK radii, identical horizontal reductions, different vertical readings.
    Does NOT establish 5D Einstein/radion equations or physical realizability.
    """
    rng = random.Random(5234)
    checked = 0
    for _ in range(6000):
        v = tuple(F(rng.randint(-9, 9), rng.randint(1, 9))
                  for _ in range(4))
        w = tuple(F(rng.randint(-9, 9), rng.randint(1, 9))
                  for _ in range(4))
        b1 = F(rng.randint(1, 8), rng.randint(1, 9))
        b2 = b1 + F(rng.randint(1, 8), rng.randint(1, 9))
        assert b1 > 0 and b2 > b1

        # Both physical candidates reduce to exactly the SAME g4,
        # including with a nonzero selected source connection.
        h1 = kk_five(
            actual_four_bilinear, connection, b1,
            v, -connection(v), w, -connection(w)
        )
        h2 = kk_five(
            actual_four_bilinear, connection, b2,
            v, -connection(v), w, -connection(w)
        )
        assert h1 == h2 == actual_four_bilinear(v, w)

        # The full 5D bilinear at a unit vertical displacement
        # re-identifies the discarded fibre-radius coordinate.
        p1 = kk_five(
            actual_four_bilinear, connection, b1,
            v, 1-connection(v), w, 1-connection(w)
        ) - actual_four_bilinear(v, w)
        p2 = kk_five(
            actual_four_bilinear, connection, b2,
            v, 1-connection(v), w, 1-connection(w)
        ) - actual_four_bilinear(v, w)
        assert p1 == b1 and p2 == b2 and p1 != p2
        checked += 4

    print(f"PASS: {checked:,} exact rational KK reverse-lift "
          "non-identifiability and vertical-radius recovery identities")




def check_kk_backward_chart_connection_nonidentifiability():
    """Original g4 forgets chart connection. Off-diagonal vertical
    5D readout retrieves local A(v). Gauge-related potentials can be
    physically equivalent, so this is NOT a physical gauge invariant.
    """
    rng = random.Random(6437)
    zero_a = lambda x: F(0)
    checked = 0
    for _ in range(6000):
        v = tuple(F(rng.randint(-9, 9), rng.randint(1, 9))
                  for _ in range(4))
        w = tuple(F(rng.randint(-9, 9), rng.randint(1, 9))
                  for _ in range(4))
        shift = F(rng.randint(1, 7), rng.randint(1, 7))
        def a2(x):
            return connection(x) + shift*x[0]
        b = F(rng.randint(1, 8), rng.randint(1, 9))
        for a in (zero_a, connection, a2):
            assert kk_five(
                actual_four_bilinear, a, b, v, -a(v), w, -a(w)
            ) == actual_four_bilinear(v, w)
            # At fixed b=1, the mixed fifth-circle cross-term
            # recovers the chart A(v) independently of A(w).
            mixed = kk_five(
                actual_four_bilinear, a, F(1), v, F(0), w, F(1)
            ) - kk_five(
                actual_four_bilinear, a, F(1), v, F(0), w, F(0)
            )
            assert mixed == a(v)
            checked += 2
    print(f"PASS: {checked:,} exact rational KK chart-connection "
          "non-injection and vertical offdiagonal readout checks "
          "(not gauge-invariant physical distinction)")




def check_selected_ket_hamiltonian_nonpromotion():
    """Two algebraic finite rational symmetric H have equal action on e0,
    but not on e1. Independent negative control: NOT physical OS H.
    """
    e0 = (F(1), F(0))
    e1 = (F(0), F(1))
    def h0(vec):
        return (F(0), F(0))
    def h1(vec):
        return (F(0), vec[1])
    def dot2(x, y):
        return x[0]*y[0] + x[1]*y[1]

    assert h0(e0) == h1(e0)
    assert h0(e1) != h1(e1)
    rng = random.Random(1541)
    checked = 0
    for _ in range(6000):
        x = tuple(F(rng.randint(-10,10),rng.randint(1,11))
                  for i in range(2))
        y = tuple(F(rng.randint(-10,10),rng.randint(1,11))
                  for i in range(2))
        assert dot2(x,h0(y)) == dot2(h0(x),y)
        assert dot2(x,h1(y)) == dot2(h1(x),y)
        checked += 2
    print(f"PASS: {checked:,} exact rational symmetry cases "
          "and selected-ket agreement/full-H disagreement control")


if __name__ == "__main__":
    check_original_access()
    check_kk_horizontal()
    check_time_no_go()
    check_actual_diamond_visibility_nonpromotion()
    check_kk_shear_congruence()
    check_kk_backward_radius_nonidentifiability()
    check_kk_backward_chart_connection_nonidentifiability()
    check_noncollapsed_two_level_wick_stone_reference()
    check_selected_ket_hamiltonian_nonpromotion()
    print("REFERENCE ONLY: NOT a physical/Agda/Stone/OS/Clay result")
