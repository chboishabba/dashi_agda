"""Recover the exact pressure multiplier from ORIGINAL R734 six-mode full NS source.

Classical incompressible NSE pressure Poisson/Leray relation, not a new
regularity theorem. Reuse R734's same N=2, divergence-free helical datum.
"""
from collections import defaultdict
import sympy as S
from test_ns_r734_pure_plus_physical_w2_no_go import (
    K, minus, physical_u, projected_NS_nonlinearity, n2,
)


def convective_raw_and_pressure(u, cut=2):
    raw = defaultdict(lambda: S.zeros(3, 1))
    for p, v in u.items():
        for q, w in u.items():
            k = tuple(p[i] + q[i] for i in range(3))
            raw[k] += S.Matrix(q).dot(v) * w
    pressure = {}
    force = {}
    for k, v in raw.items():
        if n2(k) == 0 or max(map(abs, k)) > cut:
            continue
        wave = S.Matrix(k)
        # -Delta p = partial_i partial_j(u_i u_j);
        # p_hat = -k . raw / |k|^2 since div(u)=0.
        pressure[k] = S.simplify(-wave.dot(v) / n2(k))
        force[k] = -S.I * (v + wave * pressure[k])
    return pressure, force


def test_poisson_pressure_reconstructs_same_cutoff_leray_force():
    u = physical_u()
    pressure, force = convective_raw_and_pressure(u)
    target = projected_NS_nonlinearity(u, 2)
    assert pressure.keys() == target.keys() == force.keys()
    assert any(S.simplify(value) != 0 for value in pressure.values())
    for k in force:
        wave = S.Matrix(k)
        assert S.simplify(force[k] - target[k]) == S.zeros(3, 1)
        assert S.simplify(wave.dot(force[k])) == 0
        assert S.simplify(pressure[k] - S.conjugate(pressure[minus(k)])) == 0


def test_pressure_even_under_full_velocity_reversal():
    u = physical_u()
    v = {k: -a for k, a in u.items()}
    p, f = convective_raw_and_pressure(u)
    pflip, fflip = convective_raw_and_pressure(v)
    assert p.keys() == pflip.keys()
    for k in p:
        assert S.simplify(p[k] - pflip[k]) == 0
        assert S.simplify(f[k] - fflip[k]) == S.zeros(3, 1)


def test_modewise_phase_change_changes_pressure_despite_same_power():
    u = physical_u()
    v = {m: -a if m in (K, minus(K)) else a for m, a in u.items()}
    for m in u:
        assert S.simplify((S.conjugate(u[m]).T*u[m])[0]
                        - (S.conjugate(v[m]).T*v[m])[0]) == 0
    p, _ = convective_raw_and_pressure(u)
    pflip, _ = convective_raw_and_pressure(v)
    assert p.keys() == pflip.keys()
    assert any(S.simplify(p[k] - pflip[k]) != 0 for k in p)


def test_pressure_gradient_has_zero_curl_in_every_selected_mode():
    p, _ = convective_raw_and_pressure(physical_u())
    for k, value in p.items():
        wave = S.Matrix(k)
        assert S.simplify(wave.cross(-S.I * wave * value)) == S.zeros(3, 1)
