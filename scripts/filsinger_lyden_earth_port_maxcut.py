#!/usr/bin/env python3
"""Filsinger/Lyden Earth-port CONDITIONAL numerical max-cut.
Pure Python assertions. No electrical frequency, Earth harvesting, or antenna geometry is claimed.
"""
from math import pi, sqrt, isclose

C_WHITE = 3.33e-6    # F, narrated
C_BLUE = 2.0e-6      # F, tentative label reading ONLY
V_TARGET = 1500.0    # V, narrated
P_INPUT = 6.7        # W, reported; conditional assumption that it is measured real input
F_AUDIO = 7800.0     # Hz, audio; NOT verified electronic switching frequency
F_SCHUMANN = 7.83    # Hz, comparator only


def stored_energy(c, v):
    return c * v * v / 2


def ideal_fill_time(c, v, p):
    return stored_energy(c, v) / p


def full_recharge_power(c, v, f):
    return stored_energy(c, v) * f


def ideal_collection_capacitance(p, voltage_swing, f):
    """C needed for 0.5*C*(delta V)^2*f=p assuming full replenish/reset each period."""
    return 2 * p / (voltage_swing**2 * f)


def maximal_new_voltage(c, initial_v, source_p, f):
    """Positive charging increment in one period, all source energy into C."""
    return sqrt(initial_v**2 + 2 * source_p / (c * f)) - initial_v


def budget_ok(drive, ambient, useful, loss):
    return isclose(drive + ambient, useful + loss, abs_tol=1e-12)


def test():
    assert isclose(stored_energy(C_WHITE, V_TARGET), 3.74625)
    assert isclose(ideal_fill_time(C_WHITE, V_TARGET, P_INPUT), 0.559141791044776)
    assert isclose(full_recharge_power(C_WHITE, V_TARGET, F_AUDIO), 29220.75)
    assert isclose(C_WHITE * V_TARGET * F_AUDIO, 38.961)
    assert isclose(sqrt(2*P_INPUT/(C_WHITE*F_AUDIO)), 22.7134435060, rel_tol=1e-8)
    assert isclose(maximal_new_voltage(C_WHITE, V_TARGET, P_INPUT, F_AUDIO), 0.1719569822, rel_tol=1e-8)
    assert isclose(ideal_collection_capacitance(P_INPUT,V_TARGET,F_AUDIO), 7.635327635327635e-10)
    assert isclose(ideal_collection_capacitance(P_INPUT,V_TARGET,F_SCHUMANN), 7.606073506456649e-7)
    assert isclose(full_recharge_power(100e-12,V_TARGET,F_AUDIO), 0.8775)
    assert isclose(1/((2*pi*F_AUDIO)**2*C_WHITE), 0.00012502786766, rel_tol=1e-8)
    assert budget_ok(6.7,0.0,2.0,4.7)
    assert budget_ok(6.7,1.0,2.0,5.7)
    assert not isclose(F_AUDIO/F_SCHUMANN,1000.0,rel_tol=1e-4)
    print("PASS: 12 conditional Filsinger/Lyden physics-budget checks")
    print("WARNING: these numerical checks do not validate source attribution or circuit connectivity")


if __name__ == "__main__":
    test()
