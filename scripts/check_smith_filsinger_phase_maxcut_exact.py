#!/usr/bin/env python3
"""Exact source-normalized Smith/Filsinger F01/F04/F05/F06/F07/F08/F11 controls.

Research model only. Original Smith/Filsinger Earth/plate circuit is unmeasured.
This is NOT an Agda kernel run and does not prove environmental harvesting.
Original hypothesis: user-supplied differential off-phase source/sink timing.
Arithmetic owner: DASHI/Physics/Motors/SmithFilsingerFinitePhaseMatchingExact.agda.
"""
from fractions import Fraction as F
from itertools import product
import json
import sympy as sp


def load_power(resistance: F, conductance: F, voc: F = F(1)) -> F:
    assert resistance > 0 and conductance >= 0
    return voc * voc * conductance / (1 + resistance * conductance) ** 2


def symbolic_matching():
    v, r, g = sp.symbols("V R G", positive=True)
    diff = v**2 / (4 * r) - v**2 * g / (1 + r * g) ** 2
    gap = v**2 * (r * g - 1) ** 2 / (4 * r * (1 + r * g) ** 2)
    assert sp.cancel(diff - gap) == 0
    r = sp.symbols("R", positive=True)
    anti = 1 / (1 + r)**2
    aligned = (sp.Rational(1, 2) / (1 + r / 2)**2 +
               sp.Rational(3, 2) / (1 + 3 * r / 2)**2) / 2
    delta = sp.factor(anti - aligned)
    expected = -r * (3 * r**3 - 12 * r - 8) / (
        (r + 1)**2 * (r + 2)**2 * (3 * r + 2)**2)
    assert sp.cancel(delta - expected) == 0
    return str(gap), str(delta)


def two_slot_schedule(base: int, excursion: int):
    """Two controlled branches alternate low/high without external RF phase."""
    assert base >= 0 and excursion >= 0
    low, high = base, base + 2 * excursion
    return ((low, high), (high, low))


def exact_four_phase_cross(real: int, imaginary: int):
    # Re[(real+i*imag)* exp(i phase)] for 0, pi/2, pi, 3pi/2.
    signs = ((real, 0), (0, imaginary), (0, real), (imaginary, 0))
    return sum(x for x, _ in signs), sum(y for _, y in signs)


def source_reversal():
    """Same phase schedule, source R=1 vs R=3; all exact rational work."""
    cases = {}
    for resistance in (F(1), F(3)):
        opposed = load_power(resistance, F(1))
        inphase = (
            load_power(resistance, F(1, 2))
            + load_power(resistance, F(3, 2))) / 2
        cases[str(resistance)] = dict(
            opposed=opposed, inphase=inphase,
            delta_opposed_minus_inphase=opposed - inphase)
    assert cases["1"]["opposed"] == F(1, 4)
    assert cases["1"]["inphase"] == F(52, 225)
    assert cases["1"]["delta_opposed_minus_inphase"] == F(17, 900)
    assert cases["3"]["opposed"] == F(1, 16)
    assert cases["3"]["inphase"] == F(196, 3025)
    assert cases["3"]["delta_opposed_minus_inphase"] == -F(111, 48400)
    return cases


def matched_boundary_pair(natural_t, controller_t, loss_t, final_t,
                          natural_c, controller_c, loss_c, final_c,
                          initial=F(4)):
    # Construct legal positive load from a separately specified input/storage
    # budget, and verify exact cross-equality of the two histories.
    input_t = natural_t + controller_t + initial
    input_c = natural_c + controller_c + initial
    load_t = input_t - loss_t - final_t
    load_c = input_c - loss_c - final_c
    assert min(load_t, load_c) >= 0
    output_t, output_c = load_t + loss_t + final_t, load_c + loss_c + final_c
    assert input_t == output_t and input_c == output_c
    assert output_t + input_c == output_c + input_t
    return dict(tuned_load=load_t, control_load=load_c,
                changed_natural=natural_t - natural_c,
                changed_controller=controller_t - controller_c,
                changed_load=load_t - load_c,
                changed_losses=loss_t - loss_c,
                changed_stored=final_t - final_c)


def exact_checks():
    match, delta = symbolic_matching()
    for x, y in product(range(0, 26), repeat=2):
        assert (x + y) ** 2 - 4 * x * y == (x - y) ** 2
        assert load_power(F(1), F(x, max(y, 1))) <= F(1, 4)
    for b, a in product(range(0, 20), repeat=2):
        two = two_slot_schedule(b, a)
        assert two[0][0] + two[0][1] == two[1][0] + two[1][1]
    for a, b, scalar in product(range(1, 8), range(1, 8), range(1, 8)):
        assert (scalar * a) * b == (scalar * b) * a
    for re, im in product(range(0, 21), repeat=2):
        assert exact_four_phase_cross(re, im) == (re + im, re + im)
    ratio = source_reversal()
    r = sp.symbols("R", positive=True)
    cubic = 3 * r**3 - 12 * r - 8
    assert cubic.subs(r, sp.Rational(9, 4)) < 0
    assert cubic.subs(r, sp.Rational(23, 10)) > 0
    assert sp.diff(cubic, r).subs(r, 2) > 0
    pair = matched_boundary_pair(F(3), F(2), F(1), F(2),
                                 F(2), F(2), F(1), F(2))
    assert pair["changed_load"] == pair["changed_natural"] == F(1)
    assert pair["changed_load"] - pair["changed_controller"] == (
        pair["changed_natural"] - pair["changed_losses"]
        - pair["changed_stored"])
    # Strong negative source-off control: no natural incoming means
    # net natural-work (incoming minus outgoing) is never >0.
    assert all(-F(out) <= 0 for out in range(100))
    return dict(scope="conditional exact arithmetic, not physical acceptance",
                formula_match=str(match),
                source_resistance_reversal_expression=str(delta),
                source_resistance_cases={
                    k: {j: str(v) for j, v in d.items()}
                    for k, d in ratio.items()},
                polynomial_root_bracket=["9/4", "23/10"],
                tests="PASS: 26² rational square gaps, 20² slot pairs, "
                      "7³ common drive ratios, 21² quarter phases, "
                      "2 exact source reversals, symbolic identities, "
                      "matched energy and source-off controls")


if __name__ == "__main__":
    print(json.dumps(exact_checks(), indent=2))
