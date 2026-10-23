#!/usr/bin/env python3
"""Exact synthetic trace-chain arithmetic. NOT participant or neural DMT data."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from math import comb
import json

def multiply(a, b):
    assert len(a[0]) == len(b)
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]

def inverse(a):
    n = len(a)
    if not n:
        return []
    m = [[*row, *(F(i == j) for j in range(n))]
         for i, row in enumerate(a)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if m[i][j]), None)
        if pivot is None:
            raise ValueError("No finite first-return inverse; check recurrence")
        m[j], m[pivot] = m[pivot], m[j]
        d = m[j][j]
        m[j] = [x / d for x in m[j]]
        for i in range(n):
            if i != j:
                d = m[i][j]
                m[i] = [x - d*y for x, y in zip(m[i], m[j])]
    return [row[n:] for row in m]

def valid_stochastic(q):
    return (len(q) > 0 and all(len(row) == len(q)
        and all(x >= 0 for x in row) and sum(row) == 1 for row in q))

def trace(q, visible):
    """First-return kernel Q_VV + Q_VH (I-Q_HH)^-1 Q_HV, exact Fractions."""
    if not valid_stochastic(q):
        raise ValueError("Expected a finite row-stochastic kernel")
    v = list(visible)
    if not v or len(set(v)) != len(v) or not set(v) <= set(range(len(q))):
        raise ValueError("Visible set must contain unique valid indices")
    h = [i for i in range(len(q)) if i not in v]
    vv = [[q[i][j] for j in v] for i in v]
    if not h:
        return vv
    vh = [[q[i][j] for j in h] for i in v]
    hv = [[q[i][j] for j in v] for i in h]
    hh = [[F(i == j) - q[h[i]][h[j]] for j in range(len(h))]
          for i in range(len(h))]
    excursion = multiply(multiply(vh, inverse(hh)), hv)
    result = [[vv[i][j] + excursion[i][j] for j in range(len(v))]
              for i in range(len(v))]
    if not valid_stochastic(result):
        raise ValueError("Hidden states may not return to visible set a.s.")
    return result

def display_matrix(a):
    return [[str(x) for x in row] for row in a]

def kluever_form_partition(q):
    """Synthetic source-compatible *selected* Turing-to-form projections.

    The original relation is partial and many-to-one: stripes/spots/hexagons
    may project as lattice, a spiral family as spiral, and a front as tunnel
    or cobweb. This fixture picks one allowed outcome for each of four modes;
    it does not complete the source relation or predict an individual's DMT
    reports. First-return traces are NOT Markov lumping of these forms.
    """
    modes = ["stripe", "spot", "spiral", "front"]
    form = ["lattice", "lattice", "spiral", "tunnel"]
    assert len(q) == len(modes) == len(form)
    assert form[0] == form[1] and modes[0] != modes[1]
    outcomes = sorted(set(form))
    mass = {
        modes[i]: {target: sum(
            (q[i][j] for j in range(len(q)) if form[j] == target), F(0))
            for target in outcomes}
        for i in range(len(q))
    }
    # Lattice projects at states 0/1, but future observed-form laws differ.
    # E.g. Q(stripe -> tunnel)=1/10, Q(spot -> tunnel)=1/5.
    mismatch = mass["stripe"]["tunnel"] != mass["spot"]["tunnel"]
    assert mismatch
    # If a single one-step Markov transition row on observed forms existed,
    # both fine modes with current form='lattice' would have to share it.
    lumpable = all(
        mass[modes[i]] == mass[modes[j]]
        for i in range(len(q)) for j in range(len(q))
        if form[i] == form[j]
    )
    assert not lumpable

    # The distinction is not only failure of strong lumpability. With any
    # initial distribution assigning positive mass to spiral (state 2) and
    # tunnel (state 3), the actual observable conditional future differs:
    # P(Y2=tunnel | Y1=lattice,Y0=spiral) = 2/15;
    # P(Y2=tunnel | Y1=lattice,Y0=tunnel) = 7/50.
    # The unique first-form modes make the two conditioning events explicit.
    spiral_then_lattice = (
        q[2][0] * q[0][3] + q[2][1] * q[1][3]
    ) / (q[2][0] + q[2][1])
    tunnel_then_lattice = (
        q[3][0] * q[0][3] + q[3][1] * q[1][3]
    ) / (q[3][0] + q[3][1])
    assert spiral_then_lattice == F(2, 15)
    assert tunnel_then_lattice == F(7, 50)
    assert spiral_then_lattice != tunnel_then_lattice

    return {
        "modes": modes, "form_labels": form,
        "projection_is_selected_from_partial_relation": True,
        "lattice_has_distinct_preimages": True,
        "lattice_next_tunnel_mass_from_stripe": str(mass["stripe"]["tunnel"]),
        "lattice_next_tunnel_mass_from_spot": str(mass["spot"]["tunnel"]),
        "strong_lumpability": lumpable,
        "conditional_tunnel_after_spiral_lattice": str(spiral_then_lattice),
        "conditional_tunnel_after_tunnel_lattice": str(tunnel_then_lattice),
        "observed_form_history_changes_future": (
            spiral_then_lattice != tunnel_then_lattice),
        "one_step_form_only_markov_kernel_identified": lumpable,
        "trace_is_not_lumping": True,
    }

def binomial_one_sided_tail(n, k):
    """Valid under fixed-n, iid, preregistered Bernoulli(.5) null only."""
    return F(sum(comb(n, j) for j in range(k, n+1)), 2**n)

def prove():
    # Invented 4-state fixture, each transition row positive and sums to one.
    q = [[F(x, 10) for x in row] for row in
         [[4, 3, 2, 1], [1, 5, 2, 2], [2, 1, 5, 2], [3, 2, 1, 4]]]
    assert valid_stochastic(q)
    kluever = kluever_form_partition(q)
    v0, v1 = [0, 1], [0, 1, 2]
    direct = trace(q, v0)
    via = trace(trace(q, v1), v0)
    assert direct == via
    assert direct != [row[:2] for row in q[:2]]

    altered = [row[:] for row in q]
    altered[0][0], altered[0][1] = altered[0][1], altered[0][0]
    assert valid_stochastic(altered)
    changed = trace(altered, v0)
    assert changed != direct

    eye = [[F(i == j) for j in range(len(q))] for i in range(len(q))]
    assert multiply(multiply(q, eye), eye) == q

    compositions = [(a, b, c, 7-a-b-c)
      for a in range(1, 5) for b in range(1, 5) for c in range(1, 5)
      if 1 <= 7-a-b-c <= 4]
    cases = 0
    for indexes in product(range(len(compositions)), repeat=4):
        p = [[F(x, 7) for x in compositions[i]] for i in indexes]
        assert trace(p, v0) == trace(trace(p, v1), v0)
        cases += 1
        if cases == 128:
            break

    # Restricted external signal model is an extra ASSUMPTION, not Q=DAP.
    cooperation, p_signal = F(0), F(3, 4)
    assert cooperation*p_signal + (1-cooperation)*F(1, 2) == F(1, 2)
    r_min = F(1, 4)
    p_min = r_min*p_signal + (1-r_min)*F(1, 2)
    assert p_min == F(9, 16)
    n, k = 64, 48
    tail = binomial_one_sided_tail(n, k)
    return {
       "status": "exact_synthetic_arithmetic_passed",
       "matrix_source": "invented stochastic fixture; NOT empirical DMT data",
       "q_full": display_matrix(q),
       "kluever_selected_projection_non_lumpability": kluever,
       "trace_direct_V01": display_matrix(direct),
       "trace_via_V012_then_V01": display_matrix(via),
       "nested_trace_equal": direct == via,
       "hidden_term_nonzero": direct != [row[:2] for row in q[:2]],
       "changed_kernel_counterexample": display_matrix(changed),
       "changed_kernel_differs": changed != direct,
       "identity_factorisation_passed": True,
       "distinct_synthetic_cases_checked": cases,
       "zero_cooperation_p_correct": "1/2",
       "restricted_example_assumptions": {"r_min": "1/4", "p_signal": "3/4"},
       "restricted_example_lower_bound_p_correct": str(p_min),
       "example_one_sided_binomial_tail": {
            "n": n, "k": k, "p_value_exact": str(tail),
            "p_value_decimal": float(tail)
       },
       "limitations": [
         "Nested trace identity assumes one fixed kernel and nested observed sets.",
         "Kluver mode-to-form quotient is not a subset trace and may fail Markov lumpability.",
         "Finite exact fixtures do not formally prove the general trace-chain theorem.",
         "Observed Q cannot uniquely determine internal vs external ontology.",
         "Zero cooperation permits an external story observationally identical to null.",
         "No clinical data, fitted parameters or measured concentration-to-kernel map.",
         "Unrestricted internal models can reproduce any finite Markov observable law."
       ]
    }

if __name__ == "__main__":
    print(json.dumps(prove(), sort_keys=True, indent=2))
