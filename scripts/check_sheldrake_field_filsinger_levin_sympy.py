#!/usr/bin/env python3
"""Exact synthetic discrimination checks for the Sheldrake/field/Levin consolidation.

All examples are rational finite models, not empirical field effects or evidence
of morphic resonance. No GitHub CI or Agda typecheck is implied.
"""
from itertools import product
from sympy import Matrix, Rational

Q = Rational
checks = 0

def check(label, condition):
    global checks
    assert bool(condition), label
    checks += 1
    print(f"PASS {checks:02d}: {label}")

def two_stage_galton(p_right):
    """The usual independent two-branch idealization, in L/M/R order."""
    q_left = 1 - p_right
    return Matrix([q_left**2, 2 * p_right * q_left, p_right**2])

base = two_stage_galton(Q(1, 2))
local_field = two_stage_galton(Q(3, 4))
check("reference 2-stage Galton probabilities", base == Matrix([Q(1, 4), Q(1, 2), Q(1, 4)]))
check("local-field-biased illustrative probabilities", local_field == Matrix([Q(1, 16), Q(3, 8), Q(9, 16)]))
check("reference probability normalized", sum(base) == 1)
check("biased probability normalized", sum(local_field) == 1)
check("field-off reverts to reference", two_stage_galton(Q(1, 2)) == base)
check("rightward mean count shifts", sum(i * local_field[i] for i in range(3)) - sum(i * base[i] for i in range(3)) == Q(1, 2))
check("total-variation distance exact", sum(abs(local_field[i] - base[i]) for i in range(3)) / 2 == Q(5, 16))

# A single co-varying condition cannot distinguish causal mechanisms.
# B = measured local-field coordinate, R = hypothetical cross-population
# similarity-history coordinate; neither is fitted to a physical experiment.
def kernel(alpha, beta, B, R):
    return two_stage_galton(Q(1, 2) + alpha * B + beta * R)

magnet_model = (Q(1, 4), Q(0))
morphic_model = (Q(0), Q(1, 4))
check("observational collision when local and candidate inputs co-vary",
      kernel(*magnet_model, 1, 1) == kernel(*morphic_model, 1, 1))
check("rival predictions differ when only local B is varied",
      kernel(*magnet_model, 1, 0) != kernel(*morphic_model, 1, 0))
check("rival predictions differ when only candidate R is varied",
      kernel(*magnet_model, 0, 1) != kernel(*morphic_model, 0, 1))

single_condition_design = Matrix([[1, 1, 1]])
separating_design = Matrix([[1, B, R] for B, R in product((0, 1), repeat=2)])
check("one observational condition has rank 1", single_condition_design.rank() == 1)
check("orthogonally varied candidate inputs yield full formal rank 3", separating_design.rank() == 3)
check("candidate-model probability stays valid at each selected design corner",
      all(all(0 <= x <= 1 for x in kernel(Q(1, 4), Q(0), B, R))
          for B, R in product((0, 1), repeat=2)))

# Same-boundary work bookkeeping. This is an illustrative equality, not
# an actual meter trace or an assertion of source-independent extraction.
inputs = {"natural": Q(5), "controller": Q(0), "initial_storage": Q(2)}
outputs = {"load": Q(4), "loss": Q(1), "radiated": Q(1), "final_storage": Q(1)}
check("illustrative same-boundary source energy equality",
      sum(inputs.values()) == sum(outputs.values()))
check("zero-input zero-storage nonnegative ledger forbids positive load",
      not any(load > 0 and load + loss + stored == 0
              for load, loss, stored in product(range(3), repeat=3)))

launch, delay, arrival = 2, 3, 5
check("retarded transport uses launch+delay=arrival", launch + delay == arrival)
check("retarded transport does not arrive before launch", arrival >= launch)

# Same present phenotype need not determine future local trajectory.
present = {"h0": "same", "h1": "same"}
future = {"h0": "target_A", "h1": "target_B"}
check("coarse present morphology can conceal different local histories",
      present["h0"] == present["h1"] and future["h0"] != future["h1"])

source_A = ("lab-A", "trial-001", "time-0")
source_B = ("lab-B", "trial-001", "time-0")
check("lab provenance and organism history are non-identical coordinates",
      source_A != source_B)

print(f"{checks}/{checks} exact synthetic checks PASS (SymPy)")
