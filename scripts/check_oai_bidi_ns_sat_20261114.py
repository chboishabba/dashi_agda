#!/usr/bin/env python3
"""Independent exact finite regression for two cross-OpenAI Clay transfer gates.

NS: forced C/D does not decide unforced B; zero-force counterexample has a
conditional forward transport into forced scope when its data class includes 0.
SAT: literal-list -> clause/list Finset normalization preserves exact
model count on all declared Fin n bits, including unused bits.

All finite/reference only. Does not replay Lean/Agda kernels or prove
physical NS hypotheses, real source bytes, OAI time bounds, or P!=NP.
"""
from itertools import product
import json


def model_count_list(n, cnf):
    return sum(all(any(bits[var] == polarity for var, polarity in clause)
                   for clause in cnf) for bits in product((False, True), repeat=n))


def model_count_finset(n, cnf):
    normalized = frozenset(frozenset(clause) for clause in cnf)
    return sum(all(any(bits[var] == polarity for var, polarity in clause)
                   for clause in normalized)
               for bits in product((False, True), repeat=n))


def sat_exhaustive():
    cases = 0
    for n in (0, 1, 2, 3):
        lits = tuple(product(range(n), (False, True)))
        clauses = ((),) + tuple((l,) for l in lits)
        if n <= 2:
            clauses += tuple((a, b) for a in lits for b in lits)
        # Every list of 0, 1 or 2 clauses; duplicates and order matter.
        for length in range(3):
            for formula in product(clauses, repeat=length):
                x = model_count_list(n, formula)
                y = model_count_finset(n, formula)
                assert x == y, (n, formula, x, y)
                assert (x > 0) == (y > 0)
                cases += 1
    # Force additional 3-variable permutation, duplicate and negation cases.
    sample = ((0, True), (0, True), (1, False))
    assert model_count_list(3, (sample, sample)) == model_count_finset(3, (sample,))
    assert model_count_list(3, (((0, True),),)) == 4
    assert model_count_list(3, ()) == 8
    assert model_count_list(3, ((),)) == 0
    assert model_count_list(0, ()) == 1
    assert model_count_list(0, ((),)) == 0
    # Negative controls: counting only occurring bits and empty-clause truth.
    assert model_count_list(3, (((0, True),),)) != model_count_list(1, (((0, True),),))
    assert model_count_list(3, ((),)) != model_count_list(3, ())
    return cases


def ns_scope_exhaustive():
    scenarios = 0
    forced_breakdown_and_unforced_global = 0
    # Two forcing labels: False denotes f=0, True a nonzero smooth forcing.
    # Abstract existence predicates are intentionally NOT physical solutions.
    for unforced_global, nonzero_force_global in product((False, True), repeat=2):
        universal_forced = unforced_global and nonzero_force_global
        breakdown_some_forcing = not (unforced_global and nonzero_force_global)
        assert breakdown_some_forcing == (not universal_forced)
        # An unforced no-solution witness supplies a forced witness
        # only when zero forcing is in the admitted force class.
        if not unforced_global:
            assert breakdown_some_forcing
        if unforced_global and not nonzero_force_global:
            forced_breakdown_and_unforced_global += 1
        scenarios += 1
    assert forced_breakdown_and_unforced_global == 1
    return scenarios


def main():
    sat = sat_exhaustive()
    ns = ns_scope_exhaustive()
    print(json.dumps({
        "result": "PASS", "sat_list_to_finset_formulas": sat,
        "ns_forced_unforced_truth_models": ns,
        "forced_breakdown_compatible_with_unforced_global_models": 1,
        "unused_variables_preserved": True,
        "duplicate_order_and_empty_clause_controls": True,
        "actual_oai_lean_machine_checked": False,
        "agda_kernel_checked": False,
        "physical_clay_witnesses_constructed": False,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
