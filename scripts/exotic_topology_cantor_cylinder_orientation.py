#!/usr/bin/env python3
"""Chronological cylinder interpretation of existing DASHI prefix words.

Owner: DASHI.Foundations.CantorProjectiveCylinderMeasureExact, where
leftChild prepends a bit. This is a valid reversed-stack word
operation and preserves the recorded dyadic mass identity, but DOES
NOT refine conventional chronological stream-prefix events. The
topology end tree from #1254 attaches p -> p0,p1 (APPEND), so it
needs a genuine orientation bridge, not equal masses.

This script independently audits all finite chronological prefixes to
depth 9 and explicit failing membership of the old prepend child.
The new Agda sibling supplies source-written all-depth proofs, but
kernel compilation and geometric Richards ends remain open.

Original mathematical reference: elementary Cantor product topology;
DASHI source implementation remains separately attributed.
"""
from fractions import Fraction
from itertools import product
import json


def fair_mass(word):
    return Fraction(1, 2 ** len(word))


def reverse(word):
    return word[::-1]


def matches(word, stream):
    return stream[:len(word)] == word


def audit(max_depth=9):
    total = 0
    for n in range(max_depth + 1):
        for prefix in product((False, True), repeat=n):
            for bit in (False, True):
                chronological_child = prefix + (bit,)
                stack_child = (bit,) + prefix
                assert chronological_child[:n] == prefix
                # An EQUALITY OF MASSES is not equality of EVENTS.
                assert fair_mass(chronological_child) == fair_mass(stack_child)
                assert reverse(chronological_child) == (
                    bit,) + reverse(prefix)
                # Every stream matching the chronological child
                # matches the parent, by literal prefix truncation.
                stream = chronological_child + (not bit, True, False)
                assert matches(chronological_child, stream)
                assert matches(prefix, stream)
                total += 1
    parent = (True,)
    old_left = (False,) + parent
    stream = (False, True, False)
    assert matches(old_left, stream)
    assert not matches(parent, stream)
    assert old_left != parent + (False,)
    return {
        "source_original_prepend_is_mass_consistent": True,
        "old_prepend_is_chronological_refinement": False,
        "append_children_are_chronological_refinements": True,
        "reverse_word_conjugates_append_to_prepend": True,
        "exact_prefix_child_cases": total,
        "original_source_unchanged": True,
        "richards_end_space_homeomorphism_proved": False,
        "agda_kernel_verified": False,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
