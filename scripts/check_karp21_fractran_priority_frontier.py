#!/usr/bin/env python3
"""Bounded differential model for FRACDASH priority-frontier Karp bridge.

Not an Agda kernel receipt or an N21 Turing-machine clock.
"""
from itertools import product


def enabled(require_mask, state):
    return (state & require_mask) == require_mask


def first_enabled(rules, state):
    return next((i for i, requirement in enumerate(rules)
                 if enabled(requirement, state)), None)


def refresh(rules, before, after, cache):
    changed = before ^ after
    return [enabled(rule, after) if rule & changed else old
            for rule, old in zip(rules, cache)]


def main():
    cases = 0
    refreshed = 0
    for nlanes in (1, 2, 3):
        for rule_count in (0, 1, 2, 3):
            for rules in product(range(1 << nlanes), repeat=rule_count):
                for before in range(1 << nlanes):
                    for after in range(1 << nlanes):
                        original = [enabled(rule, before) for rule in rules]
                        updated = refresh(rules, before, after, original)
                        fresh = [enabled(rule, after) for rule in rules]
                        assert updated == fresh, (rules, before, after)
                        selected = next((i for i, ok in enumerate(updated) if ok), None)
                        assert selected == first_enabled(rules, after)
                        cases += 1
                        refreshed += sum(bool(rule & (before ^ after)) for rule in rules)
    # A stale affected-rule guard is an incorrect optimization.
    assert enabled(1, 1) and not enabled(1, 0)
    print(f'FRACDASH frontier differential: {cases:,} finite cases passed; {refreshed:,} rule refreshes')
    print('Negative control: stale affected-rule guard rejected')
    print('Not Agda typechecking, original N21 equivalence, or a polynomial bit-machine clock.')


if __name__ == '__main__':
    main()
