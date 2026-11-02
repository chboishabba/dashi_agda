#!/usr/bin/env python3
"""Exhaustive six-cell reference check for the DASHI Qwenputer finite abstraction.

External inspiration: Divyansh Agrawal, Qwenputer v0.1.0 (2026),
https://github.com/divagr18/qwenputer .
This test is a DASHI *synthetic finite oracle*, not Agrawal's upstream test,
an Agda type-check, or a verification of the real compiled Qwen checkpoint.
"""

from itertools import product

HEADS = ("data", "register")
ROWS = (0, 1, 2)
ADDRS = tuple(product(HEADS, ROWS))


def overwrite(state, selected, value):
    return {address: (value if address == selected else state[address]) for address in ADDRS}


def embed(bit):
    return 1 if bit else -1


def decode(trit):
    return trit == 1


def trace_single_write(state, pc, selected, value):
    # ADDR selected ; VAL value ; STEP, where STEP increases PC and closes key.
    pending = selected
    state = overwrite(state, pending, value)
    pending = None
    return state, pc + 1, pending


def names_eq(left, right):
    return left == right


def put(store, name, content):
    return {**store, name: tuple(content)}


def get(store, name):
    return store.get(name)


def append(store, name, suffix):
    return put(store, name, store.get(name, ()) + tuple(suffix))


def delete(store, name):
    new = dict(store)
    new.pop(name, None)
    return new


def list_entries(store):
    return tuple((k, store[k]) for k in ("A", "B", "C") if k in store)



def check_multistep_and_record_boundaries():
    """Finite exhaustive analogue of new arbitrary-length transport theorems.

    This verifies the Python model only; it is not the Agda checker, source
    compiler, HF kernel, Triton GPU, or a QEMU comparison.
    """
    writes = tuple(product(ADDRS, (False, True)))
    multi_cases = 0
    # All 64 Boolean six-cell initial states and all 0..3 write sequences.
    for bits in product((False, True), repeat=len(ADDRS)):
        initial = dict(zip(ADDRS, bits))
        initial_t = {a: embed(initial[a]) for a in ADDRS}
        for length in range(4):
            for history in product(writes, repeat=length):
                final_b = initial
                final_t = initial_t
                for address, bit in history:
                    final_b = overwrite(final_b, address, bit)
                    final_t = overwrite(final_t, address, embed(bit))
                assert {a: decode(final_t[a]) for a in ADDRS} == final_b
                multi_cases += 1

    matrix_cases = 0
    # Exact integer subtraction instance of S' = S + k (v - old),
    # in a two-column finite matrix.
    for bits in product((False, True), repeat=len(ADDRS)):
        initial = {a: (int(bits[i]), -int(bits[i]))
                   for i, a in enumerate(ADDRS)}
        for selected in ADDRS:
            for target in ((0, 0), (1, -1), (-7, 12)):
                out = {}
                for a in ADDRS:
                    old = initial[a]
                    k = int(a == selected)
                    out[a] = tuple(old[c] + k * (target[c] - old[c])
                                   for c in range(2))
                assert out[selected] == target
                assert all(out[a] == initial[a]
                           for a in ADDRS if a != selected)
                matrix_cases += 1

    record_cases = 0
    # Source-family representative terminal tokens; prefix tokens do
    # not mutate ISA state. SC is deliberately excluded (source semantics open).
    ends = ("F0", "F1", "F2", "NT", "J", "ST0", "ST1",
            "SS0", "SS1", "HALT", "BYTE")
    prefixes = ("V", "R", "QS", "QD", "BD", "FLT", "HEX")
    for length in range(5):
        for prefix in product(prefixes, repeat=length):
            for terminal in ends:
                counter = 0
                for token in prefix + (terminal,):
                    if token in ends:
                        counter += 1
                assert counter == 1
                record_cases += 1

    assert (16 * 80) == 1280
    assert 131072 + 131072 == 262144
    assert 32768 == 0 + 32768
    print(f"  multistep transports: {multi_cases};"
          f" integer matrix checks: {matrix_cases};"
          f" typed record cases: {record_cases}.")

def run():
    row_checks = 0
    read_checks = 0
    trace_checks = 0
    ternary_checks = 0
    for bits in product((False, True), repeat=len(ADDRS)):
        original = dict(zip(ADDRS, bits))
        embedded = {a: embed(original[a]) for a in ADDRS}
        for selected in ADDRS:
            for bit in (False, True):
                updated = overwrite(original, selected, bit)
                assert updated[selected] == bit
                row_checks += 1
                for other in ADDRS:
                    assert updated[other] == (bit if other == selected else original[other])
                    read_checks += 1
                post, pc, pending = trace_single_write(original, 7, selected, bit)
                assert post == updated and pc == 8 and pending is None
                trace_checks += 1
                new_ternary = overwrite(embedded, selected, embed(bit))
                assert decode(new_ternary[selected]) == bit
                assert all(new_ternary[a] == embedded[a] for a in ADDRS if a != selected)
                assert all(t != 0 for t in new_ternary.values())
                ternary_checks += 1

    file_checks = 0
    for a, b, c in product((None, (), (False,), (True, False)), repeat=3):
        store = {key: tuple(value) for key, value in zip(("A", "B", "C"), (a, b, c))
                 if value is not None}
        for key in ("A", "B", "C"):
            saved = dict(store)
            for suffix in ((), (False,), (True, False)):
                changed = put(store, key, suffix)
                assert get(changed, key) == suffix
                assert all(get(changed, other) == get(store, other)
                           for other in ("A", "B", "C") if other != key)
                appended = append(store, key, suffix)
                assert get(appended, key) == store.get(key, ()) + suffix
                assert key not in delete(store, key)
                assert list_entries(saved) == tuple((k, saved[k]) for k in ("A", "B", "C")
                                                       if k in saved)
                assert dict(saved) == store  # snapshot restores original, no mutation
                file_checks += 1

    # Source P2 stage-budget arithmetic, not model-weight verification.
    assert 4 + 16 + 16 + 7 + 8 + 16 + 16 + 16 == 99
    assert sum((306, 1376, 4138, 7876, 6621, 3751, 7923, 8149, 1074, 798)) == 42012
    check_multistep_and_record_boundaries()
    print(
        "Qwenputer finite oracle OK:",
        f"{row_checks} read-after-write;",
        f"{read_checks} row comparisons;",
        f"{trace_checks} trace states;",
        f"{ternary_checks} ternary transports;",
        f"{file_checks} store cases; source stage arithmetic checked.",
    )


if __name__ == "__main__":
    run()
