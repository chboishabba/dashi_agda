#!/usr/bin/env python3
"""Executable finite-table reference for source-written Agda F1 k=1 cut.

Original Elias-gamma word 0,1,b + suffix is decoded by the existing
binary-native parser as (1,b) + suffix. A two-state physical machine
scans 0 (one Mark), skips separator 1, copies payload b to the
single work head, and halts after EXACTLY three tape instructions.

Only k=1 is certified. k=0 and k>=2 are deliberate negative controls;
this is not a whole N21 bit-machine or a proof of polynomial F4.
"""
from __future__ import annotations

import itertools
import json


def decode_original_gamma(word: tuple[int, ...]):
    k = 0
    while k < len(word) and word[k] == 0:
        k += 1
    if k == len(word) or k+1+k > len(word):
        return None
    return (1,) + word[k+1:k+1+k], word[k+1+k:]


def physical_three_step(word: tuple[int, ...]):
    input_index = 0
    state = 0  # 0 scan prefix, 1 read one payload bit
    tally = []
    output = None
    halted = False
    trace = []
    for _ in range(3):
        if halted:
            break
        symbol = word[input_index] if input_index < len(word) else None
        if state == 0 and symbol == 0:
            tally.append("Mark")
            input_index += 1
        elif state == 0 and symbol == 1:
            input_index += 1
            state = 1
        elif state == 1 and symbol in (0, 1):
            output = symbol
            input_index += 1
            halted = True
        else:
            halted = True
        trace.append((state, input_index, halted))
    return {"halted": halted, "payload": output, "tally": tuple(tally),
            "input_suffix": word[input_index:], "steps": len(trace)}


def main():
    cases = 0
    for length in range(9):
        for suffix in itertools.product((0, 1), repeat=length):
            for payload in (0, 1):
                word = (0, 1, payload) + suffix
                source = decode_original_gamma(word)
                physical = physical_three_step(word)
                assert source == ((1, payload), suffix)
                assert physical == {
                    "halted":True,"payload":payload,"tally":("Mark",),
                    "input_suffix":suffix,"steps":3}
                cases += 1
    # k=0: source consumes 1 with NO payload. This one-bit machine
    # reads a spurious payload instead. Fail closed for that family.
    zero_prefix = (1, 0)
    assert decode_original_gamma(zero_prefix) == ((1,), (0,))
    assert physical_three_step(zero_prefix)["input_suffix"] != (0,)
    # k=2: three steps only reach the separator, not all payload bits.
    two_zeros = (0, 0, 1, 0, 1)
    assert decode_original_gamma(two_zeros) == ((1, 0, 1), ())
    assert not physical_three_step(two_zeros)["halted"]
    print(json.dumps({
        "source":"Karp21GammaBinaryNativePayloadExact.readGammaBinary",
        "physical_source":"Karp21NativeGammaOneBitPayloadPhysicalExact",
        "suffix_lengths_exhaustively_checked":"0..8",
        "successful_original_k1_word_cases":cases,
        "physical_steps_per_k1_word":3,
        "unaccounted_control_state_reset":False,
        "negative_controls_k0_and_k2_pass":True,
        "agda_kernel_accepted_here":False,
        "full_N21_bit_machine_or_polynomial_clock":False
    }, indent=2))


if __name__=="__main__":
    main()
