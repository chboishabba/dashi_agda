#!/usr/bin/env python3
"""Independent exact bit-tape differential for Karp21 gamma all-k literal table.

This models the literal 3-state x 4-input x 4-work instruction table in
Karp21NativeGammaAllLengthFiniteTablePhysicalExact.agda. Exhaustive finite
evidence; NOT an Agda kernel, real-machine stack or full N21 bit-clock proof.
"""
from itertools import product
import json

B0, B1, BLANK, MARK = range(4)

class Tape:
    def __init__(self, bits=()):
        self.left = []
        self.head = bits[0] if bits else BLANK
        self.right = list(bits[1:])
    def execute(self, write, direction):
        self.head = write
        if direction == "R":
            self.left.insert(0, self.head)
            self.head = self.right.pop(0) if self.right else BLANK
        elif direction == "L":
            self.right.insert(0, self.head)
            self.head = self.left.pop(0) if self.left else BLANK
    def cells(self):
        return len(self.left) + len(self.right) + 1

def step(state, source, work):
    a, b = source.head, work.head
    if state < 2:
        if a == B0:
            return (1, B0, "R", MARK, "R", False)
        if a == B1 and state == 0:
            return (0, B1, "R", BLANK, "S", True)
        if a == B1 and state == 1:
            return (2, B1, "R", BLANK, "L", False)
        return (2, a, "S", MARK, "S", True)
    if a in (B0, B1) and b == MARK:
        return (2, a, "R", a, "L", False)
    if b == BLANK and a in (B0, B1, BLANK):
        return (2, a, "S", BLANK, "S", True)
    return (2, a, "S", MARK, "S", True)

def run(bits, fuel=100_000):
    source, work = Tape(bits), Tape()
    original_cells = source.cells() + work.cells()
    state = 0
    for t in range(1, fuel+1):
        state, wi, di, ww, dw, halt = step(state, source, work)
        source.execute(wi, di)
        work.execute(ww, dw)
        assert source.cells() + work.cells() <= original_cells + 2*t
        if halt:
            return source, work, state, t
    raise AssertionError("finite table failed to halt")

def original_gamma(bits):
    k = 0
    while k < len(bits) and bits[k] == B0:
        k += 1
    if k == len(bits) or len(bits) < 2*k + 1:
        return None
    return ([B1] + bits[k+1:2*k+1], bits[2*k+1:])

def check():
    checked = 0
    for k in range(10):
        for payload in product((B0,B1), repeat=k):
            for n in range(5):
                for suffix in product((B0,B1), repeat=n):
                    bits = [B0]*k + [B1] + list(payload) + list(suffix)
                    source, work, _, t = run(bits)
                    assert original_gamma(bits) == ([B1] + list(payload), list(suffix))
                    assert t == (1 if k == 0 else 2*k + 2)
                    assert source.head == (suffix[0] if suffix else BLANK)
                    assert source.right == list(suffix[1:])
                    if k:
                        assert work.head == BLANK
                        assert work.right == list(reversed(payload)) + [BLANK]
                    checked += 1
    malformed = ([],[B0],[B0,B0],[B0,B0,B1],[B0,B0,B1,B0],
                 [B0,B0,B0,B1,B1],[B0,B0,B0,B0,B1,B1])
    for word in malformed:
        assert original_gamma(word) is None
        run(word)
    return {"schema":"karp-gamma-physical-v1",
            "tested_k":"0..9", "wellformed_cases":checked,
            "malformed_controls":len(malformed),
            "one_token_work":"k=0:1, k>=1:2*k+2",
            "result":"PASS","agda_kernel":False,"full_N21_F4":False}

if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
