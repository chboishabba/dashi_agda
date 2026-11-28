"""Synthetic bounded controls; not Agda, LES calibration or cryptographic verification."""
from dataclasses import dataclass, replace
from itertools import product
import json
import sympy as sp

@dataclass(frozen=True)
class Balance:
    opening: int
    inflow: int
    export: int
    closing: int
    transformed: int
    residual: int
    unit: str = 'phosphorus_g'
    window: int = 0

    def valid(self):
        vals = (self.opening, self.inflow, self.export, self.closing,
                self.transformed, self.residual)
        return min(vals) >= 0 and self.opening + self.inflow == (
            self.export + self.closing + self.transformed + self.residual)

    def retained(self):
        return self.closing + self.transformed + self.residual

def matched(a, b):
    return (a.valid() and b.valid() and a.unit == b.unit and
            a.window == b.window and a.export == b.inflow)

def consolidate(a, b):
    if not matched(a, b):
        return None
    return (a.opening + a.inflow + b.opening,
            a.retained() + b.export + b.retained())

def proof_gate(expected, actual, artifact_match, executed, success, verified, review):
    # Independent Boolean fixtures, not a verifier or a security guarantee.
    return (expected == actual and artifact_match and executed and success
            and verified and review)

def run():
    counts = dict(symbolic=0, conservation=0, reject_mismatch=0, receipt_gate=0)
    # Eliminate the shared transfer from two independently balanced sites.
    x, c, d, b, y = sp.symbols('x c d b y', nonnegative=True, integer=True)
    assert sp.expand((x + c) + b - (c + d)).subs(d, b + x) == 0
    counts['symbolic'] += 1
    # Enumerate nonzero as well as zero transfers and unaccounted residuals.
    for ao, ai, bo in product(range(4), repeat=3):
        for x in range(ao + ai + 1):
            for ar in range(ao + ai - x + 1):
                for at in range(ao + ai - x - ar + 1):
                    a = Balance(ao, ai, x, ao + ai - x - ar - at, at, ar)
                    for out in range(bo + x + 1):
                        for br in range(bo + x - out + 1):
                            b = Balance(bo, x, out, bo + x - out - br, 0, br)
                            left, right = consolidate(a, b)
                            assert left == right
                            assert a.residual == ar and b.residual == br
                            counts['conservation'] += 1
    a = Balance(8, 2, 4, 5, 1, 0)
    b = Balance(2, 4, 1, 4, 1, 0)
    assert consolidate(a, b) == (12, 12)
    for bad in (replace(b, unit='water_L'), replace(b, window=1),
                replace(b, inflow=5, closing=5), replace(b, closing=3)):
        assert consolidate(a, bad) is None
        counts['reject_mismatch'] += 1
    for expected, actual in product(range(3), repeat=2):
        for flags in product((False, True), repeat=5):
            failures = (expected != actual,) + tuple(not f for f in flags)
            assert proof_gate(expected, actual, *flags) == (not any(failures))
            counts['receipt_gate'] += 1
    return counts

if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True))
