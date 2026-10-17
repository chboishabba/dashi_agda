from dataclasses import dataclass
from enum import Enum
import json

"""Independent executable reconstruction of the attributed Goldbach30/29
abstract transition semantics used only as a bounded empirical replay receipt.

External construction authority: Mike Dupont / meta-introspector, aok commits
7added5000a75226a834ba7aab08a7380f0c70b3 and
c168223e96f7acc6179044f2a365a92db2e350c3.

This is NOT a copy of the upstream Lean source and does not substitute for the
upstream Lean kernel proofs or DASHI's Agda theorems.
"""


class St(Enum):
    RAA = "RAA"
    RAB = "RAB"
    Q = "Q"
    R = "R"
    R2 = "R2"
    NTA = "NTA"
    NT2A = "NT2A"
    NTB = "NTB"
    NT2B = "NT2B"
    SA = "SA"
    SB = "SB"


@dataclass(frozen=True)
class Regs:
    a: int
    b: int
    c: int
    d: int
    e: int
    f: int
    s: int
    g: int
    h: int
    m: int


@dataclass(frozen=True)
class Cfg:
    st: St
    r: Regs


def step30(cfg):
    st, r = cfg.st, cfg.r
    a, b, c, d, e, f, s, g, h, m = (
        r.a, r.b, r.c, r.d, r.e, r.f, r.s, r.g, r.h, r.m
    )
    if st == St.RAA:
        if a > 0:
            return Cfg(St.Q, Regs(a - 1, b, c, d, e, f, s + 1, g, h, m))
        if d > 0:
            return Cfg(St.R, Regs(a, b, c, d - 1, e + 1, f, s, g, h + 1, m))
        return Cfg(St.NTA, r)
    if st == St.RAB:
        if b > 0:
            return Cfg(St.Q, Regs(a, b - 1, c, d, e, f, s + 1, g, h, m + 1))
        if d > 0:
            return Cfg(St.R, Regs(a, b, c, d - 1, e + 1, f, s, g, h + 1, m + 1))
        return Cfg(St.NTB, r)
    if st == St.Q:
        if m > 0 and d > 0:
            return Cfg(St.RAB, Regs(a, b, c, d - 1, e + 1, f, s, g, h, m - 1))
        if d > 0:
            return Cfg(St.RAA, Regs(a, b, c, d - 1, e + 1, f, s, g, h, m))
        if f > 0:
            return Cfg(St.R, Regs(a, b, c, d, e, f - 1, s, g, h, m))
        return Cfg(St.R, r)
    if st == St.R:
        if e > 0:
            return Cfg(St.R2, Regs(a, b, c, d + 1, e - 1, f, s, g, h, m))
        if m > 0 and h > 0:
            return Cfg(St.NTB, Regs(a, b, c, d, e, f, s, g + 1, h - 1, m - 1))
        if h > 0:
            return Cfg(St.NTA, Regs(a, b, c, d, e, f, s, g + 1, h - 1, m))
        return Cfg(St.Q, r)
    if st == St.R2:
        return Cfg(St.R, r)
    if st == St.NTA:
        if s > 0 and e > 0:
            return Cfg(St.NT2A, Regs(a + 1, b, c, d, e - 1, f, s - 1, g, h, m))
        if s > 0:
            return Cfg(St.NT2A, Regs(a + 1, b, c, d, e, f, s - 1, g, h, m))
        if g > 0:
            return Cfg(St.RAA, Regs(a, b, c, d + 1, e, f + 1, s, g - 1, h, m))
        if f > 0:
            return Cfg(St.NTB, Regs(a, b, c, d + 1, e, f - 1, s, g + 1, h, m))
        if b > 0 and c > 0:
            return Cfg(St.RAA, Regs(a + 1, b - 1, c - 1, d + 2, e, f + 1, s, g, h, m))
        return None
    if st == St.NTB:
        if s > 0 and e > 0:
            return Cfg(St.NT2B, Regs(a, b + 1, c, d, e - 1, f, s - 1, g, h, m))
        if s > 0:
            return Cfg(St.NT2B, Regs(a, b + 1, c, d, e, f, s - 1, g, h, m))
        if g > 0:
            return Cfg(St.RAB, Regs(a, b, c, d + 1, e, f + 1, s, g - 1, h, m))
        if f > 0:
            return Cfg(St.SA, Regs(a, b, c, d, e, f - 1, s, g, h, m))
        if b > 0 and c > 0:
            return Cfg(St.RAA, Regs(a + 1, b - 1, c - 1, d + 2, e, f + 1, s, g, h, m))
        return None
    if st == St.NT2A:
        return Cfg(St.NTA, r)
    if st == St.NT2B:
        return Cfg(St.NTB, r)
    if st == St.SA:
        if a > 0:
            return Cfg(St.SB, Regs(a - 1, b + 1, c + 1, d, e, f, s, g, h, m))
        if c > 0:
            return Cfg(St.RAA, Regs(a + 2, b, c - 1, d + 2, e, f + 1, s, g, h, m))
        return None
    if st == St.SB:
        return Cfg(St.SA, r)
    return None


def step29(cfg):
    st, r = cfg.st, cfg.r
    a, b, c, d, e, f, s, g, h, m = (
        r.a, r.b, r.c, r.d, r.e, r.f, r.s, r.g, r.h, r.m
    )
    if st in (St.RAA, St.RAB, St.Q, St.R, St.R2, St.NTA, St.NT2A):
        return step30(cfg)
    if st == St.NTB:
        if s > 0 and e > 0:
            return Cfg(St.NT2B, Regs(a, b + 1, c, d, e - 1, f, s - 1, g, h, m))
        if s > 0:
            return Cfg(St.NT2B, Regs(a, b + 1, c, d, e, f, s - 1, g, h, m))
        if g > 0:
            return Cfg(St.RAB, Regs(a, b, c, d + 1, e, f + 1, s, g - 1, h, m))
        if f > 0 and a > 0:
            return Cfg(St.SB, Regs(a - 1, b + 1, c + 1, d, e, f - 1, s, g, h, m))
        if f > 0:
            return Cfg(St.NT2B, Regs(a + 1, b + 1, c, d, e, f - 1, s, g, h, m))
        if b > 0 and c > 0:
            return Cfg(St.RAA, Regs(a + 1, b - 1, c - 1, d + 2, e, f + 1, s, g, h, m))
        return None
    if st == St.NT2B:
        return Cfg(St.NTB, r)
    if st == St.SB:
        return Cfg(St.NTB, Regs(a, b, c, d, e, f + 1, s, g, h, m))
    return None


def is_top(cfg):
    if cfg is None or cfg.st != St.RAA:
        return False
    r = cfg.r
    return (
        r.d == 2 and r.e == 0 and r.f == 1 and r.s == 0 and
        r.g == 0 and r.h == 0 and r.m == 0
    )


def terminal_formula(a_tail, b, c, d, e, h, m):
    # actual entry a = a_tail + 1, f=1, s=g=0
    return Regs(2, b + a_tail + 1, c + a_tail, d + 2, e, 1, 0, 0, h, m)


def first_raa(step, cfg, limit=10000):
    for n in range(1, limit + 1):
        cfg = step(cfg)
        if cfg is None:
            return None, n
        if cfg.st == St.RAA:
            return cfg, n
    raise AssertionError("no RAA boundary within limit")


def verify_macro_grid():
    cases = 0
    for a_tail in range(5):
        for b in range(4):
            for c in range(4):
                for d in range(3):
                    for e in range(3):
                        for h in range(2):
                            for m in range(2):
                                start = Cfg(
                                    St.NTB,
                                    Regs(a_tail + 1, b, c, d, e, 1, 0, 0, h, m),
                                )
                                expected = terminal_formula(a_tail, b, c, d, e, h, m)
                                old, _ = first_raa(step30, start)
                                new, _ = first_raa(step29, start)
                                assert old is not None and old.r == expected
                                assert new is not None and new.r == expected
                                cases += 1

    # Regression: arbitrary f>1 must NOT be admitted by the macro contract.
    overbroad = Cfg(St.NTB, Regs(1, 2, 1, 0, 0, 2, 0, 0, 0, 0))
    actual, _ = first_raa(step29, overbroad)
    forbidden_old_formula = Regs(2, 3, 1, 2, 0, 2, 0, 0, 0, 0)
    assert actual is not None and actual.r != forbidden_old_formula

    # Regression: s>0 selects restoration, not the success branch.
    restoration = Cfg(St.NTB, Regs(2, 2, 0, 0, 0, 1, 1, 0, 0, 0))
    assert step29(restoration).st == St.NT2B
    return cases


def advance_top(step, cfg, machine, max_steps=10_000_000):
    assert is_top(cfg)
    success = False
    for n in range(1, max_steps + 1):
        if machine == "30" and cfg.st == St.NTB and cfg.r.s == 0 and cfg.r.g == 0 and cfg.r.f > 0:
            nxt = step(cfg)
            if nxt is not None and nxt.st == St.SA:
                success = True
        cfg = step(cfg)
        if cfg is None or is_top(cfg):
            return cfg, n, success
    raise AssertionError("top segment exceeded max_steps")


def verify_checkpoint_replay(segments=200):
    c30 = Cfg(St.RAA, Regs(2, 2, 0, 2, 0, 1, 0, 0, 0, 0))
    c29 = c30
    total30 = 0
    total29 = 0
    successes = 0

    for i in range(segments):
        assert is_top(c30) and is_top(c29)
        assert (c30.r.a, c30.r.b, c30.r.c) == (c29.r.a, c29.r.b, c29.r.c)

        n30, l30, success = advance_top(step30, c30, "30")
        n29, l29, _ = advance_top(step29, c29, "29")
        assert (n30 is None) == (n29 is None)
        if n30 is None:
            return {
                "segments": i + 1,
                "halted": True,
                "successes": successes,
                "steps30": total30,
                "steps29": total29,
            }

        assert (n30.r.a, n30.r.b, n30.r.c) == (n29.r.a, n29.r.b, n29.r.c)
        assert l29 - l30 == (1 if success else 0)
        successes += int(success)
        total30 += l30
        total29 += l29
        assert total29 - total30 == successes
        c30, c29 = n30, n29

    return {
        "segments": segments,
        "halted": False,
        "successes": successes,
        "steps30": total30,
        "steps29": total29,
        "step_delta": total29 - total30,
        "last_top": [c30.r.a, c30.r.b, c30.r.c],
    }


def main():
    macro_cases = verify_macro_grid()
    replay = verify_checkpoint_replay()
    print(json.dumps({"macro_cases": macro_cases, "checkpoint_replay": replay}, sort_keys=True))


if __name__ == "__main__":
    main()
