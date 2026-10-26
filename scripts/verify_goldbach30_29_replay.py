from dataclasses import dataclass
from enum import Enum
from pathlib import Path
import json
import re

"""Independent executable reconstruction of the attributed Goldbach30/29
abstract transition semantics, now anchored to byte-exact vendored upstream
`Program.lean` source objects.

External construction authority: Mike Dupont / meta-introspector, aok commit
c168223e96f7acc6179044f2a365a92db2e350c3.

The vendored Lean files remain upstream AGPL-3.0 source. This Python replay is
DASHI-authored empirical verification: it parses the literal published
FRACTRAN fraction lists, checks their source-level relation, and cross-checks
direct integer FRACTRAN stepping against the independently reconstructed
abstract machines. It does not replace either Lean `fstep_enc` theorem or an
Agda kernel proof.
"""

ROOT = Path(__file__).resolve().parents[1]
VENDOR_ROOT = ROOT / "vendor" / "meta-introspector-aok"
VENDOR29_PROGRAM = (
    VENDOR_ROOT
    / "c168223e96f7acc6179044f2a365a92db2e350c3"
    / "Goldbach29"
    / "Program.lean"
)
VENDOR30_PROGRAM = (
    VENDOR_ROOT
    / "c168223e96f7acc6179044f2a365a92db2e350c3"
    / "Goldbach30"
    / "Program.lean"
)


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


REGISTER_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29)
STATE_PRIMES_30 = {
    St.RAA: 31,
    St.RAB: 37,
    St.Q: 41,
    St.R: 43,
    St.R2: 47,
    St.NTA: 53,
    St.NT2A: 59,
    St.NTB: 61,
    St.NT2B: 67,
    St.SA: 71,
    St.SB: 73,
}
STATE_PRIMES_29 = {
    St.RAA: 31,
    St.RAB: 37,
    St.Q: 41,
    St.R: 43,
    St.R2: 47,
    St.NTA: 53,
    St.NT2A: 59,
    St.NTB: 61,
    St.NT2B: 67,
    St.SB: 71,
}


def extract_fractran_program(path: Path):
    """Parse exactly the literal fraction list assigned to `goldbachProg`."""
    text = path.read_text()
    match = re.search(
        r"def\s+goldbachProg\s*:\s*FractranProgram\s*:=\s*\[(.*?)\]",
        text,
        flags=re.S,
    )
    if not match:
        raise AssertionError(f"goldbachProg list not found in {path}")
    return [(int(p), int(q)) for p, q in re.findall(r"(\d+)\s*/\s*(\d+)", match.group(1))]


def fractran_step(program, n):
    for numerator, denominator in program:
        product = n * numerator
        if product % denominator == 0:
            return product // denominator
    return None


def encode_cfg(cfg, state_primes):
    if cfg is None:
        return None
    exponents = (
        cfg.r.a,
        cfg.r.b,
        cfg.r.c,
        cfg.r.d,
        cfg.r.e,
        cfg.r.f,
        cfg.r.s,
        cfg.r.g,
        cfg.r.h,
        cfg.r.m,
    )
    n = state_primes[cfg.st]
    for p, exponent in zip(REGISTER_PRIMES, exponents):
        n *= p ** exponent
    return n


def verify_vendored_fraction_programs():
    p29 = extract_fractran_program(VENDOR29_PROGRAM)
    p30 = extract_fractran_program(VENDOR30_PROGRAM)
    assert len(p29) == 29
    assert len(p30) == 30
    # Literal source relation: the shared machine front/back-end prefix is exact.
    assert p29[:25] == p30[:25]
    # The failure transition NT_B*b*c -> RA_A*a*d^2*f is reused unchanged,
    # shifted by the inserted/removed success routing.
    assert p30[26] == p29[27] == (39494, 915)
    # Start integer is source-declared identically in both Program files.
    assert "def goldbachStart : ℕ := 710892" in VENDOR29_PROGRAM.read_text()
    assert "def goldbachStart : ℕ := 710892" in VENDOR30_PROGRAM.read_text()
    # Each exact source contains its own formal one-step bridge.
    assert "theorem fstep_enc" in VENDOR29_PROGRAM.read_text()
    assert "theorem fstep_enc" in VENDOR30_PROGRAM.read_text()
    return p29, p30


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


def verify_direct_fractran_step_bridge(program, step, state_primes, cfg):
    encoded = encode_cfg(cfg, state_primes)
    abstract_next = step(cfg)
    fractran_next = fractran_step(program, encoded)
    assert fractran_next == encode_cfg(abstract_next, state_primes)


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


def verify_macro_grid(p29, p30):
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
                                # Same-object sanity: direct FRACTRAN must agree with the
                                # attributed abstract step on the success entry itself.
                                verify_direct_fractran_step_bridge(p30, step30, STATE_PRIMES_30, start)
                                verify_direct_fractran_step_bridge(p29, step29, STATE_PRIMES_29, start)
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


def advance_top(step, cfg, machine, program, state_primes, max_steps=10_000_000):
    assert is_top(cfg)
    success = False
    for n in range(1, max_steps + 1):
        # Every abstract microstep on the replay path is cross-checked against
        # the literal vendored FRACTRAN fraction program.
        verify_direct_fractran_step_bridge(program, step, state_primes, cfg)
        if machine == "30" and cfg.st == St.NTB and cfg.r.s == 0 and cfg.r.g == 0 and cfg.r.f > 0:
            nxt = step(cfg)
            if nxt is not None and nxt.st == St.SA:
                success = True
        cfg = step(cfg)
        if cfg is None or is_top(cfg):
            return cfg, n, success
    raise AssertionError("top segment exceeded max_steps")


def verify_checkpoint_replay(p29, p30, segments=200):
    c30 = Cfg(St.RAA, Regs(2, 2, 0, 2, 0, 1, 0, 0, 0, 0))
    c29 = c30
    total30 = 0
    total29 = 0
    successes = 0

    for i in range(segments):
        assert is_top(c30) and is_top(c29)
        assert (c30.r.a, c30.r.b, c30.r.c) == (c29.r.a, c29.r.b, c29.r.c)

        n30, l30, success = advance_top(step30, c30, "30", p30, STATE_PRIMES_30)
        n29, l29, _ = advance_top(step29, c29, "29", p29, STATE_PRIMES_29)
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
    p29, p30 = verify_vendored_fraction_programs()
    macro_cases = verify_macro_grid(p29, p30)
    replay = verify_checkpoint_replay(p29, p30)
    print(
        json.dumps(
            {
                "vendored_program_lengths": [len(p30), len(p29)],
                "macro_cases": macro_cases,
                "checkpoint_replay": replay,
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
