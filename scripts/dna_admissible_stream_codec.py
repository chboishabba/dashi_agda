#!/usr/bin/env python3
"""Deterministic variable-arity DNA admissibility codec.

This is a reversible choice-index codec.  At each position the encoder computes
A(state) in canonical A,C,G,T order and consumes one digit in radix |A(state)|.
Ternary is therefore used exactly when the admissible fibre has arity three;
it is not imposed on one-, two-, or four-way fibres.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Sequence

BASES = "ACGT"
COMPLEMENT = str.maketrans("ACGT", "TGCA")


def reverse_complement(sequence: str) -> str:
    return sequence.translate(COMPLEMENT)[::-1]


@dataclass(frozen=True)
class Constraints:
    max_run: int = 4
    gc_min_fraction: float = 0.40
    gc_max_fraction: float = 0.60
    gc_slack: int = 8
    forbidden_motifs: tuple[str, ...] = ()
    hairpin_min_stem: int = 6
    hairpin_history: int = 64


@dataclass
class State:
    sequence: list[str] = field(default_factory=list)
    gc_count: int = 0
    last_base: str | None = None
    run_length: int = 0

    def append(self, base: str) -> "State":
        return State(
            sequence=[*self.sequence, base],
            gc_count=self.gc_count + int(base in "GC"),
            last_base=base,
            run_length=self.run_length + 1 if self.last_base == base else 1,
        )


def has_forbidden_suffix(sequence: str, motifs: Sequence[str]) -> bool:
    return any(sequence.endswith(motif) for motif in motifs)


def has_bounded_hairpin(sequence: str, min_stem: int, history: int) -> bool:
    """Exact bounded string predicate; deliberately separate from ΔG scoring."""
    tail = sequence[-history:]
    n = len(tail)
    for stem in range(min_stem, n // 2 + 1):
        left = tail[-stem:]
        rc = reverse_complement(left)
        # Require a nonempty loop between the paired arms.
        for loop in range(1, n - 2 * stem + 1):
            start = n - stem - loop - stem
            if start >= 0 and tail[start : start + stem] == rc:
                return True
    return False


def gc_prefix_possible(state: State, constraints: Constraints) -> bool:
    n = len(state.sequence)
    if n == 0:
        return True
    low = constraints.gc_min_fraction * n - constraints.gc_slack
    high = constraints.gc_max_fraction * n + constraints.gc_slack
    return low <= state.gc_count <= high


def admissible_bases(state: State, constraints: Constraints) -> list[str]:
    choices: list[str] = []
    for base in BASES:
        candidate = state.append(base)
        sequence = "".join(candidate.sequence)
        if candidate.run_length > constraints.max_run:
            continue
        if has_forbidden_suffix(sequence, constraints.forbidden_motifs):
            continue
        if not gc_prefix_possible(candidate, constraints):
            continue
        if has_bounded_hairpin(sequence, constraints.hairpin_min_stem, constraints.hairpin_history):
            continue
        choices.append(base)
    return choices


def encode_choice_digits(digits: Sequence[int], constraints: Constraints) -> tuple[str, list[int]]:
    state = State()
    radices: list[int] = []
    output: list[str] = []
    for position, digit in enumerate(digits):
        choices = admissible_bases(state, constraints)
        radix = len(choices)
        if radix == 0:
            raise ValueError(f"no admissible base at position {position}; restart required")
        if not 0 <= digit < radix:
            raise ValueError(f"digit {digit} is outside radix {radix} at position {position}")
        base = choices[digit]
        output.append(base)
        radices.append(radix)
        state = state.append(base)
    return "".join(output), radices


def decode_choice_digits(sequence: str, constraints: Constraints) -> tuple[list[int], list[int]]:
    state = State()
    digits: list[int] = []
    radices: list[int] = []
    for position, base in enumerate(sequence):
        choices = admissible_bases(state, constraints)
        if base not in choices:
            raise ValueError(f"sequence violates codec constraints at position {position}")
        digits.append(choices.index(base))
        radices.append(len(choices))
        state = state.append(base)
    return digits, radices


def load_constraints(args: argparse.Namespace) -> Constraints:
    return Constraints(
        max_run=args.max_run,
        gc_min_fraction=args.gc_min,
        gc_max_fraction=args.gc_max,
        gc_slack=args.gc_slack,
        forbidden_motifs=tuple(args.forbidden),
        hairpin_min_stem=args.hairpin_min_stem,
        hairpin_history=args.hairpin_history,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("encode", "decode"))
    parser.add_argument("--digits", type=Path)
    parser.add_argument("--sequence")
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--max-run", type=int, default=4)
    parser.add_argument("--gc-min", type=float, default=0.40)
    parser.add_argument("--gc-max", type=float, default=0.60)
    parser.add_argument("--gc-slack", type=int, default=8)
    parser.add_argument("--forbidden", nargs="*", default=[])
    parser.add_argument("--hairpin-min-stem", type=int, default=6)
    parser.add_argument("--hairpin-history", type=int, default=64)
    args = parser.parse_args()
    constraints = load_constraints(args)

    if args.mode == "encode":
        if args.digits is None:
            parser.error("encode requires --digits JSON")
        digits = json.loads(args.digits.read_text(encoding="utf-8"))
        sequence, radices = encode_choice_digits(digits, constraints)
        payload = {"sequence": sequence, "digits": digits, "radices": radices}
    else:
        if args.sequence is None:
            parser.error("decode requires --sequence")
        digits, radices = decode_choice_digits(args.sequence.upper(), constraints)
        payload = {"sequence": args.sequence.upper(), "digits": digits, "radices": radices}

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
