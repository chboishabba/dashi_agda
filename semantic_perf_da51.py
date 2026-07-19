#!/usr/bin/env python3
"""Dashi semantic annotation and Fractran compilation for DA51/perf traces.

This module is the executable companion to DASHI.Perf.SemanticTrace:

* surface rows remain reconstructible without loss;
* ``dashi_class`` and ``dashi_family`` are attached by a small, explicit
  classifier;
* semantic motif tokens ignore process-local surface noise;
* repeated semantic motifs can be compiled into an ordered Fractran program.

The initial classifier is intentionally conservative.  It is a bridge into the
Dashi witness vocabulary, not a claim that all repository modules have already
been classified theorem-by-theorem.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence


DASHI_CLASSES = {
    "proof-check",
    "witness-export",
    "compression-step",
    "fractran-step",
    "shard-transport",
    "unknown-class",
}

DASHI_FAMILIES = {
    "proof-family",
    "witness-family",
    "compression-family",
    "execution-family",
    "transport-family",
    "unknown-family",
}


@dataclass(frozen=True)
class SemanticLabel:
    dashi_class: str
    dashi_family: str


@dataclass(frozen=True)
class SemanticToken:
    dashi_class: str
    dashi_family: str


@dataclass(frozen=True)
class Fraction:
    numerator: int
    denominator: int
    meaning: str

    def as_text(self) -> str:
        return f"{self.numerator}/{self.denominator}"


# Stable primes used by the small semantic-motif compiler.  Dynamic motif
# primes are allocated above this fixed control/register surface.
PRIMES = {
    "row": 2,
    "literal": 3,
    "candidate": 5,
    "model_cost": 7,
    "saved": 11,
    "step0": 13,
    "step1": 17,
    "step2": 19,
    "halt": 23,
}

_DYNAMIC_PRIMES = [29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]


def classify_file(file_name: str, *, has_fractran: bool = False) -> SemanticLabel:
    """Assign the initial Dashi semantic label for one DA51 source file."""
    stem = Path(file_name).stem.lower()

    if has_fractran or "fractran" in stem:
        return SemanticLabel("fractran-step", "execution-family")
    if any(part in stem for part in ("perfhistory", "da51trace", "da51tag", "moonshineearn")):
        return SemanticLabel("witness-export", "witness-family")
    if any(part in stem for part in ("compression", "mdl", "compact", "projectiondefect")):
        return SemanticLabel("compression-step", "compression-family")
    if any(part in stem for part in ("shard", "cbor", "transport", "ipfs")):
        return SemanticLabel("shard-transport", "transport-family")
    if file_name.endswith(".agda"):
        return SemanticLabel("proof-check", "proof-family")
    return SemanticLabel("unknown-class", "unknown-family")


def annotate_record(record: dict[str, Any]) -> dict[str, Any]:
    """Return a structure-preserving record with Dashi semantic labels."""
    file_name = str(record.get("file", ""))
    label = classify_file(file_name, has_fractran="fractran" in record)
    annotated = dict(record)
    annotated["dashi_class"] = label.dashi_class
    annotated["dashi_family"] = label.dashi_family
    return annotated


def erase_annotation(record: dict[str, Any]) -> dict[str, Any]:
    """Erase only semantic labels, recovering the original surface record."""
    erased = dict(record)
    erased.pop("dashi_class", None)
    erased.pop("dashi_family", None)
    return erased


def semantic_token(record: dict[str, Any]) -> SemanticToken:
    if "dashi_class" not in record or "dashi_family" not in record:
        record = annotate_record(record)
    return SemanticToken(str(record["dashi_class"]), str(record["dashi_family"]))


def mine_semantic_motifs(
    records: Sequence[dict[str, Any]],
    *,
    min_len: int = 2,
    max_len: int = 4,
    min_support: int = 2,
) -> list[tuple[SemanticToken, ...]]:
    tokens = [semantic_token(record) for record in records]
    counts: Counter[tuple[SemanticToken, ...]] = Counter()
    for width in range(min_len, max_len + 1):
        for start in range(0, len(tokens) - width + 1):
            counts[tuple(tokens[start : start + width])] += 1

    # MDL proxy: a motif must save more token positions than its definition and
    # one reference token cost.  Exact byte accounting belongs downstream in
    # FRACDASH; this gate establishes the semantic promotion contract upstream.
    promoted = [
        motif
        for motif, support in counts.items()
        if support >= min_support and support * len(motif) > len(motif) + support
    ]
    promoted.sort(key=lambda motif: (counts[motif] * len(motif), len(motif)), reverse=True)
    return promoted


def compile_motif_to_fractran(
    motif: Sequence[SemanticToken],
    *,
    motif_index: int = 0,
    support_threshold: int = 2,
) -> list[Fraction]:
    """Compile one promoted semantic motif into a small ordered Fractran lane.

    The compiler emits the same guarded lifecycle used by the executable
    compressor: literal fallback, support accumulation, MDL-gated promotion,
    and reuse after promotion.  Token-specific matching primes are allocated
    deterministically from the motif index and token position.
    """
    needed = 2 + len(motif)
    base = motif_index * needed
    if base + needed > len(_DYNAMIC_PRIMES):
        raise ValueError("motif compiler prime budget exhausted")

    motif_prime = _DYNAMIC_PRIMES[base]
    use_prime = _DYNAMIC_PRIMES[base + 1]
    token_primes = _DYNAMIC_PRIMES[base + 2 : base + 2 + len(motif)]

    step0 = PRIMES["step0"]
    step1 = PRIMES["step1"]
    step2 = PRIMES["step2"]
    halt = PRIMES["halt"]
    row = PRIMES["row"]
    literal = PRIMES["literal"]
    candidate = PRIMES["candidate"]
    model_cost = PRIMES["model_cost"]
    saved = PRIMES["saved"]

    token_product = 1
    for prime in token_primes:
        token_product *= prime

    return [
        Fraction(
            numerator=use_prime * halt,
            denominator=step0 * motif_prime * token_product,
            meaning="reuse promoted semantic motif",
        ),
        Fraction(
            numerator=literal * step1,
            denominator=step0 * row,
            meaning="literal fallback",
        ),
        Fraction(
            numerator=candidate * step2,
            denominator=step1 * literal,
            meaning="accumulate semantic motif support",
        ),
        Fraction(
            numerator=motif_prime * saved * halt,
            denominator=step2 * (candidate**support_threshold) * model_cost,
            meaning="MDL-gated semantic motif promotion",
        ),
        Fraction(
            numerator=halt,
            denominator=step2,
            meaning="finish without promotion",
        ),
    ]


def enrich_summary(records: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    return [annotate_record(record) for record in records]


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Annotate DA51 summaries with Dashi semantics.")
    parser.add_argument("input", type=Path, help="DA51 summary JSON")
    parser.add_argument("output", type=Path, help="semantic summary JSON")
    parser.add_argument(
        "--fractran-output",
        type=Path,
        help="optional JSON description of Fractran lanes for promoted semantic motifs",
    )
    return parser


def main() -> None:
    args = build_parser().parse_args()
    records = json.loads(args.input.read_text(encoding="utf-8"))
    if not isinstance(records, list):
        raise TypeError("DA51 summary must be a JSON list")

    enriched = enrich_summary(records)
    args.output.write_text(json.dumps(enriched, indent=2) + "\n", encoding="utf-8")

    if args.fractran_output is not None:
        motifs = mine_semantic_motifs(enriched)
        compiled = []
        for index, motif in enumerate(motifs[:4]):
            fractions = compile_motif_to_fractran(motif, motif_index=index)
            compiled.append(
                {
                    "motif": [token.__dict__ for token in motif],
                    "fractions": [
                        {
                            "fraction": fraction.as_text(),
                            "numerator": fraction.numerator,
                            "denominator": fraction.denominator,
                            "meaning": fraction.meaning,
                        }
                        for fraction in fractions
                    ],
                }
            )
        args.fractran_output.write_text(json.dumps(compiled, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
