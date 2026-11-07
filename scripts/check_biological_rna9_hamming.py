#!/usr/bin/env python3
"""Cross-check native RNA9 Hamming semantics against DASHI's existing DNA codec.

Alphabet conversion is literal U->T for the equal-length Hamming metric only.
This is not a biochemical, regulatory or phenotype equivalence certificate.
"""
from __future__ import annotations

import itertools
import json
import random
import runpy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
codec_hamming = runpy.run_path(str(ROOT / "tools/dna_production_codec.py"))["hamming"]
BASES = "ACGU"
SEED = 1471


def rna9_distance(left: str, right: str) -> int:
    if len(left) != 9 or len(right) != 9 or any(
        base not in BASES for base in left + right
    ):
        raise ValueError("expected two nine-symbol RNA strings")
    return sum(a != b for a, b in zip(left, right, strict=True))


def main() -> None:
    rng = random.Random(SEED)
    count = 0
    directed_neighbours = 0
    for letters in itertools.product(BASES, repeat=9):
        genotype = "".join(letters)
        assert rna9_distance(genotype, genotype) == 0
        assert codec_hamming(genotype.replace("U", "T"), genotype.replace("U", "T")) == 0
        for position in range(9):
            for replacement in BASES:
                if replacement == genotype[position]:
                    continue
                other = genotype[:position] + replacement + genotype[position + 1:]
                assert rna9_distance(genotype, other) == 1
                assert rna9_distance(other, genotype) == 1
                assert codec_hamming(genotype.replace("U", "T"), other.replace("U", "T")) == 1
                directed_neighbours += 1
        count += 1

    for _ in range(20000):
        left = "".join(rng.choices(BASES, k=9))
        right = "".join(rng.choices(BASES, k=9))
        forward = rna9_distance(left, right)
        assert forward == rna9_distance(right, left)
        assert forward == codec_hamming(left.replace("U", "T"), right.replace("U", "T"))

    assert count == 4**9 == 262144
    assert directed_neighbours == count * 9 * 3
    assert directed_neighbours // 2 == 3538944
    # Source-pinned first two dmsC genotypes, thousandth-scaled raw replicates.
    first, second = "AAAAAAAAA", "AAAAAAAAC"
    assert rna9_distance(first, second) == 1
    assert sum((256, 769, 664)) == 3 * 563
    assert sum((389, 908, 695)) == 3 * 664
    assert 664 - 563 == 101
    print(json.dumps({
        "result": "passed",
        "alphabet": BASES,
        "rna9_genotypes_exhaustively_checked": count,
        "directed_hamming_one_edges": directed_neighbours,
        "undirected_hamming_one_edges": directed_neighbours // 2,
        "random_pair_codec_parity_checks": 20000,
        "original_dmsc_pair_hamming": 1,
        "original_dmsc_mean_difference_thousandths": 101,
        "claims_excluded": ["kinetic calibration", "phenotype equivalence", "tissue attractor"],
    }, indent=2))


if __name__ == "__main__":
    main()
