#!/usr/bin/env python3
"""Independent bounded controls for Karp signed MaxCut ↔ spin-Laplacian.

This tests the exact finite object from Karp21SignedLaplacianCutExact.agda.
Do NOT infer Agda kernel acceptance, eigenvalue approximation bounds, or
general NP-completeness from these exhaustive *small* graphs.

Source original: R. M. Karp (1972), DOI 10.1007/978-1-4684-2001-2_9.
Repository donors: dashi_agda #1415, #1416 (spectral evidence classes),
#1438 (specific finite nonnegative weighted 27-grid max-cut).
"""

from itertools import combinations, product


def signed_cut(edges: tuple[tuple[int, int, int], ...],
               labels: tuple[bool, ...]) -> int:
    return sum(w for i, j, w in edges if labels[i] != labels[j])


def signed_spin_quadratic(edges: tuple[tuple[int, int, int], ...],
                          labels: tuple[bool, ...]) -> int:
    spins = tuple(1 if label else -1 for label in labels)
    return sum(w * (spins[i] - spins[j]) ** 2 for i, j, w in edges)


def check() -> None:
    count = 0
    yes_count = 0
    no_count = 0
    for n in range(5):
        pairs = tuple(combinations(range(n), 2))
        # Includes genuinely negative and zero edge weights; never assume PSD.
        for weights in product((-2, -1, 0, 1, 2), repeat=len(pairs)):
            edges = tuple((i, j, w) for (i, j), w in zip(pairs, weights))
            for labels in product((False, True), repeat=n):
                score = signed_cut(edges, labels)
                laplacian = signed_spin_quadratic(edges, labels)
                assert 4 * score == laplacian, (n, edges, labels)
                flipped = tuple(not label for label in labels)
                assert signed_cut(edges, flipped) == score
                assert signed_spin_quadratic(edges, flipped) == laplacian
                # A positive integer threshold is Karp's target domain.
                for threshold in (1, 4):
                    assert ((score >= threshold) ==
                            (signed_cut(edges, flipped) >= threshold))
                yes_count += score >= 1
                no_count += score < 1
                count += 1
    negative_edge = ((0, 1, -1),)
    negative_labels = (True, False)
    assert signed_cut(negative_edge, negative_labels) == -1
    assert signed_spin_quadratic(negative_edge, negative_labels) == -4
    assert yes_count and no_count
    print(f"PASS signed Laplacian finite bridge: {count} graphs/labels; "
          f"YES {yes_count}, NO {no_count}; signed PSD counterexample")


if __name__ == "__main__":
    check()
