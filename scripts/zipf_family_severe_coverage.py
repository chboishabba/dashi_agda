"""Severe assumption gates for original Zipf-family coverage (2026-10-27).

Reuses the typed 27-entry atlas and existing finite Bradford optimizer.
The additional constructions repair two observational distinctions:
- An observed *lurker* must have an observed read/view, not just no posts.
- When a declared Bradford convention preserves tied journals, journals
  with identical publication counts may not be split across zones.
These are mathematical / diagnostic adapters, not universal empirical laws.
Original authors: Hill/Nielsen for participation inequality; Bradford (1934),
later tie-handling applications and bibliometric authors for scattering.
Repository adapter: Johl Brown with OpenAI ChatGPT assistance.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from importlib import import_module
from typing import Sequence

import zipf_family_formal as family


def measured_participation_four_tiers(
    reads: Sequence[int], comments: Sequence[int], creations: Sequence[int]
) -> tuple[Fraction, Fraction, Fraction, Fraction]:
    """(creator, commenter-only, observed-lurker, inactive/unknown) fractions.

    A read is an observed event (not inferred from enrolment); contribution
    priority is creator > commenter > reader. The population denominator is
    the declared collection of accounts, and is NOT assumed representative.
    """
    samples = (tuple(reads), tuple(comments), tuple(creations))
    if not samples[0] or any(len(v) != len(samples[0]) for v in samples):
        raise ValueError("equal nonempty identified-account vectors required")
    if any(type(x) is not int or x < 0 for v in samples for x in v):
        raise ValueError("nonnegative integer observations required")
    n = len(samples[0])
    creators = sum(c > 0 for c in samples[2])
    commenters = sum(c == 0 and m > 0 for m, c in zip(samples[1], samples[2]))
    lurkers = sum(c == 0 and m == 0 and r > 0
                  for r, m, c in zip(*samples))
    inactive = n - creators - commenters - lurkers
    return tuple(Fraction(x, n) for x in (creators, commenters, lurkers, inactive))


def bradford_tie_preserving_zones(
    journal_counts: Sequence[int], zones: int
) -> tuple[tuple[int, int], ...]:
    """Optimal equal-ARTICLE contiguous zones that never split equal-count ranks.

    Squared deviation from exact equal article mass is minimized. Lexicographic
    cut order resolves ties deterministically. An impossible number of
    nonempty tie-preserving zones raises ValueError rather than inventing a
    split. Zeros are allowed as journals with no articles only for an
    explicitly declared corpus; they form their own final tie block.
    """
    counts = tuple(journal_counts)
    if (not counts or any(type(x) is not int or x < 0 for x in counts)
            or sum(counts) <= 0 or type(zones) is not int or zones < 1):
        raise ValueError("nonempty, nonnegative journal counts, positive zones")
    ranked = tuple(sorted(counts, reverse=True))
    n = len(ranked)
    allowed = (0,) + tuple(i for i in range(1, n) if ranked[i] != ranked[i - 1]) + (n,)
    blocks = len(allowed) - 1
    if zones > blocks:
        raise ValueError("not enough distinct contiguous tie blocks for zones")
    prefix = (0,)
    for count in ranked:
        prefix += (prefix[-1] + count,)
    total = prefix[-1]
    # State (zones_used, boundary_index) -> (cost, tuple of internal endpoints).
    states = {(0, 0): (0, ())}
    for z in range(1, zones + 1):
        for b in range(z, blocks + 1):
            best = None
            for a in range(z - 1, b):
                previous = states.get((z - 1, a))
                if previous is None:
                    continue
                cost, cuts = previous
                actual = prefix[allowed[b]] - prefix[allowed[a]]
                candidate = (cost + (zones * actual - total) ** 2,
                             cuts + ((allowed[a],) if z > 1 else ()))
                if best is None or candidate < best:
                    best = candidate
            if best is not None:
                states[z, b] = best
    cuts = states[zones, blocks][1]
    endpoints = (0,) + cuts + (n,)
    return tuple((endpoints[i + 1] - endpoints[i],
                  prefix[endpoints[i + 1]] - prefix[endpoints[i]])
                 for i in range(zones))


@dataclass(frozen=True)
class CoverageContract:
    key: str
    module: str
    function: str
    scope: str


# Exact user-requested topics, no derived/adjacent entries masquerading as
# replacements. A callable is a code-surface receipt, NOT kernel proof.
COVERAGE = (
    CoverageContract("zipf", "zipf_family_formal", "zipf_mandelbrot", "rank model"),
    CoverageContract("one_percent", __name__, "measured_participation_four_tiers", "observed accounts"),
    CoverageContract("benford", "zipf_family_formal", "benford_first_digit", "mathematical base"),
    CoverageContract("bradford", __name__, "bradford_tie_preserving_zones", "journal tie blocks"),
    CoverageContract("brevity", "zipf_family_coverage_gates", "type_level_brevity_covariance", "type lengths"),
    CoverageContract("demographic_gravitation", "zipf_family_formal", "demographic_gravity", "population distance"),
    CoverageContract("word_list", "zipf_family_formal", "word_list", "declared token corpus"),
    CoverageContract("gibrat", "zipf_family_coverage_gates", "gibrat_size_growth_covariance", "entity panel"),
    CoverageContract("hapax", "zipf_family_formal", "hapaxes", "tokenized corpus"),
    CoverageContract("heaps", "zipf_heaps_bridge", "expected_iid_vocabulary", "IID draws"),
    CoverageContract("hilberg", "zipf_family_coverage_gates", "empirical_block_entropy", "block observations"),
    CoverageContract("historical_recurrence", "zipf_family_coverage_gates", "coded_historical_recurrence", "source-coded events"),
    CoverageContract("king", "zipf_family_formal", "king_effect_ratio", "rank baseline"),
    CoverageContract("long_tail", "zipf_family_formal", "long_tail_share", "finite support"),
    CoverageContract("lorenz", "zipf_family_formal", "lorenz_curve", "nonnegative distribution"),
    CoverageContract("lotka", "zipf_family_coverage_gates", "lotka_author_productivity", "author identity"),
    CoverageContract("menzerath", "zipf_family_coverage_gates", "menzerath_empirical_means", "hierarchical units"),
    CoverageContract("pareto_distribution", "zipf_family_formal", "pareto_cdf", "positive support"),
    CoverageContract("pareto_principle", "zipf_family_formal", "top_share", "declared cutoff"),
    CoverageContract("price", "zipf_family_formal", "price_share", "author productivity"),
    CoverageContract("least_effort", "zipf_family_coverage_gates", "observed_choice_regret", "choice cost"),
    CoverageContract("rank_size", "zipf_family_formal", "rank_size", "finite sorted sizes"),
    CoverageContract("stigler", "zipf_family_coverage_gates", "documented_eponym_gap", "dated primary sources"),
    CoverageContract("letter_frequency", "zipf_family_formal", "letter_frequencies", "declared alphabet"),
    CoverageContract("common_english", "zipf_family_formal", "common_words", "declared English corpus"),
    CoverageContract("zipf_mandelbrot", "zipf_heaps_bridge", "finite_rank_probabilities", "integer shifted powers"),
    CoverageContract("hurwitz", "zipf_heaps_bridge", "finite_hurwitz_sum", "finite rational series"),
)


def audit_coverage_contract() -> tuple[str, ...]:
    """Fail closed when a topic disappears or its advertised API is absent."""
    keys = tuple(c.key for c in COVERAGE)
    canon = {entry.key for entry in family.ATLAS}
    if len(keys) != 27 or len(set(keys)) != 27 or set(keys) != canon:
        raise AssertionError("original request does not have exactly 27 typed owners")
    for entry in COVERAGE:
        module = import_module(entry.module)
        if not callable(getattr(module, entry.function, None)):
            raise AssertionError(f"{entry.key}: missing {entry.module}.{entry.function}")
    return keys
