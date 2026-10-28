"""SSSP six-order / Heaps finite observation quotient: executable cross-check.

Formal carrier OWNED by DASHI.Computation.SSSPThreeFrontier*:
  abc acb bac bca cab cba, minimum trit and residual tail bit.
This is an independent Python enumeration of that existing Agda surface,
not a new S3 group or a replicated empirical Zipf law.

Mathematics: classical S3/multiset permutations and Heaps first discoveries.
Finite repository synthesis: Johl Brown, with OpenAI ChatGPT assistance,
2026-10-28. No Agda-kernel or empirical sampling claim.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import factorial
from typing import Sequence

from zipf_heaps_bridge import (
    observed_prefix_diversity, novelty_flags,
    multiset_heaps_extremal_profiles, multiset_heaps_area_gap,
    expected_permutation_vocabulary,
)

ABC_ORDERS = ("ABC","ACB","BAC","BCA","CAB","CBA")


def all_distinct_orders() -> tuple[str, ...]:
    """Independent enumeration checked against source-owned Agda constructors."""
    orders = tuple(sorted("".join(x) for x in permutations("ABC")))
    assert orders == ABC_ORDERS
    return orders


def min_tail_encode(word: str) -> tuple[str, int]:
    """Existing SSSP minimum and binary orientation chart, not S3=C6."""
    if word not in ABC_ORDERS:
        raise ValueError("requires one of the six named ABC orders")
    return word[0], int(word[1] > word[2])


def min_tail_decode(code: tuple[str, int]) -> str:
    """Reverse consumer chart: a three-valued minimum plus one tail bit."""
    try:
        minimum, tail = code
    except (TypeError, ValueError) as exc:
        raise ValueError("requires a minimum and one binary tail bit") from exc
    if minimum not in "ABC" or type(tail) is not int or tail not in (0,1):
        raise ValueError("requires A/B/C minimum and 0/1 tail")
    rest = sorted(set("ABC")-{minimum}, reverse=bool(tail))
    return minimum+"".join(rest)


def relation_sheet(word: str) -> tuple[int, ...]:
    """Actual pair-order comparison sheet, row and column ABC order."""
    if word not in ABC_ORDERS:
        raise ValueError("requires an ABC permutation")
    pos = {c:i for i,c in enumerate(word)}
    return tuple((pos[a]>pos[b])-(pos[a]<pos[b])
                 for a in "ABC" for b in "ABC")


def three_unique_order_receipt() -> dict:
    """All six timelines collapse to one complete Heaps curve (0,1,2,3)."""
    orders=all_distinct_orders()
    profiles=tuple(observed_prefix_diversity(o) for o in orders)
    first=Counter(o[0] for o in orders)
    codes=tuple(min_tail_encode(o) for o in orders)
    assert set(profiles)=={(0,1,2,3)}
    assert dict(first)=={"A":2,"B":2,"C":2}
    assert len(set(codes))==6 and len({relation_sheet(o) for o in orders})==6
    assert all(min_tail_decode(code)==word for word,code in zip(orders,codes))
    assert all(novelty_flags(word)==(True,True,True) for word in orders)
    return {"orders":orders, "curve":profiles[0], "minimum_counts":dict(first),
            "minimum_probabilities":{c:Fraction(n,6) for c,n in first.items()},
            "full_curves_distinct":len(set(profiles)),
            "relation_sheets_distinct":len({relation_sheet(o) for o in orders}),
            "min_tail_codes_distinct":len(set(codes))}


def uniform_multiset_curves(counts: Sequence[int]) -> dict[tuple[int, ...], Fraction]:
    """Independent exhaustive physical-token permutation modulo identical labels."""
    c=tuple(counts)
    if not c or any(type(x) is not int or x<=0 for x in c):
        raise ValueError("positive integer type counts required")
    n=sum(c)
    if n>9:
        raise ValueError("only tiny exhaustive multiset witnesses (N<=9)")
    tokens=tuple(i for i,f in enumerate(c) for _ in range(f))
    distinct_words=set(permutations(tokens))
    expected=factorial(n)
    for f in c: expected//=factorial(f)
    assert len(distinct_words)==expected
    histogram=Counter(observed_prefix_diversity(word) for word in distinct_words)
    return {curve:Fraction(freq,len(distinct_words))
            for curve,freq in sorted(histogram.items())}


def repeated_a_three_type_receipt() -> dict:
    """Smallest nontrivial three-type Heaps ambiguity (2,1,1).

    4! / 2! = 12 distinct equiprobable token orders, with a 2/4/6
    partition of their full vocabulary curves. This is finite permutation
    sampling without replacement, not iid with p=(1/2,1/4,1/4).
    """
    c=(2,1,1)
    dist=uniform_multiset_curves(c)
    expected={
        (0,1,1,2,3):Fraction(1,6),
        (0,1,2,2,3):Fraction(1,3),
        (0,1,2,3,3):Fraction(1,2),
    }
    assert dist==expected
    lows, highs=multiset_heaps_extremal_profiles(c)
    assert lows==min(dist) and highs==max(dist)
    assert multiset_heaps_area_gap(c)==2
    for t in range(5):
        from_curves=sum((Fraction(v[t])*mass for v,mass in dist.items()),Fraction())
        from_owner=expected_permutation_vocabulary(c,t)
        assert from_curves==from_owner
    return {"curve_probabilities":dist, "total_distinct_orders":12,
            "lower":lows,"upper":highs,"heaps_area_gap":2}


def two_singletons_prefix_two_gap(m: int) -> dict:
    """Closed finite (m,1,1) two-sampler comparison, all integer m>=1.

    Classical occupancy/collision identities, with no new probability owner:
      E_perm[V2] = 2 - m(m-1)/((m+2)(m+1))
      E_iid[V2]  = 2 - (m^2+2)/(m+2)^2
      difference = 2(2m+1)/((m+1)(m+2)^2) > 0
    Also the existing sharp Heaps all-prefix area gap = 2(m-1).
    """
    if type(m) is not int or m < 1:
        raise ValueError("positive integer repeated-type multiplicity required")
    from zipf_heaps_bridge import expected_iid_vocabulary
    counts=(m,1,1)
    n=m+2
    iid=expected_iid_vocabulary(tuple(Fraction(c,n) for c in counts),2)
    permutation=expected_permutation_vocabulary(counts,2)
    iid_closed=2-Fraction(m*m+2,n*n)
    perm_closed=2-Fraction(m*(m-1),n*(n-1))
    gap=Fraction(2*(2*m+1),(m+1)*n*n)
    area=multiset_heaps_area_gap(counts)
    assert iid==iid_closed and permutation==perm_closed
    assert permutation-iid==gap and gap>0
    assert area==2*(m-1)
    return {"iid_expected_v2":iid,"permutation_expected_v2":permutation,
            "permutation_minus_iid_v2":gap,"extremal_heaps_area_gap":area}
