"""Exact first-discovery ORDER law shared by two different samplers.

For strictly positive fixed counts f_i, both:
  (1) IID type draws with replacement, probabilities f_i/N, and
  (2) a uniform permutation of the N distinguishable original tokens
induce the SAME size-biased order of first appearance of types.

The WAITING TIMES and prefix-vocabulary laws do NOT thereby agree.

Original priority: R.D. Luce, Individual Choice Behavior (1959);
R.L. Plackett, The Analysis of Permutations (1975), JRSS C 24:193-202,
https://doi.org/10.2307/2346567; classical occupancy/size bias.
Repo implementation: Johl Brown-directed, OpenAI ChatGPT-assisted,
2026-10-28; NOT a new stochastic law, kernel proof or empirical inference.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import factorial
from typing import Sequence

from zipf_abc_six_order_receipt import ABC_ORDERS
from zipf_heaps_bridge import _validated_counts, expected_iid_vocabulary, expected_permutation_vocabulary


def first_seen_type_order(tokens: Sequence[int]) -> tuple[int, ...]:
    seen=set()
    out=[]
    for token in tokens:
        if type(token) is not int or token<0:
            raise ValueError("nonnegative integer type identities required")
        if token not in seen:
            seen.add(token)
            out.append(token)
    return tuple(out)


def size_biased_order_law(counts: Sequence[int]) -> dict[tuple[int, ...], Fraction]:
    """Classical Plackett-Luce law on K! first-discovery type orders.

    This is a fixed-K *order* distribution, not a random full token-word
    law or an empirical ranking/choice model.
    """
    c = _validated_counts(counts)
    if len(c)>7:
        raise ValueError("explicit enumeration capped at K<=7")
    n=sum(c)
    law={}
    for order in permutations(range(len(c))):
        remaining=n
        p=Fraction(1)
        for i in order:
            p*=Fraction(c[i],remaining)
            remaining-=c[i]
        assert remaining==0
        law[order]=p
    assert sum(law.values(), Fraction())==1
    return law


def uniform_multiset_first_seen_order_law(counts: Sequence[int]) -> dict[tuple[int,...],Fraction]:
    """Independent finite sample-space enumeration, not PL formula reuse.

    Counts are mandatory, every token order is drawn uniformly. Since
    repeated labels are indistinguishable, each DISTINCT label sequence
    has equal probability under a uniform physical-token permutation.
    """
    c=_validated_counts(counts)
    if sum(c)>9:
        raise ValueError("exhaustive without-replacement audit capped at N<=9")
    labels=tuple(i for i,f in enumerate(c) for _ in range(f))
    words=set(permutations(labels))
    expected=factorial(len(labels))
    for f in c: expected//=factorial(f)
    assert len(words)==expected
    frequencies=Counter(first_seen_type_order(word) for word in words)
    return {order:Fraction(freq,len(words)) for order,freq in sorted(frequencies.items())}


def iid_next_novel_type_probability(counts: Sequence[int],
                                   seen: Sequence[int], next_type: int) -> Fraction:
    """Sum the geometric waiting-time series for the NEXT *new* type.

    At each draw, any already-seen type repeats with mass p_seen.
    The probability the next unseen label is j is p_j/(1-p_seen),
    even though the geometric waiting time itself can be unbounded.
    """
    c=_validated_counts(counts)
    k=len(c)
    s=tuple(seen)
    if (len(set(s))!=len(s) or
            any(type(i) is not int or not 0<=i<k for i in s) or
            type(next_type) is not int or next_type not in range(k)
            or next_type in s):
        raise ValueError("distinct valid seen types and a genuinely new next type")
    remaining=sum(c[i] for i in range(k) if i not in s)
    return Fraction(c[next_type],remaining)


def first_discovery_two_sampler_certificate(
    counts: Sequence[int]
) -> dict[str,dict[tuple[int,...],Fraction]]:
    """For finite audit cases, compare independent uniform multiset count
    with IID embedded first-new-type jumps, and original PL formula.
    """
    c=_validated_counts(counts)
    if sum(c)>9 or len(c)>7:
        raise ValueError("finite independent audit requires N<=9, K<=7")
    reference=size_biased_order_law(c)
    iid={}
    for order in permutations(range(len(c))):
        p=Fraction(1)
        for j,i in enumerate(order):
            p*=iid_next_novel_type_probability(c,order[:j],i)
        iid[order]=p
    permutation=uniform_multiset_first_seen_order_law(c)
    assert reference==iid==permutation
    return {"plackett_luce":reference,"iid_first_discovery":iid,
            "uniform_permutation_first_discovery":permutation}


def abc_first_discovery_receipt() -> dict:
    """AABC three-type case: same first-order law, unequal prefix times."""
    c=(2,1,1)
    laws=first_discovery_two_sampler_certificate(c)
    ref=laws["plackett_luce"]
    alphabet=lambda order:"".join("ABC"[i] for i in order)
    named={alphabet(order):p for order,p in ref.items()}
    assert set(named)==set(ABC_ORDERS)
    assert named=={
        "ABC":Fraction(1,4),"ACB":Fraction(1,4),
        "BAC":Fraction(1,6),"BCA":Fraction(1,12),
        "CAB":Fraction(1,6),"CBA":Fraction(1,12),
    }
    p=tuple(Fraction(f,sum(c)) for f in c)
    iid_v2=expected_iid_vocabulary(p,2)
    perm_v2=expected_permutation_vocabulary(c,2)
    assert iid_v2==Fraction(13,8)
    assert perm_v2==Fraction(11,6)
    assert iid_v2!=perm_v2
    return {"order_probabilities":named,
            "iid_expected_v2":iid_v2,
            "permutation_expected_v2":perm_v2}
