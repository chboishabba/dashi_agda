"""Three-draw Heaps collision-moment law and all-distinct conditioning.

REUSE existing, source-owned:
  zipf_heaps_bridge._validated_counts (positive integer probability weights)
  zipf_full_heaps_path_distribution_exact.full_heaps_curve_law (IID PMF)
  zipf_first_discovery_plackett_luce_exact.size_biased_order_law (PL order)

For IID probabilities p_i>0, S2=sum p_i^2 and S3=sum p_i^3:
  P(V=[0,1,1,1]) = S3
  P(V=[0,1,1,2]) = S2-S3
  P(V=[0,1,2,2]) = 2(S2-S3)
  P(V=[0,1,2,3]) = 1-3S2+2S3.
This is an exact symmetric-polynomial PUSHFORWARD of named word laws.

For K IID draws from all K strictly positive types, CONDITIONED on
seeing all types EXACTLY ONCE in those K draws, each named order has
probability 1/K! regardless of unequal p_i. This is *not* the
unconditioned first-discovery order: Luce (1959)/Plackett (1975).

Original mathematics: elementary occupancy, probability conditioning,
symmetric power sums, Heaps/Herdan/Zipf and Luce/Plackett. New bounded
source adapter: Johl Brown-directed, OpenAI ChatGPT-assisted, 2026-10-28.
Numerical coincidences, uniform conditional order and 3^3/S3 sizes
DO NOT identify the 27-cube semantics or Monster/Spin/NS/RH objects.
Python checks are not an Agda kernel proof.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import permutations
from math import factorial
from typing import Sequence

from zipf_heaps_bridge import _validated_counts
from zipf_full_heaps_path_distribution_exact import full_heaps_curve_law
from zipf_first_discovery_plackett_luce_exact import size_biased_order_law


def iid_three_draw_moment_law(weights: Sequence[int]) -> dict:
    """Exact three-prefix Heaps distribution from S2 and S3.

    Source-weight and probability weights are kept distinct. The
    canonical full_heaps_curve_law owner checks the result independently.
    """
    counts=_validated_counts(weights)
    total=sum(counts)
    p=tuple(Fraction(w,total) for w in counts)
    s2=sum((x*x for x in p),Fraction())
    s3=sum((x*x*x for x in p),Fraction())
    law={
      (0,1,1,1):s3,
      (0,1,1,2):s2-s3,
      (0,1,2,2):2*(s2-s3),
      (0,1,2,3):1-3*s2+2*s3,
    }
    law={curve:mass for curve,mass in law.items() if mass>0}
    assert sum(law.values(),Fraction())==1
    assert law==full_heaps_curve_law(counts,3,"iid")
    return {"law":law,"S2":s2,"S3":s3,"probabilities":p}


def uniform_order_given_all_distinct(weights: Sequence[int]) -> dict:
    """Condition first K IID draws on all K labels appearing exactly once.

    This conditioning is a *different event/measure* from full
    unconditioned first-discovery Plackett-Luce rankings. The uniform
    distribution applies for any positive p_i, not just Zipf exponent 0.
    """
    counts=_validated_counts(weights)
    k=len(counts)
    if k>7:
        raise ValueError("explicit conditioned-order enumeration capped at K<=7")
    total=sum(counts)
    prob_per_order=Fraction(1)
    for w in counts:
        prob_per_order*=Fraction(w,total)
    distinct_event=factorial(k)*prob_per_order
    orders=tuple(permutations(range(k)))
    conditional={order:Fraction(1,factorial(k)) for order in orders}
    assert distinct_event>0 and distinct_event<=1
    assert sum(conditional.values(),Fraction())==1
    # The EXISTING classical size-biased order law is the distinct
    # *unconditioned temporal process* and is not overwritten.
    pl=size_biased_order_law(counts)
    assert len(conditional)==len(pl)
    for order in orders:
        physical_word_mass=Fraction(1)
        for i in order:
            physical_word_mass*=Fraction(counts[i],total)
        assert physical_word_mass==prob_per_order
        assert physical_word_mass/distinct_event==conditional[order]
    return {"distinct_event_probability":distinct_event,
            "conditional_order_law":conditional,
            "unconditioned_first_discovery_law":pl}


def nonuniform_zipf_three_rank_receipt() -> dict:
    """s=1,q=0 finite 3-rank Zipf: weights (1,1/2,1/3).

    Clear denominators -> integer weights (6,3,2).
    This is exactly one of the pre-existing finite-rank Zipf families.
    """
    counts=(6,3,2)
    moments=iid_three_draw_moment_law(counts)
    result=uniform_order_given_all_distinct(counts)
    assert moments["probabilities"]==(
        Fraction(6,11),Fraction(3,11),Fraction(2,11))
    assert moments["S2"]==Fraction(49,121)
    assert moments["S3"]==Fraction(251,1331)
    assert moments["law"]=={
        (0,1,1,1):Fraction(251,1331),
        (0,1,1,2):Fraction(288,1331),
        (0,1,2,2):Fraction(576,1331),
        (0,1,2,3):Fraction(216,1331),
    }
    assert result["distinct_event_probability"]==Fraction(216,1331)
    assert result["conditional_order_law"][(0,1,2)]==Fraction(1,6)
    assert result["unconditioned_first_discovery_law"][(0,1,2)]==Fraction(18,55)
    assert result["conditional_order_law"] != result["unconditioned_first_discovery_law"]
    # An S3 relabeling preserves Heaps observation but not word probability.
    aaa=Fraction(6,11)**3
    ccc=Fraction(2,11)**3
    assert aaa!=ccc
    return {"moments":moments,"distinct_conditioning":result,
            "same_heaps_curve_word_probabilities":(aaa,ccc)}


def iid_three_draw_equality_pattern_law(weights: Sequence[int]) -> dict:
    """Exact fine equality-pattern pushforward for three IID draws.

    AAB, ABA, ABB each have mass S2-S3 even for unequal named weights.
    The original named word law need NOT be invariant under relabelling.
    """
    counts=_validated_counts(weights)
    coarse=iid_three_draw_moment_law(counts)
    s2,s3=coarse["S2"],coarse["S3"]
    fine={
        "AAA":s3,
        "AAB":s2-s3,
        "ABA":s2-s3,
        "ABB":s2-s3,
        "ABC":1-3*s2+2*s3,
    }
    fine={name:mass for name,mass in fine.items() if mass>0}
    push={
        (0,1,1,1):fine.get("AAA",Fraction()),
        (0,1,1,2):fine.get("AAB",Fraction()),
        (0,1,2,2):fine.get("ABA",Fraction())+fine.get("ABB",Fraction()),
        (0,1,2,3):fine.get("ABC",Fraction()),
    }
    assert {curve:mass for curve,mass in push.items() if mass>0}==coarse["law"]
    assert sum(fine.values(),Fraction())==1
    return {"pattern_law":fine,"heaps_pushforward":coarse["law"]}
