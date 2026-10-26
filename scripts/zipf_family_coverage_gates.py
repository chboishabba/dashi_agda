"""Scoped observational diagnostics for under-covered Zipf-family hypotheses.

Each statistic has an explicit observational unit, finite sample boundary, and
no automatic population-level, causal, historical or asymptotic promotion.
Statistical roots belong to their original authors, not this adapter.
"""
from __future__ import annotations
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from math import log2
from typing import Mapping, Sequence


def _nonnegative_int_counts(values: Sequence[int], *, require_positive=False) -> tuple[int, ...]:
    a = tuple(values)
    if not a or any(type(x) is not int or x < 0 for x in a) or (require_positive and not any(a)):
        raise ValueError('nonempty nonnegative integer counts with requested positive total')
    return a


def participation_roles(readers: Sequence[int], commenters: Sequence[int], creators: Sequence[int]) -> tuple[Fraction, Fraction, Fraction]:
    """Per-identified-account mutually exclusive creator/commenter/noncontributor tiers.

    Readers = recorded views; an account with no recorded views or actions is
    still in the denominator. The final tier includes inactive people and must
    not be interpreted automatically as observed readership/lurking.
    """
    if not (len(readers) == len(commenters) == len(creators)):
        raise ValueError('three vectors must refer to identical enrolled accounts')
    r = _nonnegative_int_counts(readers); c = _nonnegative_int_counts(commenters); k = _nonnegative_int_counts(creators)
    creator = sum(v > 0 for v in k)
    commenter = sum(v > 0 and k[i] == 0 for i,v in enumerate(c))
    noncontributor = len(k)-creator-commenter
    return tuple(Fraction(x,len(k)) for x in (creator,commenter,noncontributor))


def benford_observed_digits(values:Sequence[float], base:int=10)->tuple[Fraction,...]:
    """Observed empirical first digits (not proof of scale invariance)."""
    from zipf_family_formal import leading_digit
    if type(base) is not int or base < 2: raise ValueError('base>=2')
    if not values: raise ValueError('nonempty sample')
    counts = Counter(leading_digit(x,base) for x in values)
    return tuple(Fraction(counts[d],len(values)) for d in range(1,base))


def bradford_optimal_equal_zones(journal_counts:Sequence[int],zones:int)->tuple[tuple[int,int],...]:
    """Brute-force minimum sum-of-squared deviations from equal article zones.

    Journal groups must be contiguous when sorted descending. This is a finite
    descriptive optimum, NOT a test that journal zone sizes form 1:n:n^2.
    """
    c = _nonnegative_int_counts(journal_counts,require_positive=True)
    if type(zones) is not int or not 1 <= zones <= len(c): raise ValueError('1<=zones<=journals')
    c = tuple(sorted(c,reverse=True)); total=sum(c)
    prefix=(0,)
    for x in c:prefix+=(prefix[-1]+x,)
    # Dynamic program: each transition chooses one nonempty contiguous zone.
    # This replaces O(binomial(n,z)) cut enumeration with O(z*n^2).
    states = {(0,0):(0,())}
    for groups in range(1,zones+1):
        for end in range(groups,len(c)+1):
            best = None
            for start in range(groups-1,end):
                previous = states.get((groups-1,start))
                if previous is None:continue
                cost,cuts = previous
                zone_cost = (zones*(prefix[end]-prefix[start])-total)**2
                candidate = (cost+zone_cost,cuts+((start,) if groups>1 else ()))
                if best is None or candidate < best:best=candidate
            if best is not None:states[groups,end]=best
    cuts=states[zones,len(c)][1]
    endpoints=(0,)+cuts+(len(c),)
    return tuple((endpoints[i+1]-endpoints[i],prefix[endpoints[i+1]]-prefix[endpoints[i]]) for i in range(zones))


def type_level_brevity_covariance(frequencies:Mapping[str,int],lengths:Mapping[str,int])->Fraction:
    """Unweighted covariance of length and frequency across observed TYPES."""
    if not frequencies or set(frequencies)!=set(lengths) or any(type(f) is not int or f<1 for f in frequencies.values()) or any(type(v) is not int or v<0 for v in lengths.values()):
        raise ValueError('positive counts; type-aligned nonnegative lengths')
    words=sorted(frequencies); n=len(words)
    sum_l=sum(lengths[w] for w in words);sum_f=sum(frequencies[w] for w in words)
    return Fraction(sum(lengths[w]*frequencies[w] for w in words),n)-Fraction(sum_l*sum_f,n*n)


def gibrat_size_growth_covariance(pairs:Sequence[tuple[int,int]])->Fraction:
    """Exact covariance of initial size against rational proportional growth.

    Zero covariance does not establish the Gibrat independence hypothesis.
    """
    p=tuple(pairs)
    if not p or any(len(pair)!=2 or any(type(v) is not int or v<=0 for v in pair) for pair in p):
        raise ValueError('positive integer size before/after for each entity')
    n=len(p); sizes=[x for x,y in p];ratios=[Fraction(y,x) for x,y in p]
    return sum((x*r for x,r in zip(sizes,ratios)),Fraction())/n-Fraction(sum(sizes),n)*sum(ratios,Fraction())/n


def empirical_block_entropy(tokens:Sequence[str],block_size:int)->float:
    """Sliding-window plug-in H(block) in bits, not a stationary entropy rate."""
    if type(block_size) is not int or not 1<=block_size<=len(tokens):
        raise ValueError('1<=block_size<=corpus size')
    observations=[tuple(tokens[i:i+block_size]) for i in range(len(tokens)-block_size+1)]
    hist=Counter(observations);N=len(observations)
    return sum(-float(Fraction(v,N))*log2(float(Fraction(v,N))) for v in hist.values())


def novelty_run_lengths(tokens:Sequence[str])->tuple[tuple[bool,int],...]:
    from zipf_heaps_bridge import equal_flag_runs,novelty_flags
    return equal_flag_runs(novelty_flags(tokens))


def menzerath_empirical_means(wholes:Sequence[Sequence[int]])->tuple[tuple[int,Fraction,int],...]:
    """Average component length by number of components, no fitted law.

    Each whole is a positive number of strictly-positive constituent sizes;
    reports n, mean of per-whole part lengths, number of wholes.
    """
    if not wholes or any(not w or any(type(x) is not int or x<=0 for x in w) for w in wholes):
        raise ValueError('nonempty wholes with positive constituents')
    groups:dict[int,list[Fraction]]={}
    for w in wholes:groups.setdefault(len(w),[]).append(Fraction(sum(w),len(w)))
    return tuple((n,sum(vals,Fraction())/len(vals),len(vals)) for n,vals in sorted(groups.items()))


def lotka_author_productivity(authors:Mapping[str,int])->tuple[tuple[int,int],...]:
    """Observed author count by output count; includes zeroes if specified."""
    if not authors or any(type(x) is not int or x<0 for x in authors.values()):raise ValueError('nonempty explicit author population')
    freq=Counter(authors.values())
    return tuple(sorted(freq.items()))


def observed_choice_regret(costs:Mapping[str,Fraction],chosen:str)->Fraction:
    """Choice cost above lowest available; no unobserved psychological cause."""
    if not costs or chosen not in costs or any(not isinstance(v,Fraction) for v in costs.values()):raise ValueError('finite explicit alternatives')
    return costs[chosen]-min(costs.values())


@dataclass(frozen=True)
class SourcePriority:
    label:str
    eponym:str
    original_author:str
    original_document:str
    original_year:int
    credit_document:str
    credit_year:int


def documented_eponym_gap(row:SourcePriority)->bool:
    if not row.original_document or not row.credit_document or not row.original_author or not row.eponym or row.original_year>row.credit_year:
        raise ValueError('original and naming documentary roots with chronology required')
    return row.eponym!=row.original_author


def coded_historical_recurrence(events:Sequence[tuple[int,str,str]])->tuple[tuple[str,int,int,str,str],...]:
    """Two matching event codes + their distinct evidence references."""
    if any(not root or not code for _,code,root in events):raise ValueError('event records require sources and code')
    return tuple((code,d1,d2,r1,r2) for i,(d1,code,r1) in enumerate(events)
                 for d2,code2,r2 in events[i+1:] if code==code2 and d1<d2)
