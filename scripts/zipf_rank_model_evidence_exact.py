"""Predeclared finite rank comparisons, without universal power-law promotion.

Exact conditional IID likelihoods of ranked categories use a fixed, explicitly
declared rank dictionary. Fitting a rank ordering on the holdout data and
then scoring it as independent would invalidate the evidence contract.
Classical multinomial likelihood and information-theoretic model selection
remain attributed to their mathematical/statistical origins; this bounded
source-written adapter: Johl Brown with OpenAI ChatGPT assistance, 2026-10-27.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence
from zipf_heaps_bridge import finite_rank_probabilities


def _counts(observations: Sequence[int]) -> tuple[int, ...]:
    c=tuple(observations)
    if not c or any(type(n) is not int or n<0 for n in c):
        raise ValueError('nonempty rank-aligned nonnegative integer counts required')
    return c


def finite_geometric_probabilities(n:int,ratio:Fraction)->tuple[Fraction,...]:
    """Truncated geometric rank model: P_r ∝ ratio^(r-1), 0<ratio<=1."""
    if type(n) is not int or n<1 or not isinstance(ratio,Fraction) or not 0<ratio<=1:
        raise ValueError('n>=1, rational geometric ratio in (0,1]')
    w=tuple(ratio**i for i in range(n));norm=sum(w,Fraction())
    return tuple(x/norm for x in w)


def exact_rank_likelihood(counts:Sequence[int],masses:Sequence[Fraction])->Fraction:
    """IID sequence likelihood with known fixed category labels; omit common multinomial factor."""
    c=_counts(counts);p=tuple(masses)
    if len(c)!=len(p) or any(not isinstance(x,Fraction) or x<0 for x in p) or sum(p,Fraction())!=1:
        raise ValueError('declared ranks must align with a normalized rational PMF')
    likelihood=Fraction(1)
    for count,mass in zip(c,p):
        likelihood *= mass**count
    return likelihood


def select_finite_rank_model(counts:Sequence[int],candidates:Sequence[tuple[str,tuple[Fraction,...]]])->tuple[str,Fraction]:
    """Compare predeclared candidate models on fixed-rank held-out counts."""
    c=_counts(counts);options=tuple(candidates)
    if sum(c)==0:
        raise ValueError('no held-out observations: model selection is not evidence')
    if not options or len({label for label,_ in options})!=len(options):
        raise ValueError('nonempty unique preregistered candidate identifiers')
    scores=[(label,exact_rank_likelihood(c,pmf)) for label,pmf in options]
    # Deterministic lexical tie rule. A maximum is a *relative fit*, not truth.
    return sorted(scores,key=lambda row:(-row[1],row[0]))[0]


def exact_unseen_tail_probability(masses:Sequence[Fraction],head_count:int,draws:int)->Fraction:
    """Probability that IID draws miss ALL tail types despite positive tail mass."""
    p=tuple(masses)
    if (not p or any(not isinstance(x,Fraction) or x<0 for x in p)
            or sum(p,Fraction())!=1 or type(head_count) is not int
            or not 0<=head_count<=len(p) or type(draws) is not int or draws<0):
        raise ValueError('normalized rational PMF, 0<=head<=K, draws>=0')
    return sum(p[:head_count],Fraction())**draws


@dataclass(frozen=True)
class FixedRankEvidence:
    """Input audit gate; not an inferential significance or provenance proof."""
    original_source_root: str
    rank_dictionary_id: str
    train_split_id: str
    heldout_split_id: str
    independent_draws_declared: bool
    alternative_models_preregistered: bool


def admit_rank_likelihood(evidence:FixedRankEvidence)->bool:
    return bool(evidence.original_source_root and evidence.rank_dictionary_id and
                evidence.train_split_id and evidence.heldout_split_id and
                evidence.train_split_id!=evidence.heldout_split_id and
                evidence.independent_draws_declared and evidence.alternative_models_preregistered)
