"""Finite-horizon sensitivity of Heaps discovery to probability/label error.

IID maximal coupling and uniform-permutation shared-token coupling supply
exact rational upper bounds. These are classical coupling ideas (Lindvall,
2002), not newly discovered probability theory. Unlike bounded-horizon
Heaps, expected IID collection time has no uniform continuity near the
simplex boundary. Source/test adaptation: Johl Brown and OpenAI ChatGPT,
28 Oct 2026. No physical or empirical same-object proof.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb
from typing import Sequence

from zipf_heaps_bridge import _validated_counts, _validated_pmf
from zipf_completion_time_exact import completion_cdf, completion_mean


def iid_prefix_total_variation_bound(p: Sequence[Fraction],
                                     q: Sequence[Fraction], draws: int) -> Fraction:
    """Bound on ANY first-t path event: 1-(1-TV(p,q))^t <= t*TV.

    Both distributions must have the same labeled atom support, including
    zeros. The bound also controls any deterministic Heaps/path statistic.
    """
    a, b = _validated_pmf(p), _validated_pmf(q)
    if len(a) != len(b) or type(draws) is not int or draws < 0:
        raise ValueError('same labeled support and nonnegative integer draws')
    tv = sum((abs(x-y) for x,y in zip(a,b)),Fraction()) / 2
    bound = 1 - (1 - tv) ** draws
    assert bound <= min(Fraction(1), draws * tv)
    return bound


def permutation_prefix_total_variation_bound(f: Sequence[int],
                                             g: Sequence[int], draws: int) -> Fraction:
    """Shared-position coupling: P(any mismatch by t) <=1-C(N-D,t)/C(N,t).

    D=0.5*sum_i|f_i-g_i| is the fewest changed labels between two
    individual-token populations; match N-D token positions, permute them
    with a single common uniform random permutation. Requires same N,K.
    """
    a,b=_validated_counts(f),_validated_counts(g)
    if len(a)!=len(b) or sum(a)!=sum(b):
        raise ValueError('same positive-type count and population size')
    n=sum(a)
    if type(draws) is not int or not 0 <= draws <= n:
        raise ValueError('permutation horizon must be between zero and N')
    differences=sum(abs(x-y) for x,y in zip(a,b))
    assert differences%2==0
    changed=differences//2
    result=1-Fraction(comb(n-changed,draws),comb(n,draws))
    assert 0<=result<=1
    return result


def completion_event_stability_certificate(f: Sequence[int],g: Sequence[int],
                                            draws: int) -> dict[str, tuple[Fraction,Fraction]]:
    """Compare P(T<=t) differences to independently derived path bounds.

    The exact completion PMF is from the separate coupon owner. No
    majorization is required: this is robustness for *any* histograms
    with identical token total, positive-type count and label convention.
    """
    a,b=_validated_counts(f),_validated_counts(g)
    if len(a)!=len(b) or sum(a)!=sum(b):
        raise ValueError('same population and declared type labels required')
    n=sum(a)
    if type(draws) is not int or not 0 <= draws <= n:
        raise ValueError('common both-sampler draw horizon must be in [0,N]')
    p=tuple(Fraction(x,n) for x in a)
    q=tuple(Fraction(x,n) for x in b)
    out={}
    for sampler in ('iid','permutation'):
        bound=(iid_prefix_total_variation_bound(p,q,draws)
               if sampler=='iid' else permutation_prefix_total_variation_bound(a,b,draws))
        gap=abs(completion_cdf(a,draws,sampler)-completion_cdf(b,draws,sampler))
        assert gap<=bound
        out[sampler]=(gap,bound)
    return out


def rare_tail_unstable_completion_witness(scale: int) -> tuple[Fraction, Fraction,
                                                               Fraction, Fraction]:
    """Integer two-type family: TV ->0 while IID expected-time ratio ->infinity.

    N=m*m; a=(N-1,1); b=(N-m,m). TV=(m-1)/m^2.
    E_a=N+1/(N-1), E_b=m+1/(m-1), so E_a/E_b>m/2.
    This does NOT contradict finite-time TV coupling bounds, because T
    can be arbitrarily large under IID sampling.
    """
    if type(scale) is not int or scale < 2:
        raise ValueError('integer scale >=2 required')
    n=scale*scale
    a,b=(n-1,1),(n-scale,scale)
    tv=Fraction(scale-1,n)
    ea=completion_mean(a,'iid')
    eb=completion_mean(b,'iid')
    assert ea==n+Fraction(1,n-1)
    assert eb==scale+Fraction(1,scale-1)
    assert ea/eb>Fraction(scale,2)
    return tv,ea,eb,ea/eb
