"""Constructive S24 pair-transfer full-Heaps path coupling, exact finite rationals.

Reuses canonical path-law/transport owners. No generic maxflow search needed:
coinciding pair-group/other-label schedules + quantile-coupled second-type
arrival give one coordinatewise ordered full-path coupling.

Classical majorization/coupling probability: Hardy–Littlewood–Pólya (1934),
Strassen (1965), inverse-CDF coupling. Repository source implementation
Johl Brown-directed with OpenAI ChatGPT assistance, 2026-10-28.
Finite executable certificate, NOT a general Agda kernel proof or empirical law.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction
from typing import Sequence

from zipf_heaps_bridge import _validated_counts
from zipf_full_heaps_path_distribution_exact import full_heaps_curve_law
from zipf_s24_monotone_path_transport_exact import (
    PathTransportCertificate, pair_one_type_survival_probability,
)


def pair_switch_truncated_law(
    a: int, b: int, draws: int, sampler: str,
) -> dict[int, Fraction]:
    """T=first pair-draw count with both labels, capped to H+1.

    H=draws for IID, and min(draws,a+b) for finite permutation.
    Probability at k in [1,H]: survival(k-1)-survival(k).
    Probability H+1: survival(H). For H=0 the cap is T'=1 surely.
    """
    if (type(a) is not int or type(b) is not int or min(a,b) <= 0
            or type(draws) is not int or not 0 <= draws <= 14
            or sampler not in ('iid', 'permutation')):
        raise ValueError('positive pair, horizon 0..14 and valid sampler required')
    h = min(draws, a+b) if sampler == 'permutation' else draws
    survival = [pair_one_type_survival_probability(a,b,m,sampler)
                for m in range(h+1)]
    out = {k: survival[k-1]-survival[k]
           for k in range(1,h+1) if survival[k-1] > survival[k]}
    if survival[h] > 0:
        out[h+1] = survival[h]
    assert sum(out.values(), Fraction()) == 1 and all(v>0 for v in out.values())
    return out


def quantile_ordered_pair_switches(
    original: dict[int,Fraction], concentrated: dict[int,Fraction],
) -> dict[tuple[int,int],Fraction]:
    """Monotone inverse-CDF coupling (T_concentrated >= T_original).

    Inputs are normalized finite integer-valued distributions; output order
    is (concentrated_switch, original_switch).
    """
    def validate(law):
        if (not law or sum(law.values(), Fraction()) != 1
                or any(type(t) is not int or t < 1 or type(p) is not Fraction or p<=0
                       for t,p in law.items())):
            raise ValueError('positive normalized exact switch-time law required')
    validate(original)
    validate(concentrated)
    old=sorted(original.items())
    new=sorted(concentrated.items())
    i=j=0
    oi, oj=old[0][1], new[0][1]
    coupling=defaultdict(Fraction)
    while i<len(old) and j<len(new):
        weight=min(oi,oj)
        if new[j][0] < old[i][0]:
            raise ValueError('switch-time stochastic order violated')
        coupling[(new[j][0],old[i][0])] += weight
        oi-=weight
        oj-=weight
        if oi==0:
            i+=1
            if i<len(old): oi=old[i][1]
        if oj==0:
            j+=1
            if j<len(new): oj=new[j][1]
    assert i==len(old) and j==len(new)
    assert sum(coupling.values(),Fraction())==1
    for t,p in new:
        assert sum((v for (x,_),v in coupling.items() if x==t),Fraction())==p
    for t,p in old:
        assert sum((v for (_,x),v in coupling.items() if x==t),Fraction())==p
    return dict(coupling)


def _common_group_schedules(
    counts: tuple[int,...], pair: tuple[int,int], horizon: int, sampler: str,
) -> dict[tuple[int,...],Fraction]:
    """Common sequence of group labels: -1=affected pair, i=other type.

    Both compared models have the identical distribution of this sequence.
    For IID group counts are immutable. For permutation group counts decrement.
    """
    i,j=pair
    total=sum(counts)
    group={-1:counts[i]+counts[j]}
    group.update({q:c for q,c in enumerate(counts) if q not in pair})
    out={((), tuple(group.values())): Fraction(1)}
    labels=tuple(group)
    for step in range(horizon):
        nxt=defaultdict(Fraction)
        for (seq,remaining),mass in out.items():
            for idx,code in enumerate(labels):
                available=group[code] if sampler=='iid' else remaining[idx]
                if not available: continue
                updated=remaining
                if sampler=='permutation':
                    updated=tuple((x-1 if q==idx else x) for q,x in enumerate(remaining))
                nxt[(seq+(code,),updated)] += mass*Fraction(
                    available, total if sampler=='iid' else total-step)
        out=nxt
        if len(out)>20000:
            raise ValueError('shared outer schedule budget exceeded')
    aggregate=defaultdict(Fraction)
    for (seq,_),mass in out.items():aggregate[seq]+=mass
    assert sum(aggregate.values(),Fraction())==1
    return dict(aggregate)


def _pair_curve(seq: tuple[int,...], switch: int) -> tuple[int,...]:
    others=set()
    n_pair=0
    curve=[0]
    for code in seq:
        if code==-1: n_pair+=1
        else: others.add(code)
        curve.append(len(others)+(0 if n_pair==0 else 1 if n_pair<switch else 2))
    return tuple(curve)


def constructive_pair_transfer_path_certificate(
    original: Sequence[int], pair: tuple[int,int], horizon: int,
    sampler: str,
) -> PathTransportCertificate:
    """Witness path monotonicity for the actual single transfer.

    Counts at pair (i,j) change (a,b) -> (a+1,b-1), a>=b>=2.
    Return the previously-owned PathTransportCertificate for concentrated
    versus original, with exactly checked full-path PMF marginals.
    """
    f=_validated_counts(original)
    if (type(pair) is not tuple or len(pair)!=2 or
            any(type(v) is not int or v not in range(len(f)) for v in pair)
            or pair[0]==pair[1]):
        raise ValueError('two distinct valid integer pair indexes required')
    i,j=pair
    a,b=f[i],f[j]
    if a<b or b<2:
        raise ValueError('positive concentrating transfer a>=b>=2 required')
    if (type(horizon) is not int or horizon<0 or horizon>12
            or sampler not in ('iid','permutation')
            or (sampler=='permutation' and horizon>sum(f))):
        raise ValueError('valid sampler and finite horizon <=12 required')
    g=tuple(x+(1 if k==i else -1 if k==j else 0) for k,x in enumerate(f))
    original_switch=pair_switch_truncated_law(a,b,horizon,sampler)
    concentrated_switch=pair_switch_truncated_law(a+1,b-1,horizon,sampler)
    switches=quantile_ordered_pair_switches(original_switch,concentrated_switch)
    outer=_common_group_schedules(f,pair,horizon,sampler)
    coupling=defaultdict(Fraction)
    for seq,outer_mass in outer.items():
        for (late,early),switch_mass in switches.items():
            left=_pair_curve(seq,late)
            right=_pair_curve(seq,early)
            assert all(x<=y for x,y in zip(left,right))
            coupling[(left,right)]+=outer_mass*switch_mass
    left_law=full_heaps_curve_law(g,horizon,sampler)
    right_law=full_heaps_curve_law(f,horizon,sampler)
    assert sum(coupling.values(),Fraction())==1
    certificate=PathTransportCertificate(g,f,sampler,horizon,
        left_law,right_law,dict(coupling),Fraction(1))
    certificate.validate()
    return certificate
