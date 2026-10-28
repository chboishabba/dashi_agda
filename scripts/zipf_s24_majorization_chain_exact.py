"""Constructive finite-horizon S24 majorization transport by transfer-chain gluing.

Reuse existing single-pair constructive coupling and PathTransportCertificate.
Exact rational Markov gluing: gamma_(C,A)(c,a)=sum_b gamma_(C,B)(c,b)*
 gamma_(B,A)(b,a)/P_B(b). Intermediate curves with zero mass are skipped.
No generic max-flow search and no new probability ontology.

Classical roots: HLP 1934 positive-integer majorization, Strassen 1965,
finite disintegration/gluing. New bounded algorithm: Johl Brown-directed
with ChatGPT assistance 2026-10-28; NOT an Agda kernel theorem.
"""
from __future__ import annotations
from collections import defaultdict, deque
from fractions import Fraction
from typing import Sequence

from zipf_heaps_bridge import _validated_counts, multiset_count_majorizes
from zipf_full_heaps_path_distribution_exact import full_heaps_curve_law
from zipf_s24_monotone_path_transport_exact import PathTransportCertificate
from zipf_s24_pair_switch_constructive_exact import constructive_pair_transfer_path_certificate


def _sorted_counts(xs):
    return tuple(sorted(xs,reverse=True))


def positive_majorization_transfer_chain(
    concentrated: Sequence[int], dispersed: Sequence[int], max_states: int = 10000
) -> tuple[tuple[tuple[int,...], tuple[int,int], tuple[int,...]],...]:
    """Exact BFS on sorted integer partitions, each move concentrates 1 token.

    Each source state's affected pair (i,j) has a>=b>=2, and the endpoint
    is the sorted relabeling of the concrete source transfer. This is a
    finite integer decomposition, NOT a claimed direct source Agda theorem.
    """
    f=_validated_counts(concentrated)
    g=_validated_counts(dispersed)
    if (len(f)!=len(g) or sum(f)!=sum(g)
            or not multiset_count_majorizes(f,g)
            or type(max_states) is not int or max_states<1):
        raise ValueError('equal K,N, actual majorization and positive budget required')
    start=_sorted_counts(g)
    goal=_sorted_counts(f)
    if start==goal:return ()
    parents={start:None}
    queue=deque([start])
    while queue and goal not in parents:
        current=queue.popleft()
        for i in range(len(current)):
            for j in range(len(current)):
                if i==j or current[i]<current[j] or current[j]<2:
                    continue
                updated=tuple(x+(1 if q==i else -1 if q==j else 0)
                              for q,x in enumerate(current))
                next_state=_sorted_counts(updated)
                if next_state==current or next_state in parents:
                    continue
                if len(parents)>=max_states:
                    raise ValueError('transfer search state budget exceeded')
                parents[next_state]=(current,(i,j))
                queue.append(next_state)
    if goal not in parents:
        raise AssertionError('positive integer majorization path not found')
    path=[]
    state=goal
    while state!=start:
        former,pair=parents[state]
        path.append((former,pair,state))
        state=former
    path.reverse()
    for former,pair,after in path:
        i,j=pair
        assert former[i]>=former[j]>=2
        produced=tuple(x+(1 if q==i else -1 if q==j else 0)
                       for q,x in enumerate(former))
        assert _sorted_counts(produced)==after
    return tuple(path)


def glue_monotone_path_certificates(
    later: PathTransportCertificate, earlier: PathTransportCertificate
) -> PathTransportCertificate:
    """Exact composition C<=B<=A, preserving both marginal PMFs and order."""
    if (later.sampler != earlier.sampler or later.horizon != earlier.horizon
            or later.right_law != earlier.left_law):
        raise ValueError('shared intermediate full path law and sampler required')
    later.validate()
    earlier.validate()
    new=defaultdict(Fraction)
    # Index the early B->A coupling by its B path, not by token labels.
    early_by_mid=defaultdict(list)
    for (mid,right),mass in earlier.coupling.items():
        early_by_mid[mid].append((right,mass))
    for (left,mid),mass in later.coupling.items():
        pivot=later.right_law[mid]
        assert pivot>0
        for right,second_mass in early_by_mid[mid]:
            assert all(x<=z<=y for x,z,y in zip(left,mid,right))
            new[left,right]+=mass*second_mass/pivot
    cert=PathTransportCertificate(
        later.concentrated,earlier.dispersed,later.sampler,later.horizon,
        later.left_law,earlier.right_law,dict(new),Fraction(1))
    cert.validate()
    return cert


def constructive_majorization_path_certificate(
    concentrated: Sequence[int], dispersed: Sequence[int],
    horizon: int, sampler: str, max_states: int = 10000
) -> PathTransportCertificate:
    """Exact constructive finite S24 certificate for positive count vectors.

    Complete mathematical statement requires unbounded proof of HLP transfer
    reachability and exact probability disintegration. This bounded program
    checks each concrete transfer/coupling against canonical full-path law.
    """
    f=_validated_counts(concentrated)
    g=_validated_counts(dispersed)
    if (type(horizon) is not int or horizon<0 or horizon>12
            or sampler not in ('iid','permutation')
            or (sampler=='permutation' and horizon>sum(f))):
        raise ValueError('valid sampler and bounded horizon required')
    chain=positive_majorization_transfer_chain(f,g,max_states)
    start=_sorted_counts(g)
    if not chain:
        law=full_heaps_curve_law(f,horizon,sampler)
        identity={(path,path):mass for path,mass in law.items()}
        cert=PathTransportCertificate(f,g,sampler,horizon,law,law,identity,Fraction(1))
        cert.validate()
        return cert
    combined=None
    for source,pair,after in chain:
        single=constructive_pair_transfer_path_certificate(source,pair,horizon,sampler)
        after_law=full_heaps_curve_law(after,horizon,sampler)
        assert single.left_law==after_law  # type labels are irrelevant to V(t)
        single=PathTransportCertificate(after,source,sampler,horizon,
            after_law,single.right_law,single.coupling,Fraction(1))
        single.validate()
        combined=single if combined is None else glue_monotone_path_certificates(single,combined)
    assert combined is not None
    assert combined.left_law==full_heaps_curve_law(f,horizon,sampler)
    assert combined.right_law==full_heaps_curve_law(g,horizon,sampler)
    final=PathTransportCertificate(f,g,sampler,horizon,
        combined.left_law,combined.right_law,combined.coupling,Fraction(1))
    final.validate()
    return final
