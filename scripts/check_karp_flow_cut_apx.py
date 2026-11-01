#!/usr/bin/env python3
"""Finite graph controls connecting Edmonds-Karp flow, min cuts and APX.

Original roots: Ford/Fulkerson augmenting paths (1956), Edmonds/Karp BFS
polynomial refinement (1972), classical 1/2 random-cut expectation, classical
maximal-matching 2-approximation for vertex cover. This is source-code finite
regression; no Agda proof or formal complexity certificate is claimed.
"""
from itertools import product, combinations
from collections import deque


def max_flow_min_cut(n, arcs, source=0, sink=None):
    if sink is None: sink = n-1
    assert 0 <= source < n and 0 <= sink < n and source != sink
    original = {(u,v):c for u,v,c in arcs if c}
    assert all(u!=v and c>=0 for u,v,c in arcs)
    residual = [[0]*n for _ in range(n)]
    for u,v,c in arcs: residual[u][v] += c
    flow_value=0
    while True:
        pred={source:-1}
        q=deque([source])
        while q and sink not in pred:
            u=q.popleft()
            for v in range(n):
                if v not in pred and residual[u][v]>0:
                    pred[v]=u; q.append(v)
        if sink not in pred: break
        path=[];v=sink
        while v!=source:
            u=pred[v];path.append((u,v));v=u
        delta=min(residual[u][v] for u,v in path)
        assert delta>0
        for u,v in path:
            residual[u][v]-=delta
            residual[v][u]+=delta
        flow_value+=delta
    reachable={source};queue=[source]
    for u in queue:
        for v in range(n):
            if residual[u][v]>0 and v not in reachable:
                reachable.add(v);queue.append(v)
    cut=sum(c for (u,v),c in original.items() if u in reachable and v not in reachable)
    assert sink not in reachable and cut==flow_value
    net=[sum(original.get((u,v),0)-residual[u][v] for v in range(n)) for u in range(n)]
    assert net[source]==flow_value and net[sink]==-flow_value
    assert all(net[v]==0 for v in range(n) if v not in (source,sink))
    return flow_value, frozenset(reachable)


def exhaustive_st_min_cut(n, arcs, source=0, sink=None):
    if sink is None: sink=n-1
    return min(sum(c for u,v,c in arcs if u in S and v not in S)
               for mask in range(1<<n)
               for S in (frozenset(i for i in range(n) if mask>>i&1),)
               if source in S and sink not in S)


def cut_weight(edges, bits):
    return sum(w for u,v,w in edges if bits[u] != bits[v])


def half_approx_maxcut(n, edges):
    # Conditional expectation, using twice the expected cut score.
    def twice_expectation(partial):
        return sum(2*w*(partial[u]!=partial[v]) if u in partial and v in partial else w
                   for u,v,w in edges)
    partial={}
    for v in range(n):
        c0=twice_expectation(partial|{v:0})
        c1=twice_expectation(partial|{v:1})
        partial[v]=int(c1>c0)
    bits=tuple(partial[i] for i in range(n))
    score=cut_weight(edges,bits)
    assert 2*score >= sum(w for _,_,w in edges)
    return bits,score


def two_approx_vertex_cover(n, edges):
    covered=set();matching=[]
    for u,v in edges:
        if u not in covered and v not in covered:
            matching.append((u,v)); covered|={u,v}
    assert all(u in covered or v in covered for u,v in edges)
    assert len(covered)==2*len(matching)
    return covered,matching


def min_k_cut(n,edges,k):
    assert 2<=k<=n
    # Canonical unlabelled partitions via restricted-growth strings.
    def partitions(prefix,classes):
        if len(prefix)==n:
            if classes==k: yield tuple(prefix)
            return
        for c in range(min(classes+1,k)):
            yield from partitions(prefix+(c,),max(classes,c+1))
    return min(cut_weight(edges,parts) for parts in partitions((0,),1))


def main():
    flow_cases=0;apx_cases=0;cover_cases=0;partition_cases=0
    for n in (2,3):
        ordered=[(u,v) for u in range(n) for v in range(n) if u!=v]
        for cs in product(range(3),repeat=len(ordered)):
            arcs=tuple((u,v,c) for (u,v),c in zip(ordered,cs))
            value,_=max_flow_min_cut(n,arcs)
            assert value==exhaustive_st_min_cut(n,arcs)
            flow_cases+=1
    for n in range(2,6):
        possible=list(combinations(range(n),2))
        for flags in product((0,1),repeat=len(possible)):
            edges=tuple(e for e,on in zip(possible,flags) if on)
            cover,matching=two_approx_vertex_cover(n,edges)
            opt=min(len(chosen) for size in range(n+1) for chosen in combinations(range(n),size)
                    if all(u in chosen or v in chosen for u,v in edges))
            assert len(cover)<=2*opt
            cover_cases+=1
    for n in range(2,5):
        possible=list(combinations(range(n),2))
        for weights in product(range(3),repeat=len(possible)):
            edges=tuple((u,v,w) for (u,v),w in zip(possible,weights) if w)
            _,score=half_approx_maxcut(n,edges)
            opt=max(cut_weight(edges,bits) for bits in product((0,1),repeat=n))
            assert opt<=2*score
            apx_cases+=1
            if n<=4 and all(w in (0,1) for w in weights):
                directed=tuple((u,v,w) for u,v,w in edges for u,v in ((u,v),(v,u)))
                st_min=min(max_flow_min_cut(n,directed,s,t)[0] for s in range(n) for t in range(n) if s!=t)
                assert min_k_cut(n,edges,2)==st_min
                for k in range(3,n+1):
                    assert min_k_cut(n,edges,k)>=min_k_cut(n,edges,2)
                partition_cases+=1
    print('PASS flow networks',flow_cases,'maxcut APX',apx_cases,
          'cover APX',cover_cases,'min-k-cut examples',partition_cases)


if __name__=='__main__':main()
