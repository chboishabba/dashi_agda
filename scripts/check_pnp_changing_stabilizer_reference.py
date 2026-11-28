from itertools import product, permutations
from collections import Counter
from random import Random


def move(g, key):
    return tuple(sorted((g[i],v) for i,v in key))


def check():
    rng=Random(36943); G=tuple(permutations(range(6)))
    # Actual subgroup chain from different cut sets; no assumption of freeness.
    groups=[G]+[tuple(g for g in G if {g[i] for i in range(k)}==set(range(k))) for k in range(1,6)]+[G]
    X=tuple(tuple(enumerate(x)) for x in product((0,1),repeat=6))
    checks=0; splits=0; merges=0
    for _ in range(64):
        weights=[rng.randrange(1,20) for _ in range(7)]
        raw={x:weights[sum(v for _,v in x)] for x in X}
        def partition(H):
            D=Counter()
            for x,m in raw.items():D[min(move(g,x) for g in H)]+=m
            return D
        D=partition(groups[0])
        for A,B in zip(groups,groups[1:]):
            J=tuple(sorted(set(A)&set(B))); fine=Counter()
            for x,m in D.items():
                O={move(g,x) for g in A}; u,r=divmod(m,len(O)); assert r==0
                todo=set(O)
                while todo:
                    y=min(todo);P={move(g,y) for g in J};assert P<=todo
                    todo-=P;fine[y]+=u*len(P)
            assert fine==partition(J)
            if len(fine)>len(D):splits+=1
            E=Counter()
            for x,m in fine.items():E[min(move(g,x) for g in B)]+=m
            assert E==partition(B) and sum(E.values())==sum(D.values())
            if len(E)<len(fine):merges+=1
            D=E;checks+=1
    # A consumer may agree now but disagree after a transition.
    f=lambda x:x[0]
    step=lambda x:(x[1],x[0])
    assert f((0,0))==f((0,1)) and f(step((0,0)))!=f(step((0,1)))
    print(dict(partition_transitions=checks,strict_splits=splits,strict_merges=merges,dynamic_negative_control=1))

if __name__=='__main__':check()
