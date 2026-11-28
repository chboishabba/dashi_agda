"""Acceptance against exhaustive original witnesses and actual numeric compiler."""
from itertools import product
from random import Random
from check_pnp_conditional_autarky import accepts
from check_pnp_stack_fractran import compile_stack
from check_pnp_hyperfabric_owned_joins import (
    Budget, Refused, extract_disjoint_interiors, discover_and_join,
    overlapping_join, literal_instruction, fresh_epoch_events,
)


def oracle(F,n,rows,target,exterior=(),anchor=()):
    return [x for x in product((0,1),repeat=n)
            if all(x[i]==anchor[i] for i in exterior)
            and accepts(F,x)
            and tuple(sum(a*b for a,b in zip(row,x))%3 for row in rows)==target]


def main():
    if not __debug__: raise RuntimeError("assertions required")
    rng=Random(3691128); joins=separators=literal=epochs=0
    for _ in range(48):
        n=5; bags=((0,1,2),(1,2,3),(2,3,4))
        F=tuple(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(b,rng.randrange(1,4)))
                for b in bags for _ in range(2))
        rows=tuple(tuple(rng.randrange(3) for _ in range(n)) for _ in range(2))
        for t in product(range(3),repeat=2):
            out=overlapping_join(F,n,bags,rows,t,10**7)
            want=oracle(F,n,rows,t)
            assert out is not None and out[0]==len(want)
            assert (out[1] in want) if want else out[1] is None
            assert overlapping_join(F,n,bags,rows,t,0) is None
            joins+=1
        # Source-derived separator for a path.
        G=tuple((i,i+1) for i in range(1,n))
        x=tuple(rng.randrange(2) for _ in range(n))
        out=discover_and_join(G,n,x,rows,(0,0),10**7,2,2)
        assert out is not None
        k,w,work,S,D=out
        want=oracle(G,n,rows,(0,0),S,x)
        assert k==len(want) and ((w in want) if want else w is None)
        assert len(S)<=2 and max(map(len,D),default=0)<=2
        assert all(sum(bool({abs(l)-1 for l in c}&set(d)) for d in D)<=1 for c in G)
        separators+=1
    try:
        extract_disjoint_interiors((tuple(range(1,7)),),6,1,2,Budget(10**6))
        raise AssertionError("clique must refuse")
    except Refused: pass
    for blank in (0,1):
        for direction in (-1,0,1):
            for write in (0,1):
                M=compile_stack(1,2,blank,((0,0,0,write,direction),))
                for L in ((),(0,),(1,)):
                    for R in ((0,),(1,),(0,1)):
                        v=M.encode(0,L,R)
                        assert literal_instruction(M,v,100000,10000) is not None
                        assert literal_instruction(M,v,0,10000) is None
                        literal+=1
    # Erasing a state does not imply fresh output-relevant collisions.
    X=tuple(product((0,1),repeat=3))
    state=lambda x,t: 0 if t%2==0 else x[t//2]
    obs=lambda x,t: x[t//2] if t%2==0 else 0
    for x in X:
        receipt=fresh_epoch_events(x,X,state,lambda y:y[0]^y[1]^y[2],obs,(0,2,4,6))
        assert not receipt
        receipt=fresh_epoch_events(x,X,state,lambda y:y[0]^y[1]^y[2],obs,(0,1,2,3,4,5,6))
        assert len(receipt)==3 and len({e[2] for e in receipt})==3
        epochs+=1
    print(dict(overlap_fibres=joins,separator_fibres=separators,literal_instructions=literal,epoch_anchors=epochs))


if __name__=="__main__": main()
