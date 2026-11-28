"""Scoped hyperfabric welds: disjoint patch convolution, epoch events, compact bit ABI.
No unrestricted time or space claim. The cap is a declared logical-work cap.
"""
from collections import Counter
from itertools import product
from random import Random


def cluster_join(patches, exterior, rows, target, cap):
    """Join existing conditional-project tables over a FIXED exterior.
    Interiors disjoint; no clause may meet two interiors (caller proves this).
    Tables must come from the SAME original clauses and affine rows.
    Returns count and original lift, or None on transactional refusal.
    """
    D = set()
    for P in patches:
        if D.intersection(P['D']): raise ValueError('overlap')
        D.update(P['D'])
    if any(D.intersection(P['S']) or P['rows'] != rows for P in patches):
        raise ValueError('non-exterior boundary or row mismatch')
    if len(rows) != len(target) or cap < 0: raise ValueError('source')
    if any(len(r)!=len(exterior) for r in rows): raise ValueError('rows')
    r = len(rows)
    work = 1 + len(exterior)*(r+1) + sum(len(P['table']) for P in patches)
    if work > cap: return None
    need = tuple((t-sum(a*b for i,(a,b) in enumerate(zip(row,exterior)) if i not in D))%3
                 for row,t in zip(rows,target))
    states = {(0,)*r:(1,())}
    for P in patches:
        s = tuple(exterior[i] for i in P['S'])
        entries = [(y,d,k) for (b,y),(d,k) in P['table'].items() if b==s]
        # Counts have at most n+1 bits; include a conservative arithmetic charge.
        work += len(states)*len(entries)*(1+r+len(exterior))**2
        if work > cap: return None
        nxt = {}
        for z,(count,path) in states.items():
            for y,d,k in entries:
                v = tuple((a+b)%3 for a,b in zip(z,y))
                old,rep = nxt.get(v,(0,path+(d,)))
                nxt[v] = (old+count*k,rep)
        states = nxt
    count,path = states.get(need,(0,()))
    if not count: return 0,None,work
    x = list(exterior)
    for P,d in zip(patches,path):
        for i,b in zip(P['D'],d): x[i]=b
    return count,tuple(x),work


def trace(ask, x, state, fuel):
    """Persistent complete machine state; ask returns (index, continuation)."""
    events=[]
    for _ in range(fuel):
        q=ask(state)
        if q is None: break
        i,k=q
        state=k(x[i]);events.append((i,state))
    return state,events


def epoch_supports(ask,x,alternatives,prefix,fuel):
    """Only actual start collisions and actual end-state separation qualify."""
    start=prefix(x);end,events=trace(ask,x,start,fuel);supports={}
    for y in alternatives:
        if prefix(y)!=start: continue
        other,other_events=trace(ask,y,start,fuel)
        if end==other: continue
        S=frozenset(i for i,(a,b) in enumerate(zip(x,y)) if a!=b)
        # First actual post-state divergence; equal prior states give equal addresses.
        k=next(k for k,(a,b) in enumerate(zip(events,other_events)) if a[1]!=b[1])
        assert events[k][0]==other_events[k][0] and events[k][0] in S
        supports.setdefault(S,k)
    minimal={s:k for s,k in supports.items() if not any(t<s for t in supports)}
    assert all(any(i in s for i,_ in events) for s in minimal)
    return minimal,events


def encode_index(k):
    """Canonical unsigned big-endian index; one zero byte for zero."""
    if k<0: raise ValueError('index')
    return k.to_bytes(max(1,(k.bit_length()+7)//8),'big')


def compact_query(D, frame):
    """Layout is resident and fixed; the frame contains only the query index.
    This is a compact executable ABI, not a target single-tape implementation.
    """
    if not frame or (len(frame)>1 and frame[0]==0): raise ValueError('canonical frame')
    k=int.from_bytes(frame,'big')
    return D.bit(k),8*len(frame)


def main():
    if not __debug__: raise RuntimeError('assertions required')
    from check_pnp_conditional_autarky import project, accepts
    from check_pnp_cook_quadratic_seek import QuadraticCookSeek
    from check_pnp_cook_affine_seek_campaign import reference
    C=Counter();g=Random(3692901)
    for _ in range(96):
        # Two connected two-variable interiors, one shared exterior coordinate.
        F=((1,2),(2,-3),(4,5),(-4,3))
        rows=tuple(tuple(g.randrange(3) for _ in range(5)) for _ in range(2))
        patches=tuple(project(F,5,D,100000,rows=rows)[0] for D in ((0,1),(3,4)))
        for b in (0,1):
            x=(0,0,b,0,0)
            for t in product(range(3),repeat=2):
                out=cluster_join(patches,x,rows,t,100000)
                want=[y for y in product((0,1),repeat=5) if y[2]==b and accepts(F,y) and tuple(sum(a*v for a,v in zip(row,y))%3 for row in rows)==t]
                assert out is not None and out[0]==len(want)
                assert (out[1] in want) if want else out[1] is None
                assert cluster_join(patches,x,rows,t,0) is None
                C['cluster_fibres']+=1
    for n in range(1,7):
        X=list(product((0,1),repeat=n))
        # Adaptive read order, parity retained. At termination no extra read.
        def ask(s):
            k,v=s
            if k>=n:return None
            i=k if not v else n-1-k
            return i,lambda b:(k+1,v^b)
        for x in X:
            for a in range(n+1):
                prefix=lambda y:trace(ask,y,(0,0),a)[0]
                M,E=epoch_supports(ask,x,X,prefix,n-a)
                for s,k in M.items():assert E[k][0] in s
                C['epoch_anchors']+=1;C['minimal_events']+=len(M)
    for j in range(40):
        T=j%4;w=1+j%2;r=1+j%2
        def clauses(N):return tuple(tuple((i,g.randrange(2)) for i in g.sample(range(N),g.randrange(min(N,3)+1))) for _ in range(j%3))
        D=QuadraticCookSeek(T,w,r,clauses(r+6*w),clauses(1+w),(0,)*w,tuple(g.randrange(2) for _ in range(3*w)))
        want=reference(D)
        assert len(want)==D.length()
        for i,t in enumerate(want):
            for b in range(3):
                k=3*i+b;v,paid=compact_query(D,encode_index(k))
                assert v==(t>>(2-b))&1 and paid>=max(1,k.bit_length())
                C['compact_bits']+=1
        assert compact_query(D,encode_index(3*len(want)))[0] is None
    # Large fixed layout, queried only by compact binary index.
    D=QuadraticCookSeek(10**100,1,1,(((0,1),(1,0)),),(((0,1),),),(0,),(0,1,0))
    starts=[0,D.transition_prefix(D.T),D.transition_prefix(D.T)+D.initial_prefix(D.R),D.length()-1]
    for k in starts:
        assert tuple(compact_query(D,encode_index(3*k+b))[0] for b in range(3))==tuple(((6 if k!=D.length()-1 else 4)>>(2-b))&1 for b in range(3))
        C['huge_boundaries']+=1
    print(dict(C))

if __name__=='__main__':main()
