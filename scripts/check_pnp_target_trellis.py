"""Exact target-conditioned F3 trellis on original Boolean coordinates.
Reuse systematic image and original RREF; retain clause masks and histogram.
Refusal is transactional, never emptiness. Logical work, not physical time.
"""
from check_pnp_intrinsic_patch import Image
from check_pnp_signed_component_histogram import rref


def trellis(F,cols,target,offset,R,cap):
    R=tuple(R);target=tuple(a%3 for a in target);m=len(target);n=len(R);N=len(cols)
    if cap<0 or len(set(R))!=n or any(not 0<=i<N for i in R) or any(len(c)!=m+1 for c in cols) or any(abs(l)-1 not in R for c in F for l in c):raise ValueError('source')
    stats=dict(work=0,peak=0,probes=0,rank=0,crossing=0)
    def pay(k):
        if stats['work']+k>cap:raise OverflowError('cap')
        stats['work']+=k
    def done(H,P):return (tuple(H),tuple(P)),stats
    def empty():return done((0,0,0),(None,None,None))
    try:
        scan=1+N*(m+1)+n+sum(1+len(c) for c in F)
        pay(scan)
        if () in F:return empty()
        rows=tuple(tuple(c[j] for c in cols) for j in range(m))
        pay((m+1)**2*(n+1)**2)
        I=Image(rows,R);t=I.encode(target);r=len(I.piv);stats['rank']=r
        if t is None:return empty()
        A=tuple(I.key(cols[i][:-1]) for i in R)
        # Row bases of the remaining image, built incrementally. The
        # redundant target coordinates are removed only after membership.
        def extend(B,a):
            pay((r+1)*(len(B)+1)**2*4)
            return tuple(row[:-1] for row in rref(tuple(b+(0,) for b in B+(a,)),r)[0])
        suffix=[()]*(n+1)
        for i in range(n-1,-1,-1):suffix[i]=extend(suffix[i+1],A[i])
        piv=[tuple(next(j for j,v in enumerate(b) if v) for b in B) for B in suffix]
        def member(y,i):
            B=suffix[i];p=piv[i]
            return all(sum(y[k]*b[j] for k,b in zip(p,B))%3==v for j,v in enumerate(y))
        pay((n+1)*(scan+1))
        masks=[tuple(sum(1<<j for j,c in enumerate(F) if (i+1 if b else -i-1) in c) for b in (0,1)) for i in R]
        future=[0]*(n+1)
        for i in range(n-1,-1,-1):future[i]=future[i+1]|masks[i][0]|masks[i][1]
        H=tuple(int(d==offset%3) for d in range(3));P=tuple(0 if h else None for h in H)
        states={(t,(1<<len(F))-1):(H,P)};prefix=()
        for i,(a,ms) in enumerate(zip(A,masks)):
            prefix=extend(prefix,a)
            stats['crossing']=max(stats['crossing'],len(prefix)+len(suffix[i+1])-r)
            pay(2*len(states)*(1+r*(len(suffix[i+1])+1)+len(F)+n))
            nxt={}
            for (y,u),(H,P) in states.items():
                for b in (0,1):
                    stats['probes']+=1;v=u&~ms[b]
                    if v&~future[i+1]:continue
                    z=tuple((x-b*c)%3 for x,c in zip(y,a))
                    if not member(z,i+1):continue
                    h,p=nxt.get((z,v),((0,0,0),(None,None,None)));shift=b*cols[R[i]][-1]%3
                    nh=tuple(h[d]+H[(d-shift)%3] for d in range(3))
                    np=tuple(p[d] if p[d] is not None else None if P[(d-shift)%3] is None else P[(d-shift)%3]|(b<<i) for d in range(3))
                    nxt[z,v]=nh,np
            states=nxt;stats['peak']=max(stats['peak'],len(states))
            if not states:return empty()
        H,P=states.get(((0,)*r,0),((0,0,0),(None,None,None)))
        return done(H,tuple(None if p is None else tuple((p>>i)&1 for i in range(n)) for p in P))
    except OverflowError:return None,stats


def contrast(F,cols,target,offset,R,w,cap):
    q,stats=trellis(F,cols,target,offset,R,cap)
    if q is None:return None
    H,P=q;a=tuple(w*(3*h-sum(H)) for h in H)
    return a,a,dict(stats,head=H)
