"""Overlapping F3 normal-factor histogram fold, on the original affine chart.
Reuses binary normal-boundary join geometry and F3 chart/character owners.
Only completed exact tables escape; width/work refusals are not emptiness.
"""
from itertools import product
from functools import lru_cache
from collections import defaultdict
from check_pnp_f3_syndrome_boundary import chart,span,orth,dot,convolve,ZERO,Refusal


def normal_fold(F,cols,target,offset,R,leaf_width=6,boundary_width=3,work_cap=16384):
    R=tuple(sorted(R));n=len(R);stats=dict(work=0,width=0,leaf_labels=0,join_pairs=0,factors=0)
    def pay(k):
        if stats['work']+k>work_cap:raise Refusal('work')
        stats['work']+=k
    def value(A,z):return tuple(dot(a,z) for a in A)
    def intersection(A,B,d):return span(orth(span(orth(A,d)+orth(B,d),d),d),d)
    try:
        pay(1+n+len(target)+sum(1+len(c) for c in F))
        q=chart(tuple(tuple(cols[v][i] for v in R) for i in range(len(target))),target,n)
        if q is None:return ZERO,stats
        u,V=q;d=len(V);pos={v:i for i,v in enumerate(R)}
        N=tuple(tuple(v[i] for v in V) for i in range(n))
        if any(a==2 and not any(b) for a,b in zip(u,N)) or () in F:return ZERO,stats
        factors=[]
        # Guard every original coordinate, including eliminated pivots.
        for a,b in zip(u,N):
            if any(b):factors.append(((b,),(a,),0))
        for c in F:
            I=tuple(pos[abs(l)-1] for l in c)
            if any(not any(N[i]) and u[i]==int(l>0) for i,l in zip(I,c)):continue
            factors.append((tuple(N[i] for i in I),tuple(u[i]-int(l>0) for i,l in zip(I,c)),1))
        obs=tuple(sum(cols[v][-1]*z[i] for i,v in enumerate(R))%3 for z in V)
        o=(offset+sum(cols[v][-1]*u[i] for i,v in enumerate(R)))%3
        factors.append(((obs,),(o,),2))
        factors.sort(key=lambda f:next((j for j in range(d) if any(a[j] for a in f[0])),d))
        m=len(factors);stats['factors']=m;full=(1<<m)-1
        @lru_cache(None)
        def U(mask):
            pay(1);return span((a for i,(A,_,_) in enumerate(factors) if mask>>i&1 for a in A),d)
        @lru_cache(None)
        def D(mask):
            pay(1);return intersection(U(mask),U(full^mask),d)
        def maps(A,B):
            # Express each row of B as linear combination of rows of A.
            pay(1+len(B));eq=tuple(tuple(a[i] for a in A) for i in range(d));out=[]
            for b in B:
                q=chart(eq,b,len(A));assert q is not None
                out.append(q[0])
            return tuple(out)
        assert len(U(full))==d # free original coordinates were guarded
        nodes=[(1<<i,None,None) for i in range(m)]
        while len(nodes)>1:
            choices=((i,j) for i in range(len(nodes)) for j in range(i+1,len(nodes))) if len(nodes)<=12 else ((i,i+1) for i in range(len(nodes)-1))
            best=None
            for i,j in choices:
                pay(1);mask=nodes[i][0]|nodes[j][0];key=(len(D(mask)),mask.bit_count(),mask,i,j)
                if best is None or key<best:best=key
            _,_,mask,i,j=best;A,B=nodes[i],nodes[j];nodes.pop(j);nodes[i]=(mask,A,B)
        def insert(T,k,h):T[k]=tuple(a+b for a,b in zip(T.get(k,ZERO),h))
        def run(node):
            mask,A,B=node;S=D(mask);stats['width']=max(stats['width'],len(S));T={}
            if len(S)>boundary_width:raise Refusal('width')
            if A is None:
                F,a,kind=factors[mask.bit_length()-1];C=U(mask)
                if len(C)>leaf_width:raise Refusal('leaf width')
                P,Q=maps(C,F),maps(C,S);pay(3**len(C));stats['leaf_labels']+=3**len(C)
                for z in product(range(3),repeat=len(C)):
                    y=tuple((x+t)%3 for x,t in zip(value(P,z),a))
                    if kind==0 and y[0]==2:continue
                    if kind==1 and not any(x==0 for x in y):continue
                    h=tuple(int(j==(y[0] if kind==2 else 0)) for j in range(3))
                    insert(T,value(Q,z),h)
                return T
            L=run(A);J=run(B)
            if not L or not J:return T
            E,G=D(A[0]),D(B[0]);I=intersection(U(A[0]),U(B[0]),d)
            P,Q,Z=maps(E,I),maps(G,I),maps(E+G,S);buckets=defaultdict(list)
            for r,h in J.items():pay(1);buckets[value(Q,r)].append((r,h))
            for l,h in L.items():
                pay(1)
                for r,k in buckets[value(P,l)]:
                    pay(1);stats['join_pairs']+=1;insert(T,value(Z,l+r),convolve(h,k))
            return T
        return run(nodes[0]).get((),ZERO),stats
    except (Refusal,RecursionError) as e:return None,dict(stats,reason=str(e))


def normal_contrast(F,cols,target,offset,R,w,leaf_width=6,boundary_width=3,work_cap=16384):
    H,stats=normal_fold(F,cols,target,offset,R,leaf_width,boundary_width,work_cap)
    if H is None:return None
    v=tuple(w*(3*h-sum(H)) for h in H)
    return v,v,dict(stats,head=H)
