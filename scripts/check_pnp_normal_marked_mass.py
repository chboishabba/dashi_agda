#!/usr/bin/env python3
"""One-tree signed marginal extension of the existing normal-mass ABI.
H: required GF2 rows; F: forbidden flats; O: exact-one affine bits (a,offset).
Marks are original parity normals. Counts and witnessed channels are exact
only on completed contraction; UNKNOWN carries no count. Abstract work cap.
"""
from collections import defaultdict
from check_pnp_affine_normal_components import canon, chart, lift, Budget, Exhausted
from check_pnp_normal_boundary_join import tree, intersection, value, rows, span


def marked_count(n, H, F, O, marks, cap, clip=None, max_width=16):
    H, F, O, marks = tuple(H), tuple(F), tuple(O), tuple(marks)
    if (n < 0 or cap < 0 or clip not in (None, 2) or max_width < 0
        or any(not 0 <= a < 1 << n or b not in (0, 1) for G in (H,)+F+O for a,b in G)
        or any(not 0 <= a < 1 << n for a in marks)):
        raise ValueError('source')
    B = Budget(cap)
    width = 0
    stats = dict(nodes=0, entries=0, peak=0, matches=0, convolutions=0, leaf_channels=0)
    def trim(v): return v if clip is None else min(2, v)
    def plus(a,b):
        B.pay('count_bits',1+max(a.bit_length(),b.bit_length()))
        return trim(a+b)
    def times(a,b):
        B.pay('count_bits',1+a.bit_length()*b.bit_length())
        return trim(a*b)
    def pow2(k):
        assert k >= 0
        B.pay('count_bits',k+1)
        return trim(1<<k)
    def empty(): return (0,None)
    def result(status, **kw):
        return dict(status=status,width=width,used=min(cap,cap-B.left),**stats,**kw)
    def completed_empty():
        return result('EMPTY',count=0,witness=None,marginals=[(empty(),empty()) for _ in marks])
    try:
        B.pay('chart',1+(n+1)*(1+len(H)+sum(map(len,F+O))+len(marks)))
        R=canon(H)
        if R is None: return completed_empty()
        u,V=chart(n,R); d=len(V)
        def pull(G): return tuple((value(V,a),b^((a&u).bit_count()%2)) for a,b in G)
        flats=tuple(G for f in F if (G:=canon(pull(f))) is not None)
        ones=tuple(map(pull,O)); G=flats+ones
        marks_local=tuple((value(V,a),(a&u).bit_count()%2) for a in marks)
        def split(a,L,R):
            E=L+R
            B.pay('normal_split',1+(d+1)*(len(E)+1)**2)
            K=canon((value(E,1<<j),(a>>j)&1) for j in range(d))
            if K is None: return None
            c=chart(len(E),K)[0]
            l=lift(0,L,c&((1<<len(L))-1)); r=lift(0,R,c>>len(L))
            assert l^r==a
            return l,r
        def verified(x):
            return (all((a&x).bit_count()%2==b for a,b in H)
                and all(any((a&x).bit_count()%2!=b for a,b in f) for f in F)
                and all(sum(((a&x).bit_count()%2)^b for a,b in g)==1 for g in O))
        def at(a,x): return (a&x).bit_count()%2
        def original(z): return None if z is None else lift(u,V,z)
        if not G:
            mass=pow2(d); x=u; marg=[]
            for a,b in marks_local:
                if not a:
                    c=[empty(),empty()]; c[b]=(mass,x)
                else:
                    y=original(a&-a); half=pow2(d-1); c=[empty(),empty()]
                    c[b]=(half,x); c[b^1]=(half,y)
                marg.append(tuple(c))
            return result('WITNESS',count=mass,witness=x,marginals=marg)
        root,boundary,space=tree(d,G,B); U0=space(root[0])
        inside=[]; outside=[]
        for j,(a,b) in enumerate(marks_local):
            (inside if split(a,U0,()) is not None else outside).append(j)
        def run(node,Q):
            nonlocal width
            m,L,R=node; D=boundary(m); U=space(m); width=max(width,len(D))
            if width>max_width: raise Exhausted()
            stats['nodes']+=1; T={}
            def put(p,j,b,c,x):
                if not c: return
                B.pay('marked_store',1+len(Q))
                if p not in T: T[p]=[empty(),[[empty(),empty()] for _ in Q]]
                e=T[p]
                if j<0:
                    v,y=e[0]; e[0]=(plus(v,c),x if y is None else y)
                else:
                    v,y=e[1][j][b]; e[1][j][b]=(plus(v,c),x if y is None else y)
            if L is None:
                i=m.bit_length()-1; g=G[i]
                if i<len(flats):
                    bad=chart(d,g)[0]
                    def channel(pins):
                        B.pay('marked_leaf',1+(d+1)*(len(pins)+len(U)+1)**2)
                        K=canon(pins)
                        if K is None: return empty()
                        x,W=chart(d,K); k=len(U)-len(K); assert k>=0
                        # Subtract the excluded point BEFORE clipping.
                        B.pay('count_bits',k+1)
                        c=(1<<k)-int(all(at(a,bad)==b for a,b in pins))
                        if not c: return empty()
                        if value(U,x)==value(U,bad): x^=next(w for w in W if value(U,w))
                        return trim(c),x
                    B.pay('leaf_boundary',1<<len(D))
                    for p in range(1<<len(D)):
                        pins=rows(D,p); c,x=channel(pins); put(p,-1,0,c,x)
                        if c:
                            for j,a in enumerate(Q):
                                for b in (0,1):
                                    c,x=channel(pins+((a,b),)); put(p,j,b,c,x)
                                    stats['leaf_channels']+=1
                else:
                    for j in range(len(g)):
                        B.pay('onehot',1+(d+1)*(1+len(g))**2)
                        K=canon((a,b^int(k==j)) for k,(a,b) in enumerate(g))
                        if K is None: continue
                        x=chart(d,K)[0]; p=value(D,x); put(p,-1,0,1,x)
                        for i,a in enumerate(Q):
                            put(p,i,at(a,x),1,x); stats['leaf_channels']+=1
            else:
                A,C=space(L[0]),space(R[0]); I=intersection(d,A,C)
                Z=[split(a,A,C) for a in Q]; assert all(z is not None for z in Z)
                LT=run(L,tuple(z[0] for z in Z)); RT=run(R,tuple(z[1] for z in Z))
                E=defaultdict(list)
                def glue(x,y):
                    B.pay('marked_glue',1+(d+1)*(1+len(A)+len(C))**2)
                    K=canon(rows(A,value(A,x))+rows(C,value(C,y))); assert K is not None
                    return chart(d,K)[0]
                for e in RT.values():
                    B.pay('index',1+d*(1+len(I))); E[value(I,e[0][1])].append(e)
                for le in LT.values():
                    c,x=le[0]; B.pay('index',1+d*(1+len(I)))
                    for re in E[value(I,x)]:
                        h,y=re[0]; z=glue(x,y); p=value(D,z)
                        put(p,-1,0,times(c,h),z); stats['matches']+=1
                        for j,a in enumerate(Q):
                            for b in (0,1):
                                for e in (0,1):
                                    B.pay('marked_convolution'); stats['convolutions']+=1
                                    c1,x1=le[1][j][b]; c2,x2=re[1][j][e]
                                    if c1 and c2:
                                        z1=glue(x1,x2); assert value(D,z1)==p and at(a,z1)==b^e
                                        put(p,j,b^e,times(c1,c2),z1)
            stats['entries']+=len(T); stats['peak']=max(stats['peak'],len(T))
            return T
        T=run(root,tuple(marks_local[j][0] for j in inside))
        if not T: return completed_empty()
        base, channels=T[0]; c,z=base; free=d-len(U0); mass=times(c,pow2(free)); x=original(z)
        marg=[None]*len(marks)
        for i,j in enumerate(inside):
            b=marks_local[j][1]
            marg[j]=tuple((times(channels[i][k^b][0],pow2(free)),original(channels[i][k^b][1])) for k in (0,1))
        for j in outside:
            a,b=marks_local[j]; W=chart(d,canon(rows(U0,0)))[1]
            v=next(w for w in W if at(a,w)); k=at(a,z)^b; half=times(c,pow2(free-1))
            q=[empty(),empty()]; q[k]=(half,x); q[k^1]=(half,original(z^v)); marg[j]=tuple(q)
        assert verified(x)
        for a,q in zip(marks,marg):
            assert plus(q[0][0],q[1][0])==mass
            for b,(h,y) in enumerate(q):
                assert (h==0)==(y is None)
                if h: assert verified(y) and at(a,y)==b
        return result('WITNESS',count=mass,witness=x,marginals=marg)
    except (Exhausted,RecursionError):
        return result('UNKNOWN')


def main():
    from random import Random
    rng=Random(5001); cases=channels=0
    for n in range(8):
        for _ in range(24):
            def row(k): return tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(k))
            H=row(rng.randrange(3)); F=tuple(row(rng.randrange(5)) for _ in range(rng.randrange(5))); O=tuple(row(rng.randrange(5)) for _ in range(rng.randrange(4)))
            marks=tuple(1<<i for i in range(n))+(0, rng.randrange(1<<n))
            W=[x for x in range(1<<n) if all((a&x).bit_count()%2==b for a,b in H) and all(any((a&x).bit_count()%2!=b for a,b in f) for f in F) and all(sum(((a&x).bit_count()%2)^b for a,b in g)==1 for g in O)]
            for clip in (None,2):
                q=marked_count(n,H,F,O,marks,10**7,clip)
                trim=lambda x: x if clip is None else min(2,x)
                assert q['status']!='UNKNOWN' and q['count']==trim(len(W)),q
                for a,cs in zip(marks,q['marginals']):
                    for b,(c,y) in enumerate(cs):
                        assert c==trim(sum((a&x).bit_count()%2==b for x in W))
                        if c: assert y in W and (a&y).bit_count()%2==b
                        channels+=1
                cases+=1
    S=[(2,10,15),(7,9,12),(3,4,14),(0,6,16),(1,5,13),(8,11,17),(9,15,16),(0,8,14),(2,6,17),(5,10,13),(1,3,12),(4,7,11),(3,11,12),(1,2,6),(0,7,14),(4,9,15),(10,13,17),(5,8,16),(0,1,14),(4,9,16),(7,12,15),(2,5,17),(3,6,11),(8,10,13),(0,1,9),(4,11,17),(3,6,16),(2,10,12),(5,14,15),(7,8,13)]
    R=tuple(sum(1<<j for j,s in enumerate(S) if i in s) for i in range(18)); H=tuple((r,1) for r in R); O=tuple(tuple((1<<j,0) for j in range(30) if r>>j&1) for r in R)
    q=marked_count(30,H,(),O,tuple(1<<j for j in range(30)),200000000)
    W=(63,100663443,4032,201375792,258048,16515072,1056964608)
    assert q['count']==7 and all(c==sum((x>>j&1)==b for x in W) for j,cs in enumerate(q['marginals']) for b,(c,y) in enumerate(cs))
    assert all(y in W for cs in q['marginals'] for c,y in cs if c)
    big=marked_count(128,(),(tuple((1<<i,0) for i in range(128)),),(),(1,1<<127),30000000)
    assert big['count']==(1<<128)-1 and big['marginals'][0][0][0]==(1<<127)-1
    for cap,width in ((0,16),(100000,0)):
        z=marked_count(3,(),(((1,0),(2,1)),((1,1),(4,0))),(),(1,),cap,max_width=width)
        assert z['status']=='UNKNOWN' and 'count' not in z
    print(dict(status='PASS',cases=cases,channels=channels,original={k:v for k,v in q.items() if k!='marginals'},high_rank=big['count']))


if __name__=='__main__': main()
