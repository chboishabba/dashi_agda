"""Count actual GF2 normal restrictions, not representatives or ambient points.
Reuse existing normal spaces/tree; logical caps, no uniform rank claim.
"""
from collections import defaultdict
from check_pnp_affine_normal_components import canon,chart,lift,Budget,Exhausted
from check_pnp_normal_boundary_join import tree,intersection,value,rows,span


def count(n,H,F,O,cap,clip=None,max_width=16):
    # F: forbidden affine flats; O: exact-one bits (normal, offset).
    if n<0 or clip not in (None,2) or max_width<0 or any(not 0<=a<1<<n or b not in (0,1) for G in (H,)+F+O for a,b in G):raise ValueError('source')
    B=Budget(cap);width=0
    def trim(v):return v if clip is None else min(2,v)
    def result(status,**kw):return dict(status=status,width=width,used=min(cap,cap-B.left),**kw)
    try:
        B.pay('chart',1+(n+1)*(1+len(H)+sum(map(len,F+O))))
        R=canon(H)
        if R is None:return result('EMPTY',count=0)
        u,V=chart(n,R);d=len(V)
        def pull(G):return tuple((value(V,a),b^((a&u).bit_count()%2)) for a,b in G)
        flats=tuple(G for f in F if (G:=canon(pull(f))) is not None);ones=tuple(map(pull,O));G=flats+ones
        if not G:return result('WITNESS',count=trim(1<<d),witness=u)
        root,boundary,space=tree(d,G,B);tables=0
        def run(node):
            nonlocal width,tables
            m,L,R=node;D=boundary(m);U=space(m);width=max(width,len(D))
            if width>max_width:raise Exhausted()
            T={}
            def put(p,c,h):
                if c:T[p]=(trim(T.get(p,(0,None))[0]+c),h)
            if L is None:
                i=m.bit_length()-1;g=G[i]
                if i<len(flats):
                    # A forbidden flat defines exactly one restriction on U.
                    bad=chart(d,g)[0];badkey=value(D,bad)
                    B.pay('leaf_boundary',1<<len(D))
                    for p in range(1<<len(D)):
                        B.pay('leaf_chart',1+d*(1+len(U)+len(D)))
                        mass=(1<<(len(U)-len(D)))-int(p==badkey)
                        if not mass:continue
                        a,W=chart(d,canon(rows(D,p)))
                        if value(U,a)==value(U,bad):a^=next(w for w in W if value(U,w))
                        put(p,mass,rows(U,value(U,a)))
                else:
                    # Distinct one-hot bit patterns are disjoint U restrictions.
                    for j in range(len(g)):
                        B.pay('onehot',1+d*(1+len(g)))
                        K=canon((a,b^int(k==j)) for k,(a,b) in enumerate(g))
                        if K is not None:
                            x=chart(d,K)[0];put(value(D,x),1,rows(U,value(U,x)))
            else:
                A=run(L);C=run(R);I=intersection(d,space(L[0]),space(R[0]));E=defaultdict(list)
                for c,h in C.values():
                    B.pay('index',1+d*(1+len(h)));x=chart(d,h)[0];E[value(I,x)].append((c,h))
                for a,h in A.values():
                    B.pay('index',1+d*(1+len(h)));x=chart(d,h)[0]
                    for c,k in E[value(I,x)]:
                        B.pay('match',1+d*(1+len(h)+len(k)));K=canon(h+k);assert K is not None
                        y=chart(d,K)[0];put(value(D,y),trim(a*c),K)
            B.pay('retained',len(T));tables+=len(T);return T
        T=run(root)
        if not T:return result('EMPTY',count=0,entries=tables)
        mass,h=T[0];x=lift(u,V,chart(d,h)[0]);rank=len(space(root[0]));mass=trim(mass*(1<<(d-rank)))
        assert all((a&x).bit_count()%2==b for a,b in H) and all(any((a&x).bit_count()%2!=b for a,b in f) for f in F) and all(sum(((a&x).bit_count()%2)^b for a,b in g)==1 for g in O)
        return result('WITNESS',count=mass,witness=x,entries=tables,rank=rank,free=d)
    except Exhausted:return result('UNKNOWN')


def main():
    from random import Random
    rng=Random(3693601);C=defaultdict(int)
    for n in range(9):
        for _ in range(32):
            def row(k):return tuple((rng.randrange(1<<n),rng.randrange(2)) for j in range(k))
            H=row(rng.randrange(3));F=tuple(row(rng.randrange(5)) for j in range(rng.randrange(5)));O=tuple(row(rng.randrange(5)) for j in range(rng.randrange(3)))
            W=[x for x in range(1<<n) if all((a&x).bit_count()%2==b for a,b in H) and all(any((a&x).bit_count()%2!=b for a,b in f) for f in F) and all(sum(((a&x).bit_count()%2)^b for a,b in g)==1 for g in O)]
            for clip in (None,2):
                q=count(n,H,F,O,10**7,clip);assert q['count']==(len(W) if clip is None else min(2,len(W)))
                if W:assert q['witness'] in W
                C[q['status']]+=1
    for n in (16,32,64,128):
        G=tuple((1<<i,0) for i in range(n));q=count(n,(),(G,),(),10**7,max_width=0);assert q['count']==(1<<n)-1
        z=count(n,(),(),(G,),10**7,max_width=0);assert z['count']==n
        # Two full-rank wide clauses sharing one normal, not coordinates.
        a=(1<<n)-1;F=(((a,0),)+tuple((1<<i,0) for i in range(n//2-1)),((a,1),)+tuple((1<<i,0) for i in range(n//2,n-1)))
        q=count(n,(),F,(),10**7,max_width=1);assert q['count']==(1<<n)-2*(1<<(n-n//2)) and q['width']==1
        print('wide',n,q['width'],q['entries'],q['used'])
    assert count(3,(),(((1,0),),((1,1),)),(),10000,max_width=0)['status']=='UNKNOWN'
    assert count(1,(),(),(),0)['status']=='UNKNOWN'
    print(dict(C),'refusals PASS')
if __name__=='__main__':main()
