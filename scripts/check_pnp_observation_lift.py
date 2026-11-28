"""Exact bounded CNF truth-table lift into Boolean monomial observations.
No named gadget templates. Linear inconsistency is sound even with overlap;
consistent abstract observations require original witness reopening.
"""
from itertools import product
from check_pnp_source_derived_cover import Reservation, Refused
from check_pnp_affine_normal_components import canon, chart


def groups(F,n,B,width):
    G={}
    B.pay(1+n+sum(1+len(c) for c in F))
    for c in F:
        c=set(c)
        if any(not 1<=abs(l)<=n for l in c):raise ValueError('literal')
        if any(-l in c for l in c):continue
        S=tuple(sorted(abs(l)-1 for l in c))
        if len(S)>width:continue
        G.setdefault(S,set()).add(sum((-(j+1) in c)<<i for i,j in enumerate(S)))
    return G


def polynomial(S,bad,B):
    k=len(S);B.pay((k+2)*(1<<k));a=[int(i in bad) for i in range(1<<k)]
    for j in range(k):
        for i in range(1<<k):
            if i>>j&1:a[i]^=a[i^(1<<j)]
    terms=tuple(tuple(S[j] for j in range(k) if i>>j&1) for i in range(1,1<<k) if a[i])
    return a[0],terms


def conflict(rows,B):
    basis={}
    for i,(a,b) in enumerate(rows):
        w=1<<i
        while a and a.bit_length()-1 in basis:
            B.pay(1);u,v,h=basis[a.bit_length()-1];a^=u;b^=v;w^=h
        if a:basis[a.bit_length()-1]=(a,b,w)
        elif b:return tuple(j for j in range(len(rows)) if w>>j&1)
    return None


def replay(F,n,certificate,B,width=9):
    # Independent truth-table evaluation (not the Mobius transform).
    G=groups(F,n,B,width);terms=set();constant=0;scopes=sorted(G)
    ids=tuple(certificate['indices']);P=certificate['polynomials']
    if not ids or len(set(ids))!=len(ids) or any(not 0<=i<len(scopes) for i in ids) or len(P)!=len(ids):return False
    for i,(c,T) in zip(ids,P):
        S=scopes[i];bad=G[S];B.pay(1+(1<<len(S))*(1+sum(map(len,T))))
        if c not in (0,1) or len(set(T))!=len(T) or any(not t or tuple(sorted(set(t)))!=t or not set(t)<=set(S) for t in T):return False
        for a in range(1<<len(S)):
            u={j:a>>k&1 for k,j in enumerate(S)}
            if (c+sum(all(u[j] for j in t) for t in T))%2!=int(a in bad):return False
        constant^=c;terms.symmetric_difference_update(T)
    return constant==1 and not terms


def audit(F,x):return all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)


def solve(F,n,cap=10000000,width=9):
    if n<0 or not 0<=width<=12:raise ValueError('limits')
    B=Reservation(cap);meta={}
    def out(status,**kw):return dict(status=status,used=cap-B.left,**meta,**kw)
    try:
        G=groups(F,n,B,width);P=tuple(polynomial(S,bad,B) for S,bad in sorted(G.items()))
        # Each polynomial must vanish on every satisfying original assignment.
        M=sorted({t for _,T in P for t in T});idx={t:i for i,t in enumerate(M)};meta.update(groups=len(G),monomials=len(M))
        B.pay(1+len(P)*(len(M)+1)**2);rows=tuple((sum(1<<idx[t] for t in T),c) for c,T in P)
        h=conflict(rows,B)
        if h is not None:
            cert=dict(indices=h,polynomials=tuple(P[i] for i in h))
            if not replay(F,n,cert,B,width):raise AssertionError('invalid contradiction')
            return out('EMPTY',route='monomial_conflict',certificate=cert)
        # Discover the disjoint additive components of each local polynomial.
        obs=set();Q=[]
        for c,T in P:
            B.pay(1+sum(len(t)**2 for t in T));parent={i:i for t in T for i in t}
            def root(i):
                while parent[i]!=i:i=parent[i]
                return i
            for t in T:
                for j in t[1:]:parent[root(j)]=root(t[0])
            D={}
            for t in T:D.setdefault(root(t[0]),[]).append(t)
            row=tuple(tuple(sorted(v)) for v in D.values());obs.update(row);Q.append((c,row))
        O=sorted(obs);ind={o:i for i,o in enumerate(O)};meta['observations']=len(O)
        B.pay(1+len(Q)*(len(O)+1)**2);R=canon((sum(1<<ind[o] for o in row),c) for c,row in Q)
        if R is None:raise AssertionError('component contradiction absent from monomial system')
        z,_=chart(len(O),R);x=[0]*n;seen=set()
        for i,o in enumerate(O):
            S=tuple(sorted({j for t in o for j in t}));B.pay(1+len(S))
            if seen.intersection(S):return out('UNKNOWN',reason='overlapping_components')
            seen.update(S);target=z>>i&1
            for bits in product((0,1),repeat=len(S)):
                B.pay(1+sum(map(len,o)));u=dict(zip(S,bits))
                if sum(all(u[j] for j in t) for t in o)%2==target:
                    for j,b in u.items():x[j]=b
                    break
            else:return out('UNKNOWN',reason='reopen')
        B.pay(1+n+sum(1+len(c) for c in F))
        if audit(F,x):return out('WITNESS',witness=tuple(x),route='component_reopen')
        return out('UNKNOWN',reason='original_audit')
    except Refused:return out('UNKNOWN',reason='cap')


def substituted(v,E,tables,k,odd):
    F=[]
    for i in range(v):
        edges=tuple(j for j,e in enumerate(E) if i in e);S=tuple(k*j+r for j in edges for r in range(k))
        for a in range(1<<len(S)):
            if sum(tables[j][a>>(k*p)&((1<<k)-1)] for p,j in enumerate(edges))%2!=int(odd and i==0):
                F.append(tuple((r+1)*(1-2*(a>>p&1)) for p,r in enumerate(S)))
    return tuple(F)


def main():
    from random import Random
    from check_pnp_compilation_calibration import graph
    rng=Random(3693801);checks=0
    for n in range(1,8):
        for _ in range(48):
            F=tuple(tuple(rng.choice((-1,1))*(j+1) for j in rng.sample(range(n),rng.randrange(n+1))) for i in range(rng.randrange(15)))
            W=[x for x in product((0,1),repeat=n) if audit(F,x)];q=solve(F,n)
            if q['status']=='EMPTY':assert not W
            if q['status']=='WITNESS':assert q['witness'] in W
            checks+=1
    print('small independent',checks)
    for v in (6,8,12,16):
        E=graph(v,3693700+v)
        for k,kind in ((2,'and'),(3,'majority'),(3,'random')):
            if kind=='and':T=((0,0,0,1),)*len(E)
            elif kind=='majority':T=(tuple(int(a.bit_count()>=2) for a in range(8)),)*len(E)
            else:
                L=[]
                for e in E:
                    a=rng.randrange(1,255);L.append(tuple(a>>i&1 for i in range(8)))
                T=tuple(L)
            for odd in (False,True):
                F=substituted(v,E,T,k,odd);q=solve(F,k*len(E),cap=100000000)
                assert q['status']==('EMPTY' if odd else 'WITNESS')
                print(v,k,kind,odd,len(F),q['status'],q['used'],q['monomials'],flush=True)
    # Overlap without a real lift, unsupported large clause, removed source clause.
    F=((1,2),(-1,2),(1,-2));q=solve(F,2);assert q['status']!='EMPTY'
    q=solve(((1,),(-1,)),1);assert q['status']=='EMPTY';bad=dict(q['certificate'],polynomials=((0,()),));assert not replay(((1,),(-1,)),1,bad,Reservation(1000))
    assert not replay(((1,),),1,q['certificate'],Reservation(1000))
    assert solve(((-1,),(1,2),(1,-2),(-1,2)),2)['status']=='UNKNOWN'
    assert solve(((1,),),1,cap=0)['status']=='UNKNOWN'
    assert solve(((1,2,3),),3,width=1)['status']=='UNKNOWN'
if __name__=='__main__':main()
