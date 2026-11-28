"""Original source Hall defects and pair-projection support contraction.
Reuse the Karp flow/min-cut donor; no arbitrary width or SAT claim.
"""
from itertools import combinations
from check_karp_flow_cut_apx import max_flow_min_cut
from check_pnp_source_derived_cover import Reservation,Refused
from check_pnp_frontier_resolution import accepts,norm
from check_pnp_normal_endpoint_weld import exact_cover
from check_p0_signed_contrast_20261125 import ContinuationAllowance


def flow(L,R,E,B):
    # Unit source/sink arcs, large middle arcs. At most len(L) unit
    # augmentations of the actual dense Edmonds-Karp donor.
    L=tuple(L);R=tuple(R);N=len(L)+len(R)+2
    B.pay((len(L)+2)*(N*N+len(E)+N+1))
    i={v:j+1 for j,v in enumerate(L)};j={v:k+1+len(L) for k,v in enumerate(R)}
    A=tuple((0,i[u],1) for u in L)+tuple((i[u],j[v],len(L)+1) for u,v in sorted(E) if u in i and v in j)+tuple((j[v],N-1,1) for v in R)
    f,S=max_flow_min_cut(N,A)
    if f==len(L):return None
    X=tuple(u for u in L if i[u] in S);Y=tuple(v for v in R if j[v] in S)
    assert set(Y)=={v for u,v in E if u in X and v in j}
    assert len(X)>len(Y)
    return X,Y


def matching(L,R,E,B):
    L=tuple(L);R=tuple(R);M=[]
    for u in tuple(L):
        for v in R:
            B.pay(1)
            if (u,v) not in E:continue
            l=tuple(a for a in L if a!=u);r=tuple(b for b in R if b!=v)
            if flow(l,r,E,B) is None:
                M.append((u,v));L,R=l,r;break
        else:raise AssertionError('full matching premise')
    return tuple(M)


def verify_hall(F,n,rows,cols,X,Y,B):
    B.pay(1+n+sum(1+len(c) for c in F)+sum(len(c)**2 for c in cols))
    D=set(map(norm,F));assert all(c in D and c and min(c)>0 for c in rows)
    flat=[v for c in rows for v in c];assert len(flat)==len(set(flat))
    assert sorted(v for c in cols for v in c)==list(range(1,n+1))
    assert all(norm((-a,-b)) in D for c in cols for a,b in combinations(c,2))
    assert len(set(X))==len(X) and len(set(Y))==len(Y) and len(X)>len(Y)
    assert all(0<=i<len(rows) for i in X) and all(0<=j<len(cols) for j in Y)
    assert set(v for i in X for v in rows[i])<=set(v for j in Y for v in cols[j])
    return True


def cnf_hall(F,n,cap):
    if n<0 or any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError('source')
    B=Reservation(cap)
    try:
        B.pay(1+n+sum(1+len(c) for c in F));D=tuple(map(norm,F));used=set();rows=[]
        if () in D:return dict(status='EMPTY',route='empty_clause',used=cap-B.left)
        for c in sorted(set(D),key=lambda c:(len(c),c)):
            B.pay(1+len(c))
            if min(c)>0 and not used.intersection(c):rows.append(c);used.update(c)
        E=[set() for _ in range(n+1)]
        for c in D:
            if len(c)==2 and max(c)<0:
                a,b=map(abs,c);E[a].add(b);E[b].add(a)
        U=set(range(1,n+1));cols=[]
        while U:
            a=min(U);todo=[a];U.remove(a);C=[]
            while todo:
                v=todo.pop();C.append(v);B.pay(1+len(E[v]));new=E[v]&U;U-=new;todo.extend(new)
            if all(len(E[v])==len(C)-1 for v in C):cols.append(tuple(sorted(C)))
            else:cols.extend((v,) for v in sorted(C)) # safe weaker capacity
        row=tuple(rows);col=tuple(cols);pos={v:j for j,c in enumerate(col) for v in c}
        edge={};B.pay(1+sum(map(len,row)))
        for i,c in enumerate(row):
            for v in c:edge.setdefault((i,pos[v]),v)
        L=tuple(range(len(row)));R=tuple(range(len(col)));A=set(edge)
        h=flow(L,R,A,B)
        if h is not None:
            X,Y=h;assert verify_hall(F,n,row,col,X,Y,B)
            return dict(status='EMPTY',route='hall',rows=row,cols=col,X=X,Y=Y,used=cap-B.left)
        chosen={edge[p] for p in matching(L,R,A,B)};x=tuple(int(i in chosen) for i in range(1,n+1))
        B.pay(1+n+sum(1+len(c) for c in F))
        return dict(status='WITNESS',witness=x,used=cap-B.left) if accepts(F,x) else dict(status='UNKNOWN',used=cap-B.left)
    except Refused:return dict(status='UNKNOWN',used=cap-B.left)


def projection(O,n,groups,cap):
    """Original tripartite incidence, no relaxation promoted to exact cover.
    Every column must have exactly one row in each given partition.
    Remove only columns absent from all perfect matches of a projection.
    """
    if n<0 or len(groups)!=3 or sorted(i for g in groups for i in g)!=list(range(len(O))) or any(len(set(c))!=len(c) or any(not 0<=v<n for v in c) for c in O):raise ValueError('incidence')
    B=Reservation(cap);removed=[]
    try:
        B.pay(1+n+sum(1+len(c) for c in O));G=tuple(tuple(g) for g in groups);labels=[]
        for g in G:
            d={}
            for r in g:
                for v in O[r]:
                    if v in d:raise ValueError('not tripartite')
                    d[v]=r
            if set(d)!=set(range(n)):raise ValueError('not tripartite')
            labels.append(d)
        if len(set(map(len,G)))!=1:return dict(status='EMPTY',route='unequal_partitions',used=cap-B.left)
        V=set(range(n))
        while True:
            drop=set()
            for i,j in combinations(range(3),2):
                L,R=G[i],G[j];B.pay(1+len(V));E={(labels[i][v],labels[j][v]) for v in V}
                h=flow(L,R,E,B)
                if h is not None:return dict(status='EMPTY',route='projection_hall',pair=(i,j),defect=h,removed=tuple(removed),used=cap-B.left)
                bad=set()
                for a,b in sorted(E):
                    h=flow(tuple(u for u in L if u!=a),tuple(v for v in R if v!=b),E,B)
                    if h is not None:
                        B.pay(1+len(V));bad.add((a,b));removed.append((i,j,a,b,h,tuple(sorted(V))))
                B.pay(1+len(V));drop.update(v for v in V if (labels[i][v],labels[j][v]) in bad)
            if not drop:break
            V-=drop
        active=tuple(sorted(V));idx={v:j for j,v in enumerate(active)}
        C=tuple(tuple(idx[v] for v in c if v in V) for c in O)
        q=exact_cover(C,len(active),ContinuationAllowance(B.left),B.left)
        if q['status']=='WITNESS':
            chosen={v for v,b in zip(active,q['witness']) if b};x=tuple(int(v in chosen) for v in range(n))
            assert all(sum(x[v] for v in c)==1 for c in O);q=dict(q,witness=x)
        return dict(q,active=active,removed=tuple(removed),projection_used=cap-B.left,reserved=cap)
    except Refused:return dict(status='UNKNOWN',removed=tuple(removed),projection_used=cap-B.left)


def replay_projection(O,n,groups,receipts):
    # Independently check each forced-edge Hall defect on its original
    # active carrier. Earlier deletions remain sound in subsequent rounds.
    labels=tuple({v:r for r in g for v in O[r]} for g in groups)
    V=set(range(n));snapshot=None;drop=set()
    for i,j,a,b,(X,Y),source in receipts:
        if source!=snapshot:
            V-=drop;drop=set();snapshot=source
            assert V==set(source)
        L,R=set(groups[i])-{a},set(groups[j])-{b}
        assert set(X)<=L and set(Y)<=R and len(set(X))>len(set(Y))
        assert all(labels[j][v] in Y for v in V if labels[i][v] in X and labels[j][v] in R)
        drop.update(v for v in V if labels[i][v]==a and labels[j][v]==b)
    return V-drop


def main():
    from itertools import product,permutations
    from random import Random
    from collections import Counter
    C=Counter();L=R=tuple(range(3));pairs=tuple(product(L,R))
    for b in product((0,1),repeat=9):
        E={e for e,z in zip(pairs,b) if z};B=Reservation(10**7);h=flow(L,R,E,B)
        W=[p for p in permutations(R) if all((i,p[i]) in E for i in L)]
        assert (h is None)==bool(W)
        if h is None:assert tuple(v for u,v in matching(L,R,E,B)) in W
        # Verify every forced-edge perfect matching test independently.
        for a,v in E:
            q=flow(tuple(i for i in L if i!=a),tuple(j for j in R if j!=v),E,B)
            assert (q is None)==any(p[a]==v for p in W);C['edge_tests']+=1
        C['graphs']+=1
    rng=Random(3693201)
    for k in (2,3,4):
        for _ in range(32):
            triples=tuple(rng.sample(list(product(range(k),repeat=3)),min(k**3,3*k)))
            n=len(triples);O=tuple(tuple(j for j,t in enumerate(triples) if t[i]==a) for i in range(3) for a in range(k));G=tuple(tuple(range(i*k,(i+1)*k)) for i in range(3))
            W=[x for x in product((0,1),repeat=n) if all(sum(x[j] for j in c)==1 for c in O)]
            q=projection(O,n,G,10**7)
            assert q['status']==('WITNESS' if W else 'EMPTY')
            V=replay_projection(O,n,G,q['removed'])
            if W:assert q['witness'] in W and V==set(q['active']) and all(not x[v] for x in W for v in range(n) if v not in V)
            C['tripartite',q['status']]+=1;C['removed_receipts']+=len(q['removed'])
    for k in (4,8,16,32):
        # Equal total row and column count, but a strict subset Hall defect.
        E=tuple((i,j) for i in range(k) for j in range(k) if (i<k//2+1 and j<k//2) or (i>=k//2+1 and j>=k//2));n=len(E)
        row=tuple(tuple(t+1 for t,(i,j) in enumerate(E) if i==a) for a in range(k));col=tuple(tuple(t+1 for t,(i,j) in enumerate(E) if j==a) for a in range(k))
        F=row+tuple((-a,-b) for c in col for a,b in combinations(c,2));q=cnf_hall(F,n,10**7)
        assert q['status']=='EMPTY' and q['route']=='hall' and len(q['X'])==len(q['Y'])+1
        C['balanced_defect']+=1;print('balanced defect',k,n,len(q['X']),len(q['Y']),q['used'])
    # A perfect matching of the relaxation is not necessarily a CNF witness.
    F=((1,2),(-1,-2),(-1,),(-2,));q=cnf_hall(F,2,100000);assert q['status']=='UNKNOWN'
    assert cnf_hall(((1,),),1,0)['status']=='UNKNOWN'
    print(dict(C),'negative controls PASS')
if __name__=='__main__':main()
