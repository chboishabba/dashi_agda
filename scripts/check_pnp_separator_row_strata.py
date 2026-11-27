"""Exact separator-conditioned row strata; bounded, source-keyed, original reopening.
Uses the existing normal-boundary tree, not an independent separator search.
Paper 9 equality permutation is a conceptual donor for unique keys / reverse folds.
"""
from check_pnp_affine_normal_components import bits, canon, chart, lift, satisfies
from check_pnp_normal_boundary_join import span, value, rows, representative, tree


def build(n,R,P,B,leaf_cap=8,seam_cap=8):
    """None = width refusal, not exclusion. Geometry is independent of incumbent t."""
    assert R and P==canon(P) and canon(P+tuple((r,1) for r in R))==P
    assert leaf_cap>=0 and seam_cap>=0
    B.pay('seam_chart',1+n*(1+len(P)))
    u,V=chart(n,P);d=len(V);m=len(R)
    F=tuple(tuple((value(V,1<<j),u>>j&1) for j in bits(r)) for r in R)
    B.pay('seam_normals',1+d*sum(map(len,F)))
    root,boundary,space=tree(d,F,B)
    assert len(space(root[0]))==d # every original column occurs
    nodes=[];width=[0,0]
    def prepare(node):
        mask,A,C=node;D=boundary(mask);width[1]=max(width[1],len(D))
        if len(D)>seam_cap:return None
        if A is None:
            e=mask.bit_length()-1;U=space(mask);width[0]=max(width[0],len(U))
            if len(U)>leaf_cap:return None
            B.pay('seam_leaf_labels',(1<<len(U))*(1+d*(1+len(U)+len(D))+len(F[e])))
            T=[]
            for p in range(1<<len(U)):
                z=representative(d,U,p);w=sum(b^((a&z).bit_count()%2) for a,b in F[e])
                T.append((value(D,z),w,rows(U,p)))
            nodes.append((e,T));return len(nodes)-1
        a=prepare(A);c=prepare(C)
        if a is None or c is None:return None
        L=boundary(A[0]);Q=boundary(C[0]);U=span(L+Q)
        assert span(U+D)==U
        # Enumerate the joint normal space once, not a Cartesian pairing.
        # Every compatible child key pair has exactly one U-label.
        B.pay('seam_pair_build',(1<<len(U))*(1+d*(1+len(U)+len(L)+len(Q)+len(D))))
        T=[]
        for p in range(1<<len(U)):
            z=representative(d,U,p);T.append((value(L,z),value(Q,z),value(D,z)))
        nodes.append((a,c,T));return len(nodes)-1
    top=prepare(root)
    if top is None:return None
    return n,tuple(R),P,u,tuple(V),tuple(nodes),top,tuple(width)


def observe(n,R,P,x,G,B):
    """Return status, movement, exact root masses, cover mass, admissible mass.
    Counts are on unique original points, not proof or auxiliary representations.
    """
    n0,R0,P0,u,V,nodes,top,width=G
    assert (n,tuple(R),P)==(n0,R0,P0) and satisfies(x,P,())
    m=len(R);zero=(0,)*m;tables=[]
    # Entries: admissible mass, cover mass, per-root masses, any/cover/strict receipt.
    def put(T,k,v):
        if k not in T:T[k]=v;return
        a,c,r,h,g,s=T[k];b,d,q,i,j,t=v
        T[k]=(a+b,c+d,tuple(l+z for l,z in zip(r,q)),h,g if g is not None else j,s if s is not None else t)
    for node in nodes:
        T={}
        if len(node)==2:
            e,L=node;w=(R[e]&x).bit_count()
            for k,r,h in L:
                B.pay('seam_leaf_fold',1+m)
                if r>w:continue
                strict=r<w;cover=r==1
                q=tuple(int(strict and i==e) for i in range(m))
                put(T,k,(1,int(cover),q,h,h if cover else None,h if strict else None))
        else:
            l,r,L=node;A=tables[l];C=tables[r]
            for i,j,k in L:
                B.pay('seam_pair_probe')
                if i not in A or j not in C:continue
                a,c,p,h,g,s=A[i];b,d,q,v,w,t=C[j]
                B.pay('seam_pair_fold',1+m+len(h)+len(v))
                roots=tuple(f*b+a*z for f,z in zip(p,q))
                strict=s+v if s is not None else (h+t if t is not None else None)
                cover=g+w if g is not None and w is not None else None
                put(T,k,(a*b,c*d,roots,h+v,cover,strict))
        tables.append(T)
    assert 0 in tables[top] # the incumbent itself is always admissible
    a,c,p,h,g,s=tables[top][0]
    if s is None:return ('COVER' if c else 'EMPTY'),None,p,c,a
    H=canon(g if g is not None else s);assert H is not None
    B.pay('seam_reopen',1+n*(1+len(P))+len(V)*(1+len(H))+sum(r.bit_count() for r in R))
    z=chart(len(V),H)[0];y=lift(u,V,z);v=x^y
    q=tuple((r&x).bit_count()-(r&y).bit_count() for r in R)
    assert satisfies(y,P,()) and all(t>=0 and t%2==0 for t in q) and any(q)
    if g is not None:assert all((r&y).bit_count()==1 for r in R)
    return 'SAT',v,p,c,a


def descent(n,R,P,x,B,leaf_cap=8,seam_cap=8,history=None,k_index=0):
    G=build(n,R,P,B,leaf_cap,seam_cap)
    if G is None:return None
    status,v,p,c,a=observe(n,R,P,x,G,B)
    if not c:return None,True
    if status=='COVER':return x,True
    assert v is not None;y=x^v
    assert all((r&y).bit_count()==1 for r in R)
    if history is not None:history.append((k_index,0,x,v,tuple((r&x).bit_count()-(r&y).bit_count() for r in R),B.left))
    return y,True
