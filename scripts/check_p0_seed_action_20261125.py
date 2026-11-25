from itertools import product
from fractions import Fraction as Q
from random import Random
from collections import Counter
from check_p0_signed_contrast_20261125 import canon, restrict, add, basis, member, matrix, accepts, translation
from check_p0_endpoint_frontier_20261125 import shared, adversary, decode_singleton

def binary_bad(F):
    if () in F:return True
    adj={}
    for c in F:
        if len(c)==2:
            a,b=c;adj.setdefault(-a,set()).add(b);adj.setdefault(-b,set()).add(a)
    def reaches(a,b):
        seen={a};stack=[a]
        while stack:
            for v in adj.get(stack.pop(),()):
                if v==b:return True
                if v not in seen:seen.add(v);stack.append(v)
        return False
    return any(reaches(a,-a) and reaches(-a,a) for a in adj if a>0)

def units(F,n,pins):
    F=canon(F);P=dict(pins)
    for i,b in P.items():F=restrict(F,i,b)
    while True:
        if () in F:return None
        u=next((c[0] for c in F if len(c)==1),None)
        if u is None:break
        i=abs(u)-1;b=int(u>0)
        if i in P and P[i]!=b:return None
        P[i]=b;F=restrict(F,i,b)
    if binary_bad(F):return None
    return F,P

def infer(F,n):
    P={}
    while True:
        v=units(F,n,P)
        if v is None:return None
        R,P=v
        changed=False
        for i in range(n):
            if i in P:continue
            possible=[b for b in (0,1) if units(R,n,{i:b}) is not None]
            if not possible:return None
            if len(possible)==1:P[i]=possible[0];changed=True;break
        if not changed:return P

def hashval(n,k,s,x):
    A=matrix(n,k,s[:n+k-1]);b=s[n+k-1:]
    return tuple((sum(a*z for a,z in zip(row,x))+v)%3 for row,v in zip(A,b))

def scale(v,b):return tuple(b*x%3 for x in v)

def quotient(n,k,p,P):
    L=n+2*k-1;w=L-len(p);base=tuple(p)+(0,)*w
    x0=tuple(P.get(i,0) for i in range(n));free=[i for i in range(n) if i not in P]
    points=[x0]+[tuple(int(j==i)+x for j,x in enumerate(x0)) for i in free]
    def action(s):return tuple(v for x in points for v in hashval(n,k,s,x))
    h=action(base);cols=[]
    for j in range(w):
        s=list(base);s[len(p)+j]=1;cols.append(add(action(s),h,-1))
    piv=[];B={}
    # Basis with certificates in original seed coordinates.
    for j,v in enumerate(cols):
        e=tuple(int(i==j) for i in range(w))
        for i,(a,c) in sorted(B.items()):f=v[i];v=add(v,a,-f);e=add(e,c,-f)
        if any(v):
            i=next(i for i,x in enumerate(v) if x);B[i]=(scale(v,v[i]),scale(e,v[i]));piv.append(j)
    coords=[];ker=[]
    for j,v in enumerate(cols):
        c=(0,)*w
        for i,(a,e) in sorted(B.items()):f=v[i];v=add(v,a,-f);c=add(c,e,f)
        assert not any(v);coords.append(tuple(c[i] for i in piv))
        if j not in piv:ker.append(add(tuple(int(i==j) for i in range(w)),c,-1))
    return piv,coords,ker

def represent(q,piv,w):
    t=[0]*w
    for j,b in zip(piv,q):t[j]=b
    return tuple(t)

def project(t,coords,r):return tuple(sum(a*c[i] for a,c in zip(t,coords))%3 for i in range(r))

def gated(G,n):
    # z=0: unique zero witness. z=1: G with one independent multiplicity bit.
    z=n+1;t=n+2;N=n+2;F=[(z,-i) for i in range(1,n+1)]+[(z,-t)]
    for c in G:
        if len(c)<=2:F.append((-z,)+c)
        else:
            a,b,c=c;N+=1;y=N
            F.extend(((-y,z),(-y,-a),(-z,a,y),(-y,b,c)))
    return canon(F),N

def main():
    rng=Random(620);cases=seeds=reopens=child_checks=inert=positive=tail_witnesses=0;rank_reductions=0;max_w=0
    for n in range(1,5):
        for _ in range(12):
            F=canon(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,min(n,3)+1))) for _ in range(rng.randrange(6)))
            S=[x for x in product(range(2),repeat=n) if accepts(F,x)];P=infer(F,n)
            if P is None:assert not S;continue
            assert all(all(x[i]==b for i,b in P.items()) for x in S)
            k=rng.randrange(1,4);L=n+2*k-1;w=rng.randrange(1,min(L,4)+1);p=tuple(rng.randrange(3) for _ in range(L-w));max_w=max(max_w,w)
            piv,coords,ker=quotient(n,k,p,P);r=len(piv);rank_reductions+=r<w;cases+=1
            counts={};vals={};freq=Counter();truth=[[] for _ in range(3)]
            for q in product(range(3),repeat=r):
                s=p+represent(q,piv,w);H=sum(not any(hashval(n,k,s,x)) for x in S);counts[q]=H;vals[q]=H*(2-H)
            for t in product(range(3),repeat=w):
                q=project(t,coords,r);rep=represent(q,piv,w);freq[q]+=1;seeds+=1
                assert all(hashval(n,k,p+t,x)==hashval(n,k,p+rep,x) for x in S);reopens+=len(S)
                H=sum(not any(hashval(n,k,p+t,x)) for x in S);assert H==counts[q];truth[t[0]].append(H*(2-H))
            assert set(freq.values())=={3**(w-r)}
            V=Q(sum(vals.values()),3**r);assert V==Q(sum(map(sum,truth)),3**w)
            if any(v[0] for v in ker):
                inert+=1;assert all(Q(sum(a),len(a))==V for a in truth);child_checks+=3
            else:
                for d in range(3):
                    a=[v for q,v in vals.items() if represent(q,piv,w)[0]==d];assert len(a)==3**(r-1);assert Q(sum(a),len(a))==Q(sum(truth[d]),len(truth[d]));child_checks+=1
            if V>0:
                positive+=1;assert sum(counts.values())<2*3**r
                # Actual budgeted decoder, no supplied support or occupancy used to choose charts.
                found=None
                for q in product(range(3),repeat=r):
                    s=p+represent(q,piv,w);A=matrix(n,k,s[:n+k-1]);b=tuple(-v%3 for v in s[n+k-1:]);x,_=decode_singleton(F,n,A,b,128)
                    if x is not None:found=x;break
                assert found in S;tail_witnesses+=1
    repairs=[]
    for m in (1,2,4,8,16):
        F,n,p=adversary(m);P=infer(F,n);assert P=={i:0 for i in range(n)}
        augmented=canon(F+tuple((-(i+1),) for i in P));lo,hi,c,t,_,_=shared(translation(augmented,n,1,p,()),Q(1,8*(n+1)),0)
        assert lo==hi==(2,-1,-1) and c==[0] and t==0;repairs.append(n)
    gated_checks=0
    for n in range(1,4):
        for _ in range(20):
            G=canon(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,n+1))) for _ in range(rng.randrange(7)))
            m=sum(accepts(G,x) for x in product(range(2),repeat=n));F,N=gated(G,n)
            H=sum(accepts(F,x) for x in product(range(2),repeat=N));assert H==1+2*m
            psi=H*(2-H);assert (Q(psi,3)>Q(1,24))==(m==0);assert (2*psi>=-Q(1,8*(N+1)))==(m==0);gated_checks+=1
    print(dict(quotient_cases=cases,rank_reductions=rank_reductions,max_free_seed_trits=max_w,original_seed_checks=seeds,source_action_reopenings=reopens,child_average_checks=child_checks,inert_next_trits=inert,positive_tails=positive,verified_tail_witnesses=tail_witnesses,repaired_adversary_variables=repairs,gated_certificate_controls=gated_checks))
if __name__=='__main__':main()
