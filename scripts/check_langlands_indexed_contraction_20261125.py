from itertools import product
from collections import Counter
from random import Random
from sympy import Matrix, eye, zeros, Rational

# W2: original S3, actual double cosets and transport of labelled pairs.
G=list(product(range(3),range(2))); e=(0,0)
def mul(a,b): return ((a[0]+(-1)**a[1]*b[0])%3,(a[1]+b[1])%2)
def inv(a): return next(b for b in G if mul(a,b)==e)
subs=[[e],[(0,0),(0,1)],[(0,0),(1,1)],[(0,0),(2,1)],[(i,0) for i in range(3)],G]
def cosets(H):
    cs=[]; mp={}
    for a in G:
        if a not in mp:
            cs.append(a)
            for h in H: mp[mul(a,h)]=(a,h)
    return cs,mp
mackey=trans=0
for H,J in product(subs,repeat=2):
    A,am=cosets(H); B,bm=cosets(J); seen=set()
    for g in G:
        if g in seen:continue
        seen.update(mul(mul(h,g),j) for h,j in product(H,J))
        K=[h for h in H if mul(mul(inv(g),h),g) in J]
        C,cm=cosets(K)
        f={c:(am[c][0],bm[mul(c,g)][0]) for c in C}
        assert len(set(f.values()))==len(C)
        for t,c in product(G,C):
            d,k=cm[mul(t,c)]
            a,b=f[c]; aa,ha=am[mul(t,a)]; bb,hb=bm[mul(t,b)]
            assert f[d]==(aa,bb)
            # Coset gauge: c=a*h0, c*g=b*j0. Transport on arbitrary H,J reps follows these group equalities.
            h0=am[c][1]; j0=bm[mul(c,g)][1]
            h1=am[d][1]; j1=bm[mul(d,g)][1]
            assert mul(ha,h0)==mul(h1,k)
            assert mul(hb,j0)==mul(j1,mul(mul(inv(g),k),g))
            mackey+=1
    assert len(seen)==6
for K,H in product(subs,repeat=2):
    if not set(K)<=set(H):continue
    A,am=cosets(H)
    # choose independently within H to avoid relying on global representative order
    B=[]; bm={}
    for b in H:
        if b not in bm:
            B.append(b)
            for k in K:bm[mul(b,k)]=(b,k)
    C,cm=cosets(K)
    f={(a,b):cm[mul(a,b)] for a,b in product(A,B)}
    assert len({c for c,k in f.values()})==len(C)
    for t,a,b in product(G,A,B):
        aa,h=am[mul(t,a)]; bb,k=bm[mul(h,b)]
        c,k0=f[a,b]; cc,k1=f[aa,bb]
        assert cm[mul(t,c)][0]==cc
        assert mul(cm[mul(t,c)][1],k0)==mul(k1,k)
        trans+=1

# W5: original constraints, shared seed, relative tag and chain length.
# Sparse factors with positive integer messages; record a backpointer for every inhabited output.
def factor(scope,D,pred):
    return tuple(scope),{v:1 for v in product(*(range(D[x]) for x in scope)) if pred(*v)}
def graph(n,clauses,side,D):
    x=[(side,'x',i) for i in range(n)]; t=[(side,'t',i) for i in range(n+1)]
    s=[('s',i) for i in range(n+1)]; D.update({v:2 for v in x});D.update({v:3 for v in t+s})
    z=(side,'k'); D[z]=2
    fs=[factor([t[0]],D,lambda a:a==0),factor([x[0],z],D,lambda a,b:a==b)]
    for i in range(n):
        fs.append(factor([x[i],s[i],s[i+1]],D,lambda a,b,c:(a+b+c)%3!=2))
        fs.append(factor([t[i],x[i],t[i+1]],D,lambda a,b,c:(a+2*b)%3==c))
    for cl in clauses:
        fs.append(factor([x[i] for i,b in cl],D,lambda *a,cl=cl:any(v==b for v,(_,b) in zip(a,cl))))
    return fs,t[-1],z

def eliminate(D,fs,out):
    fs=list(fs); left=set(D)-set(out); hist=[]; work=peak=0
    while left:
        def key(v):
            S={v}|{x for s,t in fs if v in s for x in s}; a=1
            for x in S:a*=D[x]
            return a,str(v)
        v=min(left,key=key);left.remove(v)
        hit=[(s,t) for s,t in fs if v in s]; fs=[(s,t) for s,t in fs if v not in s]
        scope=tuple(sorted({v}|{x for s,t in hit for x in s},key=str)); p={x:i for i,x in enumerate(scope)}
        rest=tuple(x for x in scope if x!=v); ids=[p[x] for x in rest]; lookup=[(tuple(p[x] for x in s),t) for s,t in hit]
        tab={}; back={}; rows=1
        for x in scope:rows*=D[x]
        peak=max(peak,rows);work+=rows
        for a in product(*(range(D[x]) for x in scope)):
            w=1
            for ii,t in lookup:
                w*=t.get(tuple(a[i] for i in ii),0)
                if not w:break
            if w:
                r=tuple(a[i] for i in ids);tab[r]=tab.get(r,0)+w;back.setdefault(r,a[p[v]])
        fs.append((rest,tab));hist.append((v,rest,back))
    tab={}; witnesses={}
    for a in product(*(range(D[x]) for x in out)):
        d=dict(zip(out,a));w=1
        for s,t in fs:w*=t.get(tuple(d[x] for x in s),0)
        if w:
            tab[a]=w
            for v,s,b in reversed(hist):d[v]=b[tuple(d[x] for x in s)]
            witnesses[a]=d
    return tab,witnesses,work,peak

def sat(x,C):return all(any(x[i]==b for i,b in cl) for cl in C)
def valid(x,s,C):return sat(x,C) and all((x[i]+s[i]+s[i+1])%3!=2 for i in range(len(x)))
def packet(C):
    L=Counter(); cond=rank=ex=sgn=power=0
    for (c,k,l),v in C.items():
        m=min(k,l);rank+=64*k*l*v;cond+=(112*k*l-4*m)*v;ex+=c*(28*k*l-m)*v;sgn+=(k*l-m)*v
        h=k*l*(k-l)//2; b=m*(m-1)//2-m*(l-1)
        power+=(112*h-4*b)*v
        for j in range(m):L[c,j-l+1]+=v
    return L,rank,cond,ex%3,sgn%2,power
rng=Random(275); fixtures=checks=witnesses=work=peak=0; raw=multi=0
for n in range(1,6):
    for trial in range(8):
        def cnf():
            return [tuple((i,rng.randrange(2)) for i in sorted(rng.sample(range(n),rng.randrange(1,min(n,3)+1)))) for _ in range(rng.randrange(5))]
        F,H=cnf(),cnf();D={};fs,t,k=graph(n,F,'a',D);gs,u,l=graph(n,H,'b',D)
        c=('relative',0);D[c]=3;fs+=gs+[factor([t,u,c],D,lambda a,b,c:(a-b)%3==c)]
        # Some original seed pins: not every seed is enumerated by contraction.
        pins={i:rng.randrange(3) for i in range(n+1) if rng.randrange(4)==0}
        for i,p in pins.items():fs.append(factor([('s',i)],D,lambda a,p=p:a==p))
        tab,back,w,p=eliminate(D,fs,(c,k,l));work+=w;peak=max(peak,p)
        C=Counter({(c,k+1,l+1):v for (c,k,l),v in tab.items()}); ref=Counter(); RL=Counter(); Rrank=Rc=Re=Rs=Rp=0; Rsign=Counter()
        for s in product(range(3),repeat=n+1):
            if any(s[i]!=v for i,v in pins.items()):continue
            A=[x for x in product(range(2),repeat=n) if valid(x,s,F)]
            B=[x for x in product(range(2),repeat=n) if valid(x,s,H)]
            multi+=int(len(A)*len(B)>1)
            for a,b in product(A,B):
                cc=2*(sum(a)-sum(b))%3; kk=a[0]+1; ll=b[0]+1
                ref[cc,kk,ll]+=1
                full=[i-j for i in range(kk) for j in range(ll)]
                ker=[j-ll+1 for j in range(min(kk,ll))]
                quotient=full.copy()
                for j in ker:
                    quotient.remove(j); RL[cc,j]+=1
                Rrank+=64*len(full); Rc+=108*len(full)+4*len(quotient)
                Re+=cc*(27*len(full)+len(quotient)); Rs+=len(quotient)
                Rp+=108*sum(full)+4*sum(quotient)
                # Actual four-corner multiplicities of B_b U-type analogue.
                for p,q,sign in [(1,1,1),(1,0,-1),(0,1,-1),(0,0,1)]:
                    for s0,w0 in [(0,3-2*p),(1,2*p)]:
                        for s1,w1 in [(0,3-2*q),(1,2*q)]:
                            for j in ker:Rsign[cc,s0^s1,j]+=sign*w0*w1
        assert C==ref;assert packet(C)==(RL,Rrank,Rc,Re%3,Rs%2,Rp);checks+=2
        for (cc,kk,ll),d in back.items():
            a=tuple(d['a','x',i] for i in range(n));b=tuple(d['b','x',i] for i in range(n));s=tuple(d['s',i] for i in range(n+1))
            assert valid(a,s,F) and valid(b,s,H) and all(s[i]==v for i,v in pins.items())
            assert (2*(sum(a)-sum(b))%3,a[0],b[0])==(cc,kk,ll)
            witnesses+=1
        # Signed 4-corner pole: loop sectors + and - independently, zero is not support.
        signed=Counter()
        for (cc,kk,ll),v in C.items():
            for j in range(min(kk,ll)):
                signed[cc,0,j-ll+1]+=8*v;signed[cc,1,j-ll+1]-=8*v
        assert signed==Rsign;checks+=1
        assert sum(signed.values())==0 and (not C or any(signed.values()));checks+=1
        fixtures+=1;raw+=3**(n+1)*4**n
print(dict(mackey=mackey,transitivity=trans,fixtures=fixtures,packet_and_signed_checks=checks,witnesses=witnesses,rows=work,peak=peak,raw_pair_space=raw,multiple_pair_seed_fibres=multi))
