"""Section72: exact affine hull descent and Walsh translation quotient."""
from itertools import product, combinations
from random import Random

def dot(a,b):return (a&b).bit_count()%2

def basis(vs):
    B={}
    for v in vs:
        while v:
            i=v.bit_length()-1
            if i in B:v^=B[i]
            else:B[i]=v;break
    for i in sorted(B):
        for j in B:
            if j>i and B[j]>>i&1:B[j]^=B[i]
    return tuple(B[i] for i in sorted(B,reverse=True))

def chart(rows,d):
    B={}
    for v,b in rows:
        while v:
            i=v.bit_length()-1
            if i in B:w,c=B[i];v^=w;b^=c
            else:B[i]=(v,b);break
        else:
            if b:return None
    def extend(z,hom):
        for i,(v,b) in sorted(B.items()):
            if dot(v,z)!=(0 if hom else b):z^=1<<i
        return z
    return extend(0,False),tuple(extend(1<<i,True) for i in range(d) if i not in B)

def lin(K,z):
    out=0
    for i,k in enumerate(K):
        if z>>i&1:out^=k
    return out

def observe(B,z):return sum(dot(v,z)<<i for i,v in enumerate(B))

def good(E,z):return all(not all(dot(v,z)==b for v,b in e) for e in E)

def cnf(F):return [[(1<<abs(l)-1,int(l<0)) for l in c] for c in F]

def project(E,a,K):return [[(observe(K,v),b^dot(v,a)) for v,b in e] for e in E]

def groups(E):
    G={}
    for e in E:G.setdefault(basis(v for v,b in e),[]).append(e)
    out=[]
    for B,es in G.items():
        S={p for p in range(1<<len(B)) if good(es,chart([(v,p>>i&1) for i,v in enumerate(B)],max((v.bit_length() for v in B),default=0))[0])}
        out.append((B,S))
    return out

def hull(B,S):
    p=min(S);return [(lin(B,a),dot(a,p)) for a in range(1,1<<len(B)) if all(dot(a,q^p)==0 for q in S)]

def quotient(B,S):
    k=len(B);W=basis(a for a in range(1<<k) if sum((-1)**dot(a,p) for p in S))
    T={t for t in range(1<<k) if {p^t for p in S}==S}
    assert T=={t for t in range(1<<k) if not observe(W,t)}
    A={observe(W,p) for p in S}
    assert all((p in S)==(observe(W,p) in A) for p in range(1<<k))
    return tuple(lin(B,w) for w in W),A

def pair_hull(B,S,C,T):
    U=basis(B+C)
    if len(U)==len(B)+len(C):return []
    d=max((v.bit_length() for v in U),default=0);A=set()
    for p in range(1<<len(U)):
        z=chart([(v,p>>i&1) for i,v in enumerate(U)],d)[0]
        if observe(B,z) in S and observe(C,z) in T:A.add(p)
    return hull(U,A) if A else None

def descend(E,d,pairs=True):
    a=0;K=tuple(1<<i for i in range(d));ranks=[]
    while True:
        P=project(E,a,K);G=groups(P)
        if any(not S for B,S in G):return None
        rows=[r for B,S in G for r in hull(B,S)]
        if pairs:
            for (B,S),(C,T) in combinations(G,2):
                h=pair_hull(B,S,C,T)
                if h is None:return None
                rows.extend(h)
        L=chart(rows,len(K))
        if L is None:return None
        b,H=L
        if len(H)==len(K):break
        ranks.append(len(K)-len(H));a^=lin(K,b);K=tuple(lin(K,h) for h in H)
    Q=[quotient(B,S) for B,S in G]
    U=basis(v for B,S in Q for v in B);res=[]
    for B,S in Q:
        # each row of B has unique coefficient mask in U
        C=[]
        for v in B:
            c=0
            for i,u in enumerate(U):
                if v>>(u.bit_length()-1)&1:v^=u;c^=1<<i
            assert v==0;C.append(c)
        res.append((tuple(C),S))
    def reopen(p,t=0):
        L=chart([(v,p>>i&1) for i,v in enumerate(U)],len(K));b,H=L
        return a^lin(K,b^lin(H,t))
    return len(U),len(K)-len(U),res,reopen,ranks,len(K),sum(len(B) for B,S in G),sum(len(B) for B,S in Q)

def accepted(R,p):return all(observe(B,p) in S for B,S in R)

def exclusions(B,S):return [[(v,p>>i&1) for i,v in enumerate(B)] for p in range(1<<len(B)) if p not in S]

def main():
    rng=Random(72);checks=0;counts=0
    for d in range(1,8):
        for _ in range(40):
            F=[tuple(rng.choice((-1,1))*rng.randint(1,d) for _ in range(rng.randrange(4))) for _ in range(rng.randrange(10))]
            E=cnf(F);truth={z for z in range(1<<d) if good(E,z)};R=descend(E,d)
            if R is None:assert not truth
            else:
                k,f,Q,reopen,*_=R;got=[reopen(p,t) for p in range(1<<k) if accepted(Q,p) for t in range(1<<f)]
                assert set(got)==truth and len(got)==len(truth);counts+=len(got)
            checks+=1
    # Pair-hull singleton (Section71 donor); local hulls alone leave two freedoms.
    for g in (4,8,16,32):
        E=[]
        for i in range(g):
            a,b,c,e=(1<<(4*i+j) for j in range(4))
            E+=exclusions((a,b,c),{0,2,5})+exclusions((a,b,e),{0,3,7})
        R=descend(E,4*g);assert R[:2]==(0,0) and R[3](0)==0
        print('pair singleton',4*g,'rank drops',R[4])
    # A true invisible direction in each full-affine-hull local predicate.
    E=[]
    for i in range(16):
        B=tuple(1<<(3*i+j) for j in range(3));E+=exclusions(B,{1,2,3,5,6,7})
    R=descend(E,48);assert R[:2]==(32,16) and R[4]==[]
    print('translation quotient',R[:2],R[6:])
    # Linear triple system, each local set full affine span; seek exact singleton
    # with no unary or pair-hull consequence, on literal original CNF.
    scopes=[tuple(1<<((i+j)%7) for j in (0,1,3)) for i in range(7)]
    options=[{0,*p} for p in combinations(range(1,8),3) if len(basis(p))==3]
    for trial in range(10000):
        S=[rng.choice(options) for _ in scopes];E=[e for B,A in zip(scopes,S) for e in exclusions(B,A)]
        if sum(good(E,z) for z in range(128))!=1:continue
        R=descend(E,7)
        if R is not None and R[4]==[] and R[:2]==(7,0):break
    else:raise AssertionError('no anti-control')
    print('full-hull singleton',trial,[sorted(A) for A in S])
    print('random CNF exact fibre comparisons',checks,'total original lifts',counts)

if __name__=='__main__':main()
