"""Section 67: parsimonious 3CNF -> 2CNF + actual Toeplitz prefix."""
from itertools import product
from random import Random
from math import prod


def accepts(F,x):
    return all(any(bool(x[abs(l)-1])==(l>0) for l in c) for c in F)


def build(G,r,pad):
    m=len(G);k=m+pad;assert k>0
    n=3*k+r;d=n+k-1;a=[0]*d
    for h in range(3):a[n-1-h*k]=1
    F=[];local=[]
    def lit(l):return (3*k+abs(l))*(1 if l>0 else -1)
    for i,C in enumerate(G):
        assert len(C)<=3
        R=[]
        for j in range(3):
            y=j*k+i+1
            if j>=len(C):R.append((-y,));continue
            R.append((-y,lit(C[j])))
            R.extend((-y,-lit(l)) for l in C[:j])
        local.append(R);F.extend(R)
    for i in range(m,k):
        R=[(i+1,-(k+i+1)),(-(2*k+i+1),)]
        local.append(R);F.extend(R)
    return n,k,tuple(a)+(2,)*m,F,local


def hashval(n,k,s,x):
    return tuple((sum(s[n-1+i-j]*x[j] for j in range(n))+s[n+k-1+i])%3 for i in range(k))


def lift(G,x,t):
    triples=[]
    for C in G:
        j=next((j for j,l in enumerate(C) if bool(x[abs(l)-1])==(l>0)),None)
        if j is None:return None
        triples.append(tuple(int(h==j) for h in range(3)))
    triples.extend(((0,0,0),(1,0,0),(1,1,0))[(-z)%3] for z in t)
    return tuple(row[h] for h in range(3) for row in triples)+tuple(x)


def main():
    rng=Random(670);fixtures=localchecks=jointchecks=occupancies=0
    for r in range(1,5):
        for _ in range(24):
            G=[tuple(rng.choice((-1,1))*rng.randrange(1,r+1) for _ in range(rng.randrange(4))) for _ in range(rng.randrange(5))]
            pad=rng.randrange(1,4);n,k,p,F,R=build(G,r,pad);m=len(G)
            assert all(len(c)<=2 for c in F)
            assert [[p[n-1+i-j] for j in range(n)] for i in range(k)]==[[int(j in (i,k+i,2*k+i)) for j in range(n)] for i in range(k)]
            X=list(product((0,1),repeat=r));M=sum(accepts(G,x) for x in X)
            for t in product(range(3),repeat=pad):
                H=0
                for x in X:
                    z=[0]*(3*k)+list(x);counts=[]
                    for i,cs in enumerate(R):
                        choices=[]
                        for triple in product((0,1),repeat=3):
                            for h,b in enumerate(triple):z[h*k+i]=b
                            if (sum(triple)+(2 if i<m else t[i-m]))%3==0 and accepts(cs,z):choices.append(triple)
                            localchecks+=1
                        counts.append(len(choices))
                    c=prod(counts);assert c==int(accepts(G,x));H+=c
                    y=lift(G,x,t)
                    assert (y is not None)==bool(c)
                    if y is not None:assert y[3*k:]==x and accepts(F,y) and not any(hashval(n,k,p+t,y));jointchecks+=1
                assert H==M;occupancies+=1
            fixtures+=1
    # Independent exhaustive original Boolean lift (not factored reference).
    full=0
    for G in ([(1,2)],[(1,),(-1,)],[(1,-1)], [()], []):
        r=2;pad=1;n,k,p,F,R=build(G,r,pad)
        for t in product(range(3),repeat=pad):
            truth=[y for y in product((0,1),repeat=n) if accepts(F,y) and not any(hashval(n,k,p+t,y))]
            expected=[lift(G,x,t) for x in product((0,1),repeat=r) if accepts(G,x)]
            assert sorted(truth)==sorted(expected);full+=1
    # Singleton source, independent padding makes arbitrary effective seed rank.
    for pad in (1,8,32,64):
        G=[(1,),(-2,)];n,k,p,F,R=build(G,2,pad)
        for t in ((0,)*pad,(1,)*pad,(2,)*pad):
            y=lift(G,(1,0),t);assert accepts(F,y) and not any(hashval(n,k,p+t,y))
    print(dict(fixtures=fixtures,local_triple_checks=localchecks,verified_joint_lifts=jointchecks,occupancy_checks=occupancies,full_boolean_checks=full,padding_ranks=[1,8,32,64]))

if __name__=='__main__':main()
