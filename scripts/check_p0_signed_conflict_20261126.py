"""Exact integer signed affine conflict packing; no SAT oracle.
Rows are (bitmask, rhs); terms are (tuple(rows), signed integer weight).
A receipt is a list of (indices, charge). No positivity means UNKNOWN.
"""
from random import Random


def conflict(terms,remaining):
    basis={}
    for i,(rows,w) in enumerate(terms):
        if not remaining[i] or w>=0:continue
        for a,b in rows:
            # A union provenance is sufficient: redundant owners are harmless.
            a,b,p=reduce_union(a,b,1<<i,basis)
            if not a:
                if b:return p
            else:basis[a.bit_length()-1]=(a,b,p)
    for i,(rows,w) in enumerate(terms):
        if not remaining[i] or w<=0:continue
        p=1<<i
        for a,b in rows:
            a,b,q=reduce_union(a,b,0,basis)
            if a or b:break
            p|=q
        else:return p
    return 0


def reduce_union(a,b,p,basis):
    while a:
        k=a.bit_length()-1
        if k not in basis:break
        c,d,q=basis[k];a^=c;b^=d;p|=q
    return a,b,p


def pack(c,terms,early=True):
    remaining=[abs(w) for _,w in terms]
    floor=c+sum(min(0,w) for _,w in terms);receipt=[]
    while not early or floor<=0:
        mask=conflict(terms,remaining)
        if not mask:break
        I=tuple(i for i in range(len(terms)) if mask>>i&1)
        delta=min(remaining[i] for i in I);assert delta>0
        for i in I:remaining[i]-=delta
        receipt.append((I,delta));floor+=delta
    return floor,receipt


def verify(c,terms,receipt):
    remaining=[abs(w) for _,w in terms];floor=c+sum(min(0,w) for _,w in terms)
    for I,delta in receipt:
        assert I and len(set(I))==len(I) and delta>0
        assert all(0<=i<len(terms) and remaining[i]>=delta for i in I)
        local=[int(i in I) for i in range(len(terms))]
        assert conflict(terms,local)
        for i in I:remaining[i]-=delta
        floor+=delta
    return floor


def conditioned(c,terms,hard):
    """Equivalent positivity on admissible quotient, including vacuous case.
    Positive rank-one terms are rewritten using their affine complements.
    Return the exact transformed objective for pack/verify.
    """
    K=1+abs(c)+sum(abs(w) for _,w in terms)
    out=[]
    for rows,w in list(terms)+[(R,K) for R in hard]:
        if w>0 and len(rows)==1:
            a,b=rows[0];c+=w;out.append((((a,b^1),),-w))
        else:out.append((rows,w))
    return c,out


def point(c,terms,x):
    return c+sum(w for R,w in terms if all((a&x).bit_count()%2==b for a,b in R))


def main():
    rng=Random(369);checks=0;strict=0;receipts=0;conditioned_checks=0
    for n in range(9):
        for _ in range(150):
            terms=[(tuple((rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(5))),rng.randrange(-8,9)) for i in range(rng.randrange(13))]
            c=rng.randrange(-8,9)
            a,R=pack(c,terms,False);assert verify(c,terms,R)==a
            b,S=pack(c,terms);assert verify(c,terms,S)==b
            truth=min(point(c,terms,x) for x in range(1<<n))
            base=c+sum(min(0,w) for _,w in terms)
            assert base<=b<=a<=truth
            checks+=1;strict+=a>base;receipts+=len(R)
            H=[tuple((rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(3))) for i in range(rng.randrange(4))]
            d,U=conditioned(c,terms,H);v,P=pack(d,U,False);assert verify(d,U,P)==v
            for x in range(1<<n):
                valid=not any(all((a&x).bit_count()%2==b for a,b in R) for R in H)
                q=point(d,U,x);assert q>=v
                assert q==point(c,terms,x) if valid else q>=1
            conditioned_checks+=1
    print('conditioned comparisons',conditioned_checks)
    print('random exact minimum comparisons',checks,'strict improvements',strict,'receipts',receipts)
    # Dense connected normal graph, each pair wants unequal labels. Triangles conflict.
    for n in (8,16,32,64):
        T=[(((1<<i ^ 1<<j,1),),-1) for i in range(n) for j in range(i+1,n)]
        a,R=pack(len(T),T,False);assert verify(len(T),T,R)==a and a>0
        truth=len(T)-(n//2)*((n+1)//2)
        assert a<=truth
        print('dense',n,'terms',len(T),'lower',a,'exact',truth,'receipts',len(R))
    # A positive domain is forced by the preferred negative domains.
    T=[(((1,0),),-3),(((2,1),),-2),(((3,1),),4)]
    a,R=pack(5,T,False);assert verify(5,T,R)==a==2==min(point(5,T,x) for x in range(4))
    # Deliberate blind spot: two positive domains cover the entire quotient.
    T=[(((1,0),),1),(((1,1),),1)]
    assert pack(0,T,False)[0]==0 and min(point(0,T,x) for x in range(2))==1
    d,U=conditioned(0,T,());assert pack(d,U,False)[0]==1
    # Two complementary higher-rank positive unions can still evade this check.
    T=[(((1,a),(2,b)),1) for a in (0,1) for b in (0,1)]
    d,U=conditioned(0,T,());assert pack(d,U,False)[0]==0
    assert min(point(d,U,x) for x in range(4))==1
    print('entailment, rank-one complement and blind-spot controls PASS')

if __name__=='__main__':main()
