"""Section 74: original CNF sign certificates in the Boolean ring over GF(2)."""
from itertools import combinations, product
from random import Random


def masks(n,d):
    return [sum(1<<i for i in c) for k in range(d+1) for c in combinations(range(n),k)]


def clause(c):
    # Falsity indicator; idempotent monomials are masks of variables.
    p={0}
    for l in c:
        v=1<<(abs(l)-1)
        q=set()
        for a in p:
            q.symmetric_difference_update({a|v})
        p=q if l<0 else p^q
    return p


def sat(F,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in F)


def reduce(v,B):
    for i in sorted(B,reverse=True):
        if v>>i&1:v^=B[i]
    return v


def space(F,n,d):
    M=masks(n,d);I={m:i for i,m in enumerate(M)};B={}
    for c in F:
        p=clause(c)
        if not p:continue
        u=0
        for m in p:u|=m
        if u.bit_count()>d:continue
        outside=[i for i in range(n) if not u>>i&1]
        for k in range(d-u.bit_count()+1):
            for c0 in combinations(outside,k):
                t=sum(1<<i for i in c0)
                v=sum(1<<I[m|t] for m in p)
                while v:
                    i=v.bit_length()-1
                    if i in B:v^=B[i]
                    else:B[i]=v;break
    return M,I,B


def pins(F,n,d):
    M,I,B=space(F,n,d);one=reduce(1,B)
    if not one:return None,len(B)
    assert one==1
    out=[]
    for j in range(n):
        v=reduce(1<<I[1<<j],B)
        out.append(v if v<=1 else None)
        # A nonconstant remainder gives two normalized dual functionals.
        if v>1:
            k=(v&~1).bit_length()-1
            for w in (1,1|(1<<k)):
                assert all((reduce(row,B)&w).bit_count()%2==0 for row in B.values())
            assert (v&1).bit_count()%2 != (v&(1|(1<<k))).bit_count()%2
    return out,len(B)


def affine_basis(vs):
    B={}
    for v in vs:
        while v:
            i=v.bit_length()-1
            if i in B:v^=B[i]
            else:B[i]=v;break
    return tuple(B.values())


def coordinate_image(F,n,d):
    M,I,B=space(F,n,d)
    if not reduce(1,B):return None
    a=0;columns={}
    for j in range(n):
        v=reduce(1<<I[1<<j],B)
        if v&1:a|=1<<j
        v&=~1
        while v:
            bit=v&-v;columns[bit]=columns.get(bit,0)|(1<<j);v^=bit
    return a,affine_basis(columns.values())


def expand(a,K):
    V={a}
    for k in K:V|={v^k for v in V}
    return V


def restrict(F,j,b):
    return [tuple(l for l in c if abs(l)!=j) for c in F if not any(abs(l)==j and (l>0)==bool(b) for l in c)]


def gate(G,n):
    s=n+1;F=[(s,-i) for i in range(1,n+1)];a=n+1
    for c in G:
        if len(c)<=2:F.append((-s,*c))
        else:
            l,m,k=c;a+=1
            F.extend([(-s,l,a),(-a,m,k),(s,-a)])
    return F,a,s


def original7():
    sets=[[0,4,5,6],[0,1,4,6],[0,4,5,7],[0,4,5,6],[0,4,5,6],[0,1,2,7],[0,3,4,6]]
    return [tuple(-(j+1) if p>>k&1 else j+1 for k,j in enumerate((i,(i+1)%7,(i+3)%7))) for i,S in enumerate(sets) for p in range(8) if p not in S]


def main():
    rng=Random(74);tests=branch=0
    for n in range(1,7):
        for _ in range(25):
            F=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(4))) for _ in range(rng.randrange(12))]
            truth=[x for x in range(1<<n) if sat(F,x)]
            for d in range(1,n+1):
                P,r=pins(F,n,d)
                if P is None:assert not truth
                else:
                    assert all(all(b is None or x>>j&1==b for j,b in enumerate(P)) for x in truth)
                    if d==n:
                        assert truth and P==[next(iter({x>>j&1 for x in truth})) if len({x>>j&1 for x in truth})==1 else None for j in range(n)]
                A=coordinate_image(F,n,d)
                if A is None:assert not truth
                else:
                    V=expand(*A);assert set(truth)<=V
                    if d==n:
                        a=truth[0];assert V==expand(a,affine_basis(x^a for x in truth))
                tests+=1
            # Restriction/lift of a bounded contradiction, allowing one extra degree.
            for j in range(1,n+1):
                for b in (0,1):
                    G=restrict(F,j,b)
                    for d in range(1,n):
                        P,_=pins(G,n,d)
                        if P is None:
                            Q,_=pins(F,n,d+1);assert Q is None or Q[j-1]==1-b
                            branch+=1
    F=original7();assert [x for x in range(128) if sat(F,x)]==[0]
    for d in range(3,8):
        P,r=pins(F,7,d);A=coordinate_image(F,7,d);print('section72',d,P,r,'image rank',len(A[1]))
    for t in (1,37,85,127):
        H=[tuple(-l if t>>(abs(l)-1)&1 else l for l in c) for c in F]
        P,r=pins(H,7,4);assert P==[t>>i&1 for i in range(7)]
    # Gate an inconsistent 2-CNF and a contradictory 3-CNF; no witness used.
    for k in (2,3):
        G=[tuple(-i if b else i for i,b in enumerate(p,1)) for p in product((0,1),repeat=k)]
        H,n,s=gate(G,k);assert [x for x in range(1<<n) if sat(H,x)]==[0]
        for d in range(1,k+3):
            P,r=pins(H,n,d);print('gated',k,'degree',d,'selector',P[s-1], 'rank',r)
        assert P[s-1]==0
    print('random degree fixtures',tests,'branch lift comparisons',branch)

if __name__=='__main__':main()
