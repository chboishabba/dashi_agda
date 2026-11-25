"""R411-R414: future-safe affine projection of the simultaneous parity jet.
Only reference tests enumerate points. State cap returns UNKNOWN.
"""
from itertools import product
from random import Random
from collections import Counter
import sympy as sp


def rref(rows):
    basis={}
    for a,b in rows:
        for i,(u,v) in sorted(basis.items(),reverse=True):
            if a&i: a,b=a^u,b^v
        if not a:
            if b: return None
            continue
        i=1<<(a.bit_length()-1)
        for j,(u,v) in list(basis.items()):
            if u&i: basis[j]=(u^a,v^b)
        basis[i]=(a,b)
    return tuple(basis[i] for i in sorted(basis,reverse=True))


def xor_at(p,k,v):
    if v:
        p[k]=p.get(k,0)^v
        if not p[k]: del p[k]


def substitute(p,i,a,b):
    p=dict(p); v=p.pop(i,0)
    if b: xor_at(p,0,v)
    a^=i
    while a:
        j=a&-a; a^=j; xor_at(p,j,v)
    return p


def normalize(B,p):
    for a,b in B: p=substitute(p,1<<(a.bit_length()-1),a,b)
    return p


def forget(B,p,i):
    row=next(((a,b) for a,b in B if a&i),None)
    if row is None:
        # Both values occur: constants cancel, derivative survives.
        v=p.get(i,0)
        return B,({0:v} if v else {})
    a,b=row
    C=rref(tuple((u^a,v^b) if u&i else (u,v) for u,v in B if (u,v)!=row))
    return C,normalize(C,substitute(p,i,a,b))


def add(S,B,p):
    if not p: return
    q=S.setdefault(B,{})
    for i,v in p.items(): xor_at(q,i,v)
    if not q: del S[B]


def violation(c):
    return tuple((1<<(abs(l)-1),int(l<0)) for l in c)


def mask(c):
    m=0
    for l in c: m|=1<<(abs(l)-1)
    return m


def frontier(n,rows,clauses,cap=10000,project=True):
    B=rref(rows)
    if B is None: return 0,0,0,0
    suffix=[0]*(len(clauses)+1)
    for j in range(len(clauses)-1,-1,-1): suffix[j]=suffix[j+1]|mask(clauses[j])
    p=normalize(B,{0:1,**{1<<i:1<<(i+1) for i in range(n)}})
    S={B:p}; active=(1<<n)-1; peak=1; attempts=0; dropped=0
    for j in range(-1,len(clauses)):
        T={}
        if j<0: T=S
        else:
            for B,p in S.items():
                add(T,B,p); attempts+=1
                C=rref(B+violation(clauses[j])); attempts+=1
                if C is not None: add(T,C,normalize(C,p))
        if project or j==len(clauses)-1:
            keep=suffix[j+1]; dead=active&~keep
            S={}
            for B,p in T.items():
                d=dead
                while d and p:
                    i=d&-d; d^=i; B,p=forget(B,p,i)
                if p: add(S,B,p)
                else: dropped+=1
            active=keep
        else: S=T
        peak=max(peak,len(S))
        if len(S)>cap: return None,peak,attempts,dropped
    assert all(B==() and set(p)<={0} for B,p in S.items())
    return S.get((),{}).get(0,0),peak,attempts,dropped


def sat(a,clauses):
    return all(any(bool(a&(1<<(abs(l)-1)))==(l>0) for l in c) for c in clauses)


def valid(a,rows,clauses):
    return all((a&u).bit_count()%2==b for u,b in rows) and sat(a,clauses)


def packed(n,a):
    M=1<<(n+2); A=1
    for i in range(n): A=A*(1+pow(5,1<<i,M))%(4*M)
    return (3*A-4*pow(5,a,M))%(4*M)


def producer(n,rows,clauses,cap=10000):
    q,peak,attempts,dropped=frontier(n,rows,clauses,cap)
    if q is None or not q&1: return None,peak,attempts,dropped
    a=q>>1
    return ((a,packed(n,a)) if valid(a,rows,clauses) else None),peak,attempts,dropped


def main():
    # Exact square-zero jet multiplication, with F2 coefficients.
    t=sp.symbols('t'); a,b,c,d=sp.symbols('a b c d')
    assert sp.expand((a+b*t)*(c+d*t)-(a*c+(a*d+b*c)*t))==b*d*t*t
    rng=Random(411); stats=Counter()
    # Empty versus occupied zero mass with a surviving first moment.
    assert frontier(1,(),())[0]==2
    assert frontier(2,(),())[0]==0
    assert frontier(1,((1,0),(1,1)),())[0]==0
    for n in range(1,8):
        for _ in range(40):
            rows=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(3,n)+1))) for _ in range(rng.randrange(8))]
            if rng.randrange(4)==0: f.append((1,-1))
            ws=[a for a in range(1<<n) if valid(a,rows,f)]
            ref=0
            for a in ws: ref^=1|(a<<1)
            for clauses in (f,list(reversed(f)),rng.sample(f,len(f))):
                q,peak,at,dr=frontier(n,rows,clauses)
                assert q==ref; stats['jet_order_comparisons']+=1
                raw=frontier(n,rows,clauses,project=False)[0]
                assert raw==ref; stats['unprojected_comparisons']+=1
                stats['projected_attempts']+=at; stats['zero_packets']+=dr
            ans,_,_,_=producer(n,rows,f)
            if len(ws)==1:
                assert ans==(ws[0],packed(n,ws[0])); stats['singleton']+=1
            elif ans is not None: assert ans[0] in ws
            stats['empty' if not ws else 'multi' if len(ws)>1 else 'unique']+=1
    # Each 2-bit block forbids three corners; one original witness survives.
    # Raw R408 pruned parity frontier contains 3^k completed point choices.
    for k in (1,2,3,4,5,8,16,32,64):
        n=2*k; f=[]; witness=0
        for j in range(k):
            x,y=2*j+1,2*j+2
            a,b=rng.randrange(2),rng.randrange(2)
            witness|=a<<(x-1)|b<<(y-1)
            f.extend(tuple(-v if bit else v for v,bit in zip((x,y),q)) for q in product((0,1),repeat=2) if q!=(a,b))
        ans,peak,at,dr=producer(n,(),f,cap=4)
        assert ans==(witness,packed(n,witness)) and peak<=4
        stats['block_producers']+=1
        if k<=5:
            raw=frontier(n,(),f,project=False)
            assert raw[0]==(1|(witness<<1)); stats['raw_block_comparisons']+=1
        print('blocks',k,'projected_peak',peak,'attempts',at,'R408_boundary_states',3**k)
    print(dict(stats))


if __name__=='__main__': main()
