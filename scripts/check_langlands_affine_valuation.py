"""R407-R410: exact normalized affine jets and signed intersection filtration.
The state cap is a resource boundary, not an UNSAT certificate.
"""
from itertools import combinations, product
from collections import Counter
from random import Random
from math import comb
import sympy as sp


def canonical(rows):
    basis = {}
    for a,b in rows:
        for i,(u,v) in sorted(basis.items(), reverse=True):
            if a>>i&1: a,b=a^u,b^v
        if not a:
            if b: return None
            continue
        i=a.bit_length()-1
        for j,(u,v) in list(basis.items()):
            if u>>i&1: basis[j]=(u^a,v^b)
        basis[i]=(a,b)
    return tuple(basis[i] for i in sorted(basis,reverse=True))


def character(rows, mask):
    b=0
    for u,v in rows:
        if mask>>(u.bit_length()-1)&1: mask,b=mask^u,b^v
    return 0 if mask else (-1)**b


def jet(n, rows, tags, h, mask=0):
    """Sum over affine fibre, divided by 2^dimension, modulo 2^h."""
    assert rows is not None and all(z%4==1 for z in tags) and h>=1
    d=n-len(rows); mod=1<<h; ans=0
    for k in range(min(h-1,n)+1):
        for J in combinations(range(n),k):
            B=canonical(rows+tuple((1<<i,1) for i in J))
            if B is None: continue
            sign=character(B,mask)
            if not sign: continue
            e=2*k-(len(B)-len(rows)); assert e>=k
            if e>=h: continue
            u=sign*(1<<e)
            for i in J: u=u*((tags[i]-1)//4)%mod
            ans=(ans+u)%mod
    return ans


def violate(c):
    return tuple((1<<(abs(l)-1),int(l<0)) for l in c)


def terms(rows, clauses, cap):
    if rows is None: return {}
    states={rows:1}
    for c in clauses:
        out=Counter(states)
        for a,w in states.items():
            b=canonical(a+violate(c))
            if b is not None: out[b]-=w
        states={b:w for b,w in out.items() if w}
        if len(states)>cap: return None
    return states


def fibre_points(n, rows):
    if rows is None: return
    piv={u.bit_length()-1 for u,v in rows}; free=[i for i in range(n) if i not in piv]
    for bs in product((0,1),repeat=len(free)):
        a=sum(b<<i for b,i in zip(bs,free))
        for u,v in rows:
            if ((a&u).bit_count()&1)!=v: a^=1<<(u.bit_length()-1)
        yield a


def weight(a,tags,mod=None):
    w=1
    for i,z in enumerate(tags):
        if a>>i&1: w*=z
        if mod: w%=mod
    return w


def residue(n,rows,clauses,tags,H,cap=10000,mask=0):
    S=terms(rows,clauses,cap)
    if S is None: return None
    mod=1<<H; result=0; skipped=0
    for B,w in S.items():
        d=n-len(B)
        if d>=H: skipped+=1; continue
        h=H-d
        # Choose cheap exact route; affine jets avoid crossing width at low h.
        cost=sum(comb(n,k) for k in range(min(h-1,n)+1))
        if (1<<d)<cost:
            v=sum((-1)**((a&mask).bit_count()%2)*weight(a,tags,mod) for a in fibre_points(n,B))
        else:
            v=(1<<d)*jet(n,B,tags,h,mask)
        result=(result+w*v)%mod
    return result,skipped,len(S)


def parity(n,rows,clauses,cap=10000):
    """Low precision only: prune before generating the full signed frontier."""
    if rows is None: return 0,0,0
    suffix=[0]*(len(clauses)+1)
    for j in range(len(clauses)-1,-1,-1):
        suffix[j]=suffix[j+1]
        for l in clauses[j]: suffix[j]|=1<<(abs(l)-1)
    def can_finish(B,mask):
        # Project out all coordinates that future violation rows can pin.
        # The rank of surviving rows plus the number of projected coordinates
        # equals the maximum rank obtainable by adjoining all future pins.
        return mask.bit_count()+len(canonical(tuple((u&~mask,0) for u,v in B)))==n
    if not can_finish(rows,suffix[0]): return 0,1,0
    S={rows}; peak=1; skipped=0
    for j,c in enumerate(clauses):
        out=set()
        for a in S:
            b=canonical(a+violate(c))
            for B in (a,b):
                if B is None: continue
                if not can_finish(B,suffix[j+1]): skipped+=1; continue
                if B in out: out.remove(B)
                else: out.add(B)
        S=out; peak=max(peak,len(S))
        if len(S)>cap: return None,skipped,peak
    assert all(len(a)==n for a in S)
    return len(S)%2,skipped,peak


def promised_producer(n,rows,clauses,cap=10000):
    """Witness-only, parity zero is UNKNOWN unless a promise is external."""
    q,_,peak=parity(n,rows,clauses,cap)
    if q!=1: return None,peak
    a=0
    for i in range(n):
        q,_,p=parity(n,canonical(rows+((1<<i,1),)),clauses,cap)
        peak=max(peak,p)
        if q is None: return None,peak
        a|=q<<i
    if not sat(a,clauses) or any((a&u).bit_count()%2!=v for u,v in rows):
        return None,peak
    M=1<<(n+2); A=1
    for i in range(n): A=A*(1+pow(5,1<<i,M))%(4*M)
    return (a,(3*A-4*pow(5,a,M))%(4*M)),peak


def sat(a,clauses):
    return all(any(((a>>(abs(l)-1))&1)==int(l>0) for l in c) for c in clauses)


def bonferroni(n,rows,clauses,k):
    if rows is None:return 0
    total=0
    for j in range(min(k,len(clauses))+1):
        for inds in combinations(range(len(clauses)),j):
            B=canonical(rows+tuple(v for i in inds for v in violate(clauses[i])))
            if B is not None: total+=(-1)**j*(1<<(n-len(B)))
    return total


def main():
    a,b,c=sp.symbols('a b c'); X=sp.symbols('X0:3'); z=[1+4*t for t in (a,b,c)]
    assert sp.expand(sp.prod(1+X[i]*(z[i]-1) for i in range(3))-sum(4**len(J)*sp.prod((a,b,c)[i]*X[i] for i in J) for k in range(4) for J in combinations(range(3),k)))==0
    rng=Random(407); stats=Counter()
    for n in range(1,9):
        for _ in range(25):
            A=canonical(tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+2))))
            if A is None: stats['empty_affine']+=1; continue
            pts=list(fibre_points(n,A)); d=n-len(A)
            assert len(pts)==1<<d and all(all((a&u).bit_count()%2==v for u,v in A) for a in pts)
            tags=[1+4*rng.randrange(-5,6) for i in range(n)]
            exact=sum(weight(a,tags) for a in pts)
            assert exact%(1<<(d+1))==1<<d; stats['valuation']+=1
            for mask in (0,rng.randrange(1<<n)):
                q=sum((-1)**((a&mask).bit_count()%2)*weight(a,tags) for a in pts)
                for h in (1,2,3,4):
                    assert (q-(1<<d)*jet(n,A,tags,h,mask))%(1<<(d+h))==0
                    stats['jets']+=1
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randint(1,min(3,n)))) for _ in range(rng.randrange(0,8))]
            ws=[a for a in pts if sat(a,f)]; stats['singleton' if len(ws)==1 else 'unsat' if not ws else 'multi']+=1
            for H in (1,2,3,n+2):
                for mask in (0,rng.randrange(1<<n)):
                    r,skip,_=residue(n,A,f,tags,H,mask=mask)
                    assert r==sum((-1)**((a&mask).bit_count()%2)*weight(a,tags) for a in ws)%(1<<H)
                    stats['residues']+=1; stats['skipped']+=skip
            p,skip,peak=parity(n,A,f); assert p==len(ws)%2
            stats['pruned_parity']+=1; stats['pruned_branches']+=skip
            ans,_=promised_producer(n,A,f)
            if len(ws)==1:
                assert ans is not None and ans[0]==ws[0]
                M=1<<(n+2); Z=[pow(5,1<<i,M) for i in range(n)]; B=1
                for z in Z: B=B*(1+z)%(4*M)
                assert ans[1]==(3*B-4*sum(weight(a,Z,M) for a in ws))%(4*M)
                stats['packed_singletons']+=1
            elif ans is not None: assert ans[0] in ws
            for k in range(5):
                v=bonferroni(n,A,f,k)
                assert (v>=len(ws) if k%2==0 else v<=len(ws))
                if d>3*k:
                    assert v%(1<<(d-3*k))==0
                    if len(ws)==1: assert v<=0 if k%2 else v>=2
                stats['bonferroni']+=1
    for n in (16,32,64,128):
        A=canonical(tuple(((1<<i)|(1<<(i+1)),i%2) for i in range(0,n,2)))
        tags=[5]*n; d=n//2
        # Independent product by disjoint pair constraints, no enumeration.
        q=1
        for i in range(d): q*=26 if i%2==0 else 10
        assert q%(1<<(d+1))==1<<d
        for h in (1,2):
            assert jet(n,A,tags,h)==(q>>d)%(1<<h); stats['large_jets']+=1
    for n in (8,16,24):
        # Unique all-zero witness, deliberately no expensive full expansion.
        f=[(-i,) for i in range(1,n+1)]
        for k in (1,2,3):
            if n<=3*k: continue
            v=bonferroni(n,(),f,k)
            assert v<=0 if k%2 else v>=2
            assert v%(1<<(n-3*k))==0; stats['singleton_order_controls']+=1
    for n in (16,32,64):
        a=rng.randrange(1<<n); f=[(i+1 if a>>i&1 else -i-1,) for i in range(n)]
        ans,peak=promised_producer(n,(),f,cap=1)
        assert ans is not None and ans[0]==a and peak==1
        stats['large_pruned_producers']+=1
    assert residue(8,(),[(-i,) for i in range(1,9)],[5]*8,3,cap=4) is None
    print(dict(stats))


if __name__=='__main__': main()
