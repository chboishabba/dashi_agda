"""Section 76: original CNF conditional component-local Shannon portfolios."""
from fractions import Fraction as Q
from itertools import product
from random import Random
from check_p0_shannon_path_budget_20261125 import sat, propagate, search, path, original7


def condition(F,n,pins):
    x=sum(b<<(j-1) for j,b in pins.items());a=sum(1<<(j-1) for j in pins)
    st=propagate(F,x,a)
    if st is None:return None
    x,a,R=st
    free=[j for j in range(1,n+1) if not a>>(j-1)&1];parent={j:j for j in free}
    def root(j):
        while j!=parent[j]:j=parent[j]
        return j
    for c in R:
        j=abs(c[0])
        for l in c[1:]:parent[root(abs(l))]=root(j)
    parts={}
    for j in free:parts.setdefault(root(j),[[],[]])[0].append(j)
    for c in R:parts[root(abs(c[0]))][1].append(c)
    Cs=[]
    for J,G in parts.values():
        ix={j:i+1 for i,j in enumerate(J)}
        Cs.append((J,[tuple(ix[abs(l)]*(1 if l>0 else -1) for l in c) for c in G]))
    return x,a,Cs


def cut(F,n,budget):
    # Deterministic primal-graph greedy separator; no SAT observation used.
    edges={j:set() for j in range(1,n+1)}
    for c in F:
        J=set(map(abs,c))
        if any(-l in c for l in c):continue
        for j in J:edges[j].update(J-{j})
    S=[]
    for _ in range(min(budget,n)):
        j=max((v for v in edges if v not in S),key=lambda v:(len(edges[v]-set(S)),-v))
        S.append(j)
    return S


def decode(F,n,S,tau,modes=(0,1,2,3)):
    assert len(set(S))==len(S) and all(1<=j<=n for j in S)
    calls=0;branches=0
    for bits in product(range(2),repeat=len(S)):
        branches+=1;st=condition(F,n,dict(zip(S,bits)))
        if st is None:continue
        x,a,Cs=st;receipts=[]
        for J,G in Cs:
            for m in modes:
                L,stats=search(G,len(J),tau,m);calls+=stats[0]
                if L:break
            else:break
            y,w=L[0]
            assert sat(G,y)
            for i,j in enumerate(J):x|=((y>>i)&1)<<(j-1);a|=1<<(j-1)
            receipts.append((J,m,y,w))
        else:
            assert a==(1<<n)-1 and sat(F,x)
            assert calls<=2**len(S)*len(modes)*3*n*(1//tau)
            return x,receipts,calls,branches
    assert calls<=2**len(S)*len(modes)*3*n*(1//tau)
    return None,[],calls,branches


def reference(F,n,S,tau):
    # Independent enumeration of original solutions, checking their local path masses.
    for x in range(1<<n):
        if not sat(F,x):continue
        pins={j:(x>>(j-1))&1 for j in S};z,a,Cs=condition(F,n,pins)
        assert not ((z^x)&a)
        if all(any(path(G,len(J),sum(((x>>(j-1))&1)<<i for i,j in enumerate(J)),m)[0]>=tau for m in range(4)) for J,G in Cs):return True
    return False


def main():
    rng=Random(76);checks=products=solved=0
    for n in range(1,8):
        for _ in range(24):
            F=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(4))) for _ in range(rng.randrange(15))]
            for S in ([],cut(F,n,1),cut(F,n,2)):
                for bits in product(range(2),repeat=len(S)):
                    st=condition(F,n,dict(zip(S,bits)))
                    truth={x for x in range(1<<n) if sat(F,x) and all((x>>(j-1))&1==b for j,b in zip(S,bits))}
                    if st is None:assert not truth
                    else:
                        z,a,Cs=st;rebuilt={z}
                        for J,G in Cs:
                            ys=[sum(((y>>i)&1)<<(j-1) for i,j in enumerate(J)) for y in range(1<<len(J)) if sat(G,y)]
                            rebuilt={v|y for v in rebuilt for y in ys}
                        assert rebuilt==truth
                    products+=1
                for tau in (Q(1,2),Q(1,2*n),Q(1,2*(2*n)**2)):
                    x,R,c,b=decode(F,n,S,tau);assert (x is not None)==reference(F,n,S,tau)
                    checks+=1;solved+=x is not None
    print('random sources',168,'original fibre product comparisons',products,'threshold comparisons',checks,'successes',solved)
    for g in (2,4,8,16,32):
        n=7*g;F=[c for i in range(g) for c in original7(127*(i%2),7*i)];x=sum(127<<(7*i) for i in range(g) if i%2)
        k=[path(F,n,x,m)[1] for m in range(4)]
        y,R,c,b=decode(F,n,[],Q(1,2));assert y==x and len(R)==g and min(k)>0
        assert all(w>=Q(1,2) for J,m,z,w in R)
        print('mixed source',n,'global discrepancies',k,'local calls',c,'components',len(R))
        # Connected original source: a common guard z, forced by two original clauses.
        z=n+1;v=n+2;H=[(-z,*cl) for cl in F]+[(z,v),(z,-v),(-z,-v)]
        S=cut(H,n+2,1);assert S==[z]
        y,R,c,b=decode(H,n+2,S,Q(1,2));assert y==x|(1<<n) and len(R)==g
        print('guarded source',n+2,'separator',S,'local calls',c,'branches',b)


if __name__=='__main__':main()
