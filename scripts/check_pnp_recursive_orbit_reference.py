from itertools import product, permutations
from collections import Counter
from random import Random
from time import monotonic

# Independent mathematical model: compare full and orbit-mass extension
# counts for a stable group, including actual transported prefix witnesses.
def run(bags, clauses, columns, G):
    n=len(columns)
    first=[next(j for j,b in enumerate(bags) if i in b) for i in range(n)]
    last=[max(j for j,b in enumerate(bags) if i in b) for i in range(n)]
    owned=[[] for b in bags]
    for c in clauses:
        owned[next(j for j,b in enumerate(bags) if {abs(l)-1 for l in c}<=set(b))].append(c)
    D={((),0):(1,{})};peak=1
    for j,b in enumerate(bags):
        fresh=[i for i in b if first[i]==j];N={}
        for (key,s),(mass,w) in D.items():
            for bits in product((0,1),repeat=len(fresh)):
                z=dict(zip(fresh,bits));x=dict(key)|z
                if not all(any(x[abs(l)-1]==int(l>0) for l in c) for c in owned[j]):continue
                live={i:v for i,v in x.items() if last[i]>j}
                k,g=min((tuple(sorted((g[i],v) for i,v in live.items())),g) for g in G)
                t=(s+sum(columns[i]*z[i] for i in fresh))%3
                old,rep=N.get((k,t),(0,{g[i]:v for i,v in (w|z).items()}))
                N[k,t]=(old+mass,rep)
        D=N;peak=max(peak,len(D))
    for (_,s),(mass,w) in D.items():
        assert all(any(w[abs(l)-1]==int(l>0) for l in c) for c in clauses)
        assert sum(columns[i]*w[i] for i in range(n))%3==s
    return {s:mass for (_,s),(mass,_) in D.items()},peak

def main():
    start=monotonic(); rng=Random(36943);checks=0;savings=0
    # Two independent S3 actions; each bag retains whole symmetry blocks.
    G=tuple(tuple(p)+tuple(3+i for i in q) for p in permutations(range(3)) for q in permutations(range(3)))
    bags=((0,1,2),(0,1,2,3,4,5),(3,4,5)); identity=(tuple(range(6)),)
    for _ in range(128):
        clauses=set()
        for _ in range(rng.randrange(1,7)):
            c=tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(6),rng.randrange(1,4)))
            clauses.update(tuple(sorted((g[abs(l)-1]+1)*(1 if l>0 else -1) for l in c)) for g in G)
        cols=(rng.randrange(3),)*3+(rng.randrange(3),)*3
        exact=Counter(sum(a*b for a,b in zip(cols,x))%3 for x in product((0,1),repeat=6) if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in clauses))
        a,p=run(bags,clauses,cols,G);b,q=run(bags,clauses,cols,identity)
        assert a==b==dict(exact);assert p<=q
        checks+=1;savings+=p<q
    print(dict(checks=checks,strict_peak_reductions=savings,seconds=round(monotonic()-start,4)))
if __name__=='__main__':main()
