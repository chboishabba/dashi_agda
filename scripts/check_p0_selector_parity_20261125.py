"""Section 68: original selector compatibility, exact parity bundle contraction."""
from itertools import product
from collections import defaultdict
from random import Random


def accepts(F,x):
    return all(any(bool(x[abs(l)-1])==(l>0) for l in c) for c in F)


def domains(F):
    D=[]
    for c in F:
        d=[]
        for j,l in enumerate(c):
            pins={};ok=True
            for z in tuple(-h for h in c[:j])+(l,):
                i=abs(z)-1;b=int(z>0)
                if i in pins and pins[i]!=b:ok=False
                pins[i]=b
            if ok:d.append(pins)
        D.append(d)
    return D


def compatible(p,q):return all(i not in q or q[i]==b for i,b in p.items())


def ac(D):
    while True:
        E=[[p for p in d if all(i==j or any(compatible(p,q) for q in e) for j,e in enumerate(D))] for i,d in enumerate(D)]
        if E==D:return E
        D=E


def selector_count(F,n):
    M=0;tuples=0
    for ds in product(*domains(F)):
        p={}
        for q in ds:
            if not compatible(p,q):break
            p.update(q)
        else:
            M+=2**(n-len(p));tuples+=1
    return M,tuples


def parity_clauses(I,b):
    return [tuple((i+1)*(-1 if z else 1) for i,z in zip(I,x)) for x in product((0,1),repeat=len(I)) if sum(x)%2!=b]


def extract(F):
    """Group by actual original scope; recognize exactly parity groups."""
    groups=defaultdict(list);res=[];rows=[]
    for c in F:
        I=tuple(sorted({abs(l)-1 for l in c}))
        if len(I)>3 or len(I)!=len(c):res.append(c);continue
        groups[I].append(c)
    for I,cs in groups.items():
        if not I:res.extend(cs);continue
        bad={tuple(int(-(i+1) in c) for i in I) for c in cs}
        ok=[x for x in product((0,1),repeat=len(I)) if x not in bad]
        if ok and len(ok)==2**(len(I)-1) and len({sum(x)%2 for x in ok})==1:
            rows.append((sum(1<<i for i in I),sum(ok[0])%2))
        else:res.extend(cs)
    return rows,res


def affine(rows,n):
    B={}
    for v,b in rows:
        while v:
            i=v.bit_length()-1
            if i not in B:B[i]=(v,b);break
            w,c=B[i];v^=w;b^=c
        else:
            if b:return None
    free=[i for i in range(n) if i not in B]
    def lift(z):
        x=sum(b<<i for i,b in zip(free,z))
        for i,(v,b) in sorted(B.items()):
            if (v&x).bit_count()%2!=b:x|=1<<i
        return tuple((x>>i)&1 for i in range(n))
    return free,lift


def solve(F,n,cap):
    rows,res=extract(F);a=affine(rows,n)
    if a is None:return 'unsat',None
    free,lift=a
    if len(free)>cap:return 'unknown',None
    for z in product((0,1),repeat=len(free)):
        x=lift(z)
        if accepts(res,x):assert accepts(F,x);return 'sat',x
    return 'unsat',None


def cyclic(n,x):
    I=[tuple(sorted((i,(i+1)%n,(i+3)%n))) for i in range(n)]
    assert all(len(set(a)&set(b))<=1 for i,a in enumerate(I) for b in I[i+1:])
    return [c for J in I for c in parity_clauses(J,sum(x[i] for i in J)%2)]


def main():
    rng=Random(680);countchecks=liftchecks=solvechecks=0
    for n in range(1,7):
        for _ in range(30):
            F=[tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(4))) for j in range(rng.randrange(6))]
            if n>=3 and rng.randrange(2):
                I=tuple(rng.sample(range(n),3));F+=parity_clauses(I,rng.randrange(2))
            ref=[x for x in product((0,1),repeat=n) if accepts(F,x)]
            M,t=selector_count(F,n);assert M==len(ref);countchecks+=1
            rows,res=extract(F);a=affine(rows,n)
            if a is None:assert not ref
            else:
                free,lift=a;xs=[lift(z) for z in product((0,1),repeat=len(free))]
                assert len(xs)==len(set(xs));assert sorted(x for x in xs if accepts(res,x))==ref
                liftchecks+=len(xs)
            status,x=solve(F,n,n);assert (status=='sat')==bool(ref);assert status!='unknown';solvechecks+=1
    controls=[]
    for n in (8,16,32,64):
        x=tuple(rng.randrange(2) for _ in range(n));F=cyclic(n,x);D=domains(F)
        assert all(len(d)==3 for d in D);assert ac(D)==D
        rows,res=extract(F);assert len(rows)==n and not res
        a=affine(rows,n);assert a is not None and not a[0];assert a[1](())==x
        assert solve(F,n,0)==('sat',x)
        controls.append((n,len(F),sum(map(len,D)),n))
    # Singularity at n=7: rank 4; a contradictory charge has no solution.
    F=cyclic(7,(0,)*7);rows,_=extract(F);a=affine(rows,7);assert len(a[0])==3
    for i in range(7):
        G=F[:4*i]+parity_clauses(tuple(sorted((i,(i+1)%7,(i+3)%7))),1)+F[4*i+4:]
        assert ac(domains(G))==domains(G);assert solve(G,7,0)==('unsat',None)
    print(dict(selector_count_fixtures=countchecks,affine_lift_checks=liftchecks,decision_fixtures=solvechecks,unique_controls=controls,inconsistent_arc_consistent_controls=7))

if __name__=='__main__':main()
