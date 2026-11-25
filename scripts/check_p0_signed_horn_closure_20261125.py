"""Section 79: signed Horn closure repair on the original CNF."""
from random import Random


def sat(F,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in F)


def canonical(F):
    return [tuple(sorted(set(c))) for c in F if not any(-l in c for l in c)]


def gauge(F,a):
    return [tuple(-l if a>>(abs(l)-1)&1 else l for l in c) for c in F]


def compile_core(F,n,a):
    H=[];R=[];edges=[set() for _ in range(n)]
    for c in canonical(gauge(F,a)):
        P=tuple(l-1 for l in c if l>0);N=sum(1<<(-l-1) for l in c if l<0)
        if len(P)<=1:
            h=0 if not P else 1<<P[0];H.append((N,h))
            if N.bit_count()==1 and h:edges[N.bit_length()-1].add(P[0])
        else:R.append((N,P))
    # Mutual reachability of unary Horn implications, computed only for analysis.
    reach=[]
    for i in range(n):
        seen={i};todo=[i]
        while todo:
            for j in edges[todo.pop()]-seen:seen.add(j);todo.append(j)
        reach.append(seen)
    classes=[min(j for j in reach[i] if i in reach[j]) for i in range(n)]
    return H,R,classes


def close(H,x):
    while True:
        y=x
        for N,h in H:
            if N&x==N:
                if not h:return None
                y|=h
        if y==x:return x
        x=y


def repair(F,n,a,r):
    H,R,classes=compile_core(F,n,a);calls=0
    def walk(p,left):
        nonlocal calls
        calls+=1;x=close(H,p)
        if x is None:return None
        for N,P in R:
            if N&x==N and not any(x>>j&1 for j in P):
                if left==0:return None
                for j in P:
                    y=walk(x|(1<<j),left-1)
                    if y is not None:return y
                return None
        return x
    y=walk(0,r)
    if y is not None:
        y^=a;assert sat(F,y)
    return y,calls


def component_distance(x,z,classes):
    return len({classes[j] for j in range(len(classes)) if (x^z)>>j&1})


def original7(t,off):
    S=[[0,4,5,6],[0,1,4,6],[0,4,5,7],[0,4,5,6],[0,4,5,6],[0,1,2,7],[0,3,4,6]]
    F=[tuple(-(j+1) if p>>k&1 else j+1 for k,j in enumerate((i,(i+1)%7,(i+3)%7))) for i,A in enumerate(S) for p in range(8) if p not in A]
    return [tuple((1 if (l>0)^bool(t>>(abs(l)-1)&1) else -1)*(abs(l)+off) for l in c) for c in F]


def main():
    rng=Random(79);checks=complete=solved=0
    for n in range(1,8):
        for _ in range(30):
            F=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(4))) for _ in range(rng.randrange(15))]
            S=[x for x in range(1<<n) if sat(F,x)]
            for a in (0,(1<<n)-1,rng.randrange(1<<n)):
                H,R,C=compile_core(F,n,a);z=close(H,0)
                if z is None:assert not S
                else:
                    assert all(z&(x^a)==z for x in S)
                for r in range(n+1):
                    x,c=repair(F,n,a,r)
                    assert c<=(3**(r+1)-1)//2
                    if x is not None:assert x in S;solved+=1
                    if z is not None and any(component_distance(z,x^a,C)<=r for x in S):
                        assert x is not None;complete+=1
                    if len(R)<=r:assert (x is not None)==bool(S)
                    checks+=1
    print(dict(sources=210,budget_checks=checks,sufficient_radius_checks=complete,verified_returns=solved))
    for t in range(128):
        F=original7(t,0);assert [x for x in range(128) if sat(F,x)]==[t]
        x,c=repair(F,7,0,7);assert x==t
    print('all 128 signed nonlinear singleton translations passed')
    # Nonlinear original block with equality copies of every bit. Gauge zero,
    # no witness supplied to the producer. Each positive root flip propagates.
    for copies in (4,16,64,128):
        n=7*copies;F=original7(127,0)
        for j in range(1,8):
            for k in range(1,copies):
                v=7*k+j;F.extend([(-j,v),(j,-v)])
        H,R,C=compile_core(F,n,0);z=close(H,0);assert z is not None
        target=(1<<n)-1;d=component_distance(z,target,C)
        x,c=repair(F,n,0,d);assert x==target
        print(dict(n=n,raw_hamming=(z^target).bit_count(),scc_distance=d,calls=c,nonhorn=len(R)))
    # All cross-copy equality constraints are essential for singleton uniqueness.
    # A family with r independent non-Horn choices, each unlocking a large SCC.
    for g in (2,4,8):
        m=64;n=g*m;F=[]
        for i in range(g):
            j=i*m+1
            for v in range(j+1,j+m):F.extend([(-j,v),(j,-v)])
        # One binary non-Horn root constraint; Horn clauses create the unique
        # viable choice and transport it through all g components.
        F.append((1,m+1));F.append((-1,-(m+1)))
        F.append((1,-(m+1)))
        for i in range(2,g):F.append((-1,i*m+1))
        x,c=repair(F,n,0,1);assert x is not None and c<=3
        print(dict(chain_n=n,root_budget=1,actual_flips=x.bit_count(),calls=c))


if __name__=='__main__':main()
