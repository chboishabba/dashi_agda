"""Section 69: signed overlap forest on actual Boolean affine fibres."""
from itertools import product, combinations
from fractions import Fraction as Q
from random import Random


def rank(rows):
    B={}
    for v,b in rows:
        while v:
            i=v.bit_length()-1
            if i not in B:B[i]=(v,b);break
            w,c=B[i];v^=w;b^=c
        else:
            if b:return None
    return len(B)


def mass(rows,pins):
    r=rank(pins);s=rank(pins+rows)
    assert r is not None
    return Q(0) if s is None else Q(1,2**(s-r))


def forest(events,pins):
    m=len(events);parent=list(range(m));edges=[]
    def root(i):
        while i!=parent[i]:i=parent[i]
        return i
    pairs=sorted(((mass(events[i]+events[j],pins),i,j) for i,j in combinations(range(m),2)),reverse=True)
    for w,i,j in pairs:
        a,b=root(i),root(j)
        if w and a!=b:parent[a]=b;edges.append((i,j))
    return edges


def score(events,edges,pins):
    return 1-sum(mass(e,pins) for e in events)+sum(mass(events[i]+events[j],pins) for i,j in edges)


def hit(rows,z):return all((v&z).bit_count()%2==b for v,b in rows)


def point(events,edges,z):
    h=[hit(e,z) for e in events]
    return 1-sum(h)+sum(h[i] and h[j] for i,j in edges)


def decode(d,events):
    pins=[];edges=forest(events,pins);v=score(events,edges,pins)
    if v<=0:return None,v
    start=v;z=0
    for i in range(d):
        a,b=[score(events,edges,pins+[(1<<i,j)]) for j in (0,1)]
        assert a+b==2*v
        j=int(b>a);v=max(a,b);pins.append((1<<i,j));z|=j<<i
    assert v==1 and not any(hit(e,z) for e in events)
    return z,start


def main():
    rng=Random(690);points=averages=positive=improved=0
    for d in range(1,7):
        for _ in range(30):
            E=[[(rng.randrange(1<<d),rng.randrange(2)) for _ in range(rng.randrange(1,4))] for _ in range(rng.randrange(1,9))]
            T=forest(E,[]);s=score(E,T,[]);union=1-sum(mass(e,[]) for e in E)
            vals=[]
            for z in range(1<<d):
                f=point(E,T,z);assert f<=int(not any(hit(e,z) for e in E));vals.append(f);points+=1
            assert s==Q(sum(vals),1<<d) and s>=union;averages+=1
            z,v=decode(d,E);assert v==s
            if z is not None:positive+=1;assert not any(hit(e,z) for e in E)
            improved+=s>0 and union<=0
    # Actual original affine bundle: a=u XOR v, b=w XOR q.
    # Residual clauses (a OR b OR x_i), 12 independent x_i.
    # Repeat each event using original distinct parity-linked copies of x_i.
    controls=[]
    for copies in (1,2,4,8):
        d=16;E=[[(3,0),(12,0),(1<<(4+i),0)] for i in range(12) for _ in range(copies)]
        z,v=decode(d,E);assert z is not None and v==Q(3,16)
        assert 1-sum(mass(e,[]) for e in E)==1-Q(12*copies,8)
        u,w=[(z>>i)&1 for i in (0,2)];a=(z&3).bit_count()%2;b=(z&12).bit_count()%2
        assert all(a or b or ((z>>(4+i))&1) for i in range(12))
        controls.append((copies,len(E),str(v)))
    # Singleton with independent unit constraints: this bound stalls at d>=3.
    E=[[(1<<i,0)] for i in range(4)];z,v=decode(4,E);assert z is None and v<=0
    print(dict(pointwise=points,average=averages,positive=positive,improved=improved,controls=controls,singleton_bound=str(v)))

if __name__=='__main__':main()
