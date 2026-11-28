"""Section71: original dual restrictions, independent dependency syndrome and signed filter."""
from itertools import product
from random import Random


def basis(rows):
    B={}
    for v in rows:
        while v:
            i=v.bit_length()-1
            if i in B:v^=B[i]
            else:B[i]=v;break
    # canonical reduced basis, decreasing pivots
    for i in sorted(B):
        for j in B:
            if j>i and B[j]>>i&1:B[j]^=B[i]
    return tuple(B[i] for i in sorted(B,reverse=True))


def lift(rows):
    B={}
    for v,b in rows:
        while v:
            i=v.bit_length()-1
            if i in B:w,c=B[i];v^=w;b^=c
            else:B[i]=(v,b);break
        else:
            if b:return None
    z=0
    for i,(v,b) in sorted(B.items()):
        if (v&z).bit_count()%2!=b:z|=1<<i
    return z


def value(v,z):return (v&z).bit_count()%2


def good(E,z):return all(not all(value(v,z)==b for v,b in e) for e in E)


def prepare(E):
    groups={}
    for e in E:groups.setdefault(basis(v for v,b in e),[]).append(e)
    blocks=[]
    for B,es in groups.items():
        A=[]
        for p in product((0,1),repeat=len(B)):
            z=lift(zip(B,p));assert z is not None
            if good(es,z):A.append(sum(b<<i for i,b in enumerate(p)))
        blocks.append((B,A))
    return blocks


def decompose(blocks):
    rows=[];owners=[];ranges=[]
    for i,(B,A) in enumerate(blocks):
        ranges.append(tuple(range(len(rows),len(rows)+len(B))))
        rows.extend(B);owners.extend([i]*len(B))
    piv={};rels=[]
    for j,v in enumerate(rows):
        c=1<<j
        while v:
            i=v.bit_length()-1
            if i in piv:w,t=piv[i];v^=w;c^=t
            else:piv[i]=(v,c);break
        else:rels.append(c)
    parent=list(range(len(blocks)))
    def root(i):
        while i!=parent[i]:i=parent[i]
        return i
    for c in rels:
        I=sorted({owners[j] for j in range(len(rows)) if c>>j&1})
        for i in I[1:]:parent[root(i)]=root(I[0])
    comps={}
    for i in range(len(blocks)):comps.setdefault(root(i),[[],[]])[0].append(i)
    for c in rels:
        j=(c&-c).bit_length()-1;comps[root(owners[j])][1].append(c)
    return ranges,list(comps.values()),len(piv)


def choices(blocks,ranges,ids,rels):
    result=[]
    for i in ids:
        C=[sum(((c>>j)&1)<<k for k,j in enumerate(ranges[i])) for c in rels]
        result.append([(p,sum(((p&a).bit_count()%2)<<h for h,a in enumerate(C))) for p in blocks[i][1]])
    return result


def solve(E,d,cap=12,check_fourier=True):
    blocks=prepare(E);ranges,comps,rank=decompose(blocks)
    assert sum(len(B) for B,A in blocks)-rank==sum(len(R) for I,R in comps)
    count=1;rows=[];peak=0;work=0;maxr=0;freqs=0
    for I,R in comps:
        r=len(R);maxr=max(r,maxr)
        if r>cap:raise OverflowError('UNKNOWN: component redundancy cap')
        C=choices(blocks,ranges,I,R);M={0:(1,())}
        for opts in C:
            N={}
            for s,(n,ps) in M.items():
                for p,t in opts:
                    work+=1;u=s^t;old=N.get(u,(0,ps+(p,)));N[u]=(old[0]+n,old[1])
            M=N;peak=max(peak,len(M))
        n,ps=M.get(0,(0,()))
        # Independent signed phase consumer, no original witness enumeration.
        if check_fourier:
            S=0
            for a in range(1<<r):
                f=1
                for opts in C:f*=sum((-1)**value(a,t) for p,t in opts)
                S+=f;freqs+=1
            assert S==(1<<r)*n
        count*=n
        if n:
            for i,p in zip(I,ps):rows.extend((v,p>>j&1) for j,v in enumerate(blocks[i][0]))
    z=lift(rows) if count else None
    assert z is not None and good(E,z) if count else z is None
    return count*(1<<(d-rank)),z,(len(blocks),len(comps),maxr,peak,work,freqs)


def decision(E,d,cap=12):
    blocks=prepare(E);ranges,comps,rank=decompose(blocks);rows=[]
    for I,R in comps:
        if len(R)>cap:raise OverflowError('UNKNOWN')
        M={0:()}
        for opts in choices(blocks,ranges,I,R):
            N={}
            for s,ps in M.items():
                for p,t in opts:N.setdefault(s^t,ps+(p,))
            M=N
        if 0 not in M:return None
        for i,p in zip(I,M[0]):rows.extend((v,p>>j&1) for j,v in enumerate(blocks[i][0]))
    z=lift(rows);assert z is not None and good(E,z);return z


def exclusions(B,allowed):return [list(zip(B,p)) for p in product((0,1),repeat=len(B)) if p not in allowed]


def main():
    rng=Random(71);fixtures=0;frequencies=0;controls=[]
    for d in range(1,9):
        for _ in range(40):
            E=[[(rng.randrange(1<<d),rng.randrange(2)) for _ in range(rng.randrange(1,4))] for _ in range(rng.randrange(0,6))]
            expected=[z for z in range(1<<d) if good(E,z)]
            n,z,stats=solve(E,d,15);w=decision(E,d,15)
            assert n==len(expected) and ((z in expected and w in expected) if n else z is None and w is None)
            fixtures+=1;frequencies+=stats[-1]
    for g in (4,8,16,32):
        d=4*g;V=[((1<<d)-1)^(1<<i) for i in range(d)]
        L=[];R=[]
        for j in range(g):
            a,b,c,e=V[4*j:4*j+4]
            L+=exclusions((a,b,c),{(0,0,0),(0,1,0),(1,0,1)})
            R+=exclusions((a,b,e),{(0,0,0),(1,1,0),(1,1,1)})
        assert len(basis(V))==d
        n,z,stats=solve(L+R,d,2);assert n==1 and z==0 and decision(L+R,d,2)==0
        assert stats[:4]==(2*g,g,2,4)
        controls.append(('interleaved',d,len(L+R),n,stats))
    for g in (4,8,16,32):
        d=3*g;V=[1<<i for i in range(d)];E=[]
        for j in range(g):E.append([(v,0) for v in V[3*j:3*j+3]])
        G=tuple(sum(V[k] for k in range(i,d,3)) for i in range(3))
        E+=exclusions(G,{(0,0,0)})
        n,z,stats=solve(E,d,3);assert n==(7**g+7*(-1)**g)//8 and decision(E,d,3) is not None
        assert stats[:3]==(g+1,1,3);controls.append(('global',d,len(E),n,stats))
    print(dict(fixtures=fixtures,random_fourier_frequencies=frequencies,controls=controls))

if __name__=='__main__':main()
