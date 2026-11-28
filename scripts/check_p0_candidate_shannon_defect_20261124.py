"""G99–G104 exact finite regressions; not a universal machine compiler."""
from itertools import product, combinations
from random import Random
from sympy import symbols
rng=Random(369)
def truth(F,x):return all(any(x[i]==v for i,v in c) for c in F)
def maj(a,b,c):return tuple(int(x+y+z>=2) for x,y,z in zip(a,b,c))
def build(F,n,r):
    m=n+3*r;s=m;C=[((s,1),(i,0)) for i in range(m)]
    Cs=list(F)+[tuple((n+3*j+i,1) for i in range(3)) for j in range(r)]
    for j,c in enumerate(Cs):
        if not c:C.extend([((s,0),),((m+1+j,0),)]);continue
        a,b,d=c+(c[-1],)*(3-len(c))
        y=m+1+j
        C += [((y,0),(s,1)),((y,0),(a[0],1-a[1])),((s,0),a,(y,1)),((y,0),b,d)]
    return C,Cs,m,s
def ext(x,z,s,Cs):
    v=x+z+(s,)
    return v+tuple(int(s and c and v[c[0][0]]!=c[0][1]) if c else 0 for c in Cs)
count=0;defects=0;weighted=0;extension_checks=0
for n in range(1,5):
    for trial in range(30):
        F=[tuple((i,rng.randrange(2)) for i in rng.sample(range(n),rng.randrange(min(3,n)+1))) for _ in range(rng.randrange(6))]
        r=1+trial%2;C,Cs,m,s=build(F,n,r);A=[];orig=[]
        for x in product((0,1),repeat=n):
            if truth(F,x):orig.append(x)
            for z in product((0,1),repeat=3*r):
                for b in (0,1):
                    v=ext(x,z,b,Cs);expected=(not any(x+z)) if b==0 else truth(F,x) and all(any(z[3*j:3*j+3]) for j in range(r))
                    assert truth(C,v)==expected
                    count+=1
                    if expected:A.append(v)
                    if trial<3:
                        extensions=sum(truth(C,x+z+(b,)+ys) for ys in product((0,1),repeat=len(Cs)))
                        assert extensions==int(expected);extension_checks+=1
        assert len(A)==1+len(orig)*7**r
        if orig:
            for j in range(r):
                T=[]
                for k in range(3):
                    z=tuple(int(i==3*j+k or (i//3!=j and i%3==0)) for i in range(3*r))
                    T.append(ext(orig[0],z,1,Cs))
                assert all(truth(C,v) for v in T) and not truth(C,maj(*T))
                D={i for i,t in enumerate(zip(*T)) if len(set(t))>1}
                assert D <= set(range(n+3*j,n+3*j+3))|{m+1+len(F)+j}
                defects+=1
        else:assert len(A)==1
        w=[(rng.randrange(-2,3),rng.randrange(-2,3)) for _ in range(m+1)]
        def weight(v,ws):
            p=1
            for b,(a,c) in zip(v,ws):p*=(a,c)[b]
            return p
        direct=sum(weight(v,w) for v in A)
        base=weight((0,)*(m+1),w)
        origz=sum(weight(x,w[:n]) for x in orig)
        blocks=1
        for j in range(r):
            ws=w[n+3*j:n+3*j+3];blocks*=sum(weight(v,ws) for v in product((0,1),repeat=3) if any(v))
        assert direct==base+w[s][1]*origz*blocks;weighted+=1
print('switch',count,'unique extension brute force',extension_checks,'defects',defects,'weighted',weighted)
n=2;cl=[tuple((i,v) for i,v in zip(I,vs)) for k in (1,2) for I in combinations(range(n),k) for vs in product((0,1),repeat=k)]
pins=[p for k in range(n+1) for p in product((0,1),repeat=k)]
Flist=[[c for i,c in enumerate(cl) if mask>>i&1] for mask in range(1<<len(cl))]
T={(m,p):int(any(truth(F,p+x) for x in product((0,1),repeat=n-len(p)))) for m,F in enumerate(Flist) for p in pins}
checks=0;paths=0
for trial in range(101):
    A={k:v^int(trial>0 and rng.random()<0.02) for k,v in T.items()}
    def delta(m,p):
        b=(A[m,p+(0,)]|A[m,p+(1,)]) if len(p)<n else int(truth(Flist[m],p))
        return A[m,p]-b
    D={k for k in A if delta(*k)};E={k for k in A if A[k]!=T[k]}
    assert bool(D)==bool(E)
    for m,p in E:
        while not delta(m,p):
            assert len(p)<n
            p=next(p+(b,) for b in (0,1) if A[m,p+(b,)]!=T[m,p+(b,)])
        paths+=1
    checks+=len(A)
print('candidate local checks',checks,'error descent paths',paths,'candidates',101)
u,v,w=symbols('u v w');d=u-(v+w-v*w)
for a,b,c in product((0,1),repeat=3):
    q=int(d.subs({u:a,v:b,w:c}));assert q==a-(b|c);assert q*q==int(q!=0)
print('SymPy signed defect table 8/8')
S=set(range(1,8));c=0
for mask in range(128):
    A={x for x in S if mask>>(x-1)&1};c+=all(((a&b)|(a&d)|(b&d)) in A for a,b,d in combinations(A,3))
print('G94 majority closed count',c)
C=[(-2,4),(-3,4),(2,3,-4),(-1,-4,-5),(1,4,-5),(1,-4,5),(-1,4,5),(5,)]
for u,v,w in product((0,1),repeat=3):
    a=[]
    for x,y in product((0,1),repeat=2):
        vals=(u,v,w,x,y)
        if all(any(vals[abs(i)-1]==(i>0) for i in c) for c in C):a.append((x,y))
    assert a==([(v|w,1)] if u!=(v|w) else [])
print('Tseitin defect gate 8/8 unique extensions')
