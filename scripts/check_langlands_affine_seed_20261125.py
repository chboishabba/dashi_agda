from collections import Counter
from itertools import product
from random import Random
from sympy import Matrix

# All row operations carried out modulo 3, with the full left chart retained.
def rref(A,d):
    a=[list(row) for row in A]; m=len(a); E=[[int(i==j) for j in range(m)] for i in range(m)]; piv=[]
    for c in range(d):
        i=next((i for i in range(len(piv),m) if a[i][c]%3),None)
        if i is None:continue
        j=len(piv); a[i],a[j]=a[j],a[i];E[i],E[j]=E[j],E[i]
        v=pow(a[j][c],-1,3);a[j]=[v*x%3 for x in a[j]];E[j]=[v*x%3 for x in E[j]]
        for i in range(m):
            if i==j:continue
            v=a[i][c];a[i]=[(x-v*y)%3 for x,y in zip(a[i],a[j])];E[i]=[(x-v*y)%3 for x,y in zip(E[i],E[j])]
        piv.append(c)
    return a,E,piv

def dot(a,b):return sum(x*y for x,y in zip(a,b))%3
def mv(A,x):return tuple(dot(row,x) for row in A)
def add(a,b):return tuple((x+y)%3 for x,y in zip(a,b))
def neg(a):return tuple(-x%3 for x in a)
def columns(A,n):return [tuple(row[i] for row in A) for i in range(n)]
def project(Q,A,n):return [mv(Q,c) for c in columns(A,n)]
def seedsolve(R,E,piv,rhs,d,free=None):
    z=mv(E,rhs); r=len(piv)
    if any(z[r:]):return None
    f=[i for i in range(d) if i not in piv];s=[0]*d
    for i,v in zip(f,free or [0]*len(f)):s[i]=v
    for i,c in enumerate(piv):s[c]=(z[i]-sum(R[i][j]*s[j] for j in f))%3
    return tuple(s)

# Source-only joint old/new residual antichain DP, as in R201. Each state
# retains an affine syndrome, tag, length and original witness.
def norm(C):
    S={frozenset(c) for c in C if not any(-l in c for l in c)}
    if frozenset() in S:return None
    return tuple(sorted(tuple(sorted(c)) for c in S if not any(b<c for b in S)))
def step(C,i,v):
    if C is None:return None
    lit=(i+1)*(1 if v else -1)
    return norm([tuple(l for l in c if l!=-lit) for c in C if lit not in c])
def hist(n,old,new,cols,w,offset,mod=None):
    D={(norm(old),norm(new),offset,0,0):(1,())}; rows=0
    for i in range(n):
        T={}
        for (o,p,z,t,k),(count,x) in D.items():
            for v in (0,1):
                a,b=step(o,i,v),step(p,i,v);rows+=1
                if a is None and b is None:continue
                key=(a,b,add(z,cols[i]) if v else z,(t+w[i]*v)%3,v if i==0 else k)
                nc,wx=T.get(key,(0,x+(v,)));T[key]=((nc+count) if mod is None else (nc+count)%mod,wx)
        D=T
    out={}
    for (o,p,z,t,k),(count,x) in D.items():
        assert o in (None,()) and p in (None,())
        key=(z,t,k+1,int(o==())+2*int(p==()))
        nc,wx=out.get(key,(0,x));out[key]=((nc+count) if mod is None else (nc+count)%mod,wx)
    return out,rows

def sat(C,x):return all(any(x[abs(l)-1]==int(l>0) for l in c) for c in C)
def st(C,D,x):return int(sat(C,x))+2*int(sat(D,x))
def packet(C):
    out=Counter()
    for (c,k,l,st),v in C.items():
        m=min(k,l);h=k*l*(k-l)//2;b=m*(m-1)//2-m*(l-1)
        out[st,'rank']+=64*k*l*v;out[st,'cond']+=(112*k*l-4*m)*v
        out[st,'phase']+=c*(28*k*l-m)*v;out[st,'sign']+=(k*l-m)*v;out[st,'power']+=(112*h-4*b)*v
        for j in range(m):out[st,'L',c,j-l+1]+=v
    return out

def match(H,J,factor,mod=None):
    by={}
    for key,v in J.items():by.setdefault(key[0],[]).append((key,v))
    out=Counter();back={};joins=0
    for (z,t,k,a),(n,x) in H.items():
        for (_,u,l,b),(m,y) in by.get(neg(z),[]):
            joins+=1
            old=bool(a&1 and b&1);new=bool(a&2 and b&2);st=int(old)+2*int(new)
            if not st:continue
            key=((t-u)%3,k,l,st);out[key]+=factor*n*m
            if mod is not None:out[key]%=mod
            back.setdefault(key,(x,y))
    return out,back,joins

rng=Random(283); checks=Counter(); work=Counter()
for n in range(1,6):
  for trial in range(12):
    d=1+trial%4; a=1+trial%3;b=1+(trial//2)%3
    def mat(r,c):return [[rng.randrange(3) for j in range(c)] for i in range(r)]
    def cnf():return [tuple((i+1)*rng.choice([-1,1]) for i in rng.sample(range(n),rng.randrange(1,min(n,3)+1))) for _ in range(rng.randrange(5))]
    A,C=mat(a,d),mat(b,d); B,D=mat(a,n),mat(b,n)
    u=tuple(rng.randrange(3) for _ in range(a));v=tuple(rng.randrange(3) for _ in range(b))
    pins={i:rng.randrange(3) for i in range(d) if rng.randrange(4)==0}
    M=A+C+[[int(i==j) for j in range(d)] for i in pins]; p=tuple(pins.values());R,E,piv=rref(M,d);Q=E[len(piv):];mult=3**(d-len(piv))
    assert all(not any(mv([row],c)) for row in Q for c in columns(M,d));checks['left_kernel']+=1
    z0=(0,)*len(Q);off=mv(Q,u+v+p)
    U=project(Q,B+[[0]*n for _ in range(b+len(p))],n);V=project(Q,[[0]*n for _ in range(a)]+D+[[0]*n for _ in p],n)
    w=[rng.randrange(3) for _ in range(n)];w2=[rng.randrange(3) for _ in range(n)]
    F,F2,G,G2=cnf(),cnf(),cnf(),cnf()
    H,h=hist(n,F,F2,U,w,off);J,j=hist(n,G,G2,V,w2,z0);work['dp_transitions']+=h+j
    out,back,jc=match(H,J,mult);work['matched_packets']+=jc
    ref=Counter();diag=Counter();allx=list(product(range(2),repeat=n));seeds=list(product(range(3),repeat=d))
    def rhs(x,y):return add(mv(B,x),u)+add(mv(D,y),v)+p
    for x,y in product(allx,repeat=2):
        sa,sb=st(F,F2,x),st(G,G2,y);st0=int(bool(sa&1 and sb&1))+2*int(bool(sa&2 and sb&2))
        if not st0:continue
        r=rhs(x,y);good=[s for s in seeds if mv(M,s)==r]
        assert len(good)==(0 if any(mv(Q,r)) else mult);checks['affine_fibres']+=1
        if good:
            k=((dot(w,x)-dot(w2,y))%3,x[0]+1,y[0]+1,st0);ref[k]+=len(good)
            if x==y:diag[k]+=len(good)
    assert out==ref;checks['paired_histograms']+=1
    # True original diagonal: same original x, not equal tag or equal syndrome.
    # Build all four source acceptance masks as a joint antichain state.
    D0={(norm(F),norm(F2),norm(G),norm(G2),off,0,0):(1,())}
    for i in range(n):
        D1={}
        for key,(count,x) in D0.items():
            for bit in (0,1):
                cs=tuple(step(c,i,bit) for c in key[:4]);work['diagonal_transitions']+=1
                if (cs[0] is None or cs[2] is None) and (cs[1] is None or cs[3] is None):continue
                z=add(key[4],add(U[i],V[i])) if bit else key[4]
                k=cs+(z,(key[5]+(w[i]-w2[i])*bit)%3,bit if i==0 else key[6]);nn,wx=D1.get(k,(0,x+(bit,)));D1[k]=(nn+count,wx)
        D0=D1
    dd=Counter()
    for (f0,f1,g0,g1,z,t,k),(count,x) in D0.items():
        st0=int(f0==() and g0==())+2*int(f1==() and g1==())
        if not any(z) and st0:dd[t,k+1,k+1,st0]+=mult*count
    assert dd==diag;checks['original_diagonal']+=1
    for key,(x,y) in back.items():
        rr=rhs(x,y);free=[i for i in range(d) if i not in piv]
        for f in product(range(3),repeat=len(free)):
            s=seedsolve(R,E,piv,rr,d,f);assert s is not None and mv(M,s)==rr and tuple(s[i] for i in free)==f;checks['reopened_seed_coordinates']+=1
        assert st(F,F2,x) and st(G,G2,y)
        assert key[:3]==((dot(w,x)-dot(w2,y))%3,x[0]+1,y[0]+1)
        checks['original_pair_witnesses']+=1
    # Paired revisions: old=loss+common, new=gain+common, signed gain-loss.
    P=packet(out);old=Counter({k[1:]:v for k,v in P.items() if k[0]==1});new=Counter({k[1:]:v for k,v in P.items() if k[0]==2});common=Counter({k[1:]:v for k,v in P.items() if k[0]==3})
    # aggregate collisions across loss/common using explicit sum rather than dict overwrite
    aa=Counter();bb=Counter()
    for (c,k,l,t),v in out.items():
        if t&1:aa[c,k,l,1]+=v
        if t&2:bb[c,k,l,2]+=v
    ap={k[1:]:v for k,v in packet(aa).items()};bp={k[1:]:v for k,v in packet(bb).items()}
    for k in set(ap)|set(bp)|set(old)|set(new)|set(common):
        assert ap.get(k,0)==old[k]+common[k] and bp.get(k,0)==new[k]+common[k]
        assert bp.get(k,0)-ap.get(k,0)==new[k]-old[k];checks['revision_ledger']+=1
    # Reverse-demand precision: no full integer evaluation in these runs.
    # 3-adic factor known at source; modulus 1 retains occupancy only.
    for prime in (2,3):
        for h in range(1,5):
            exponent=d-len(piv) if prime==3 else 0
            need=prime**max(0,h-exponent);mod=prime**h
            HH,_=hist(n,F,F2,U,w,off,need);JJ,_=hist(n,G,G2,V,w2,z0,need)
            low,lb,_=match(HH,JJ,mult,mod)
            assert set(low)==set(out)==set(lb)
            assert all(low[key]==out[key]%mod for key in out)
            checks['precision_and_support']+=1
            if need==1:checks['occupancy_only']+=1
    checks['fixtures']+=1;work['raw_candidate_pairs']+=3**d*4**n
# Exact F81 quadratic Gauss sum, with both nonzero F3 orientations.
F=list(product(range(3),repeat=4));one=(1,0,0,0);zero=(0,0,0,0)
def fm(a,b):
    c=[0]*7
    for i,j in product(range(4),repeat=2):c[i+j]+=a[i]*b[j]
    for i in range(6,3,-1):c[i-3]-=c[i];c[i-4]-=2*c[i]
    return tuple(x%3 for x in c[:4])
def fp(a,n):
    b=one
    while n:
        if n%2:b=fm(b,a)
        a=fm(a,a);n//=2
    return b
def tr(a):return tuple(sum(fp(a,3**i)[j] for i in range(4))%3 for j in range(4))
assert all(fp(a,81)==a for a in F)
for sign in (1,2):
    G=Counter()
    for a in F[1:]:
        v=tr(a);assert not any(v[1:]);q=fp(a,40);assert q in (one,(2,0,0,0))
        G[sign*v[0]%3]+=1 if q==one else -1
    assert G[0]-G[2]==-9 and G[1]-G[2]==0
    checks['quadratic_gauss']+=1
assert fp((2,0,0,0),40)==one
# beta = 3(1+2*pi)/pi^5 = (1+2*pi)/(zeta*pi^3)*(-1),
# so pi^3 beta has nonzero residue -1 (since pi^2=-3*zeta).
# Both signs have quadratic residue character +1 in F81.
# Full forward AND dual factor collision, no source identification.
K=list(product(range(1,5),repeat=2))
def features(k,l):
    m=min(k,l);h=k*l*(k-l)//2;b=m*(m-1)//2-m*(l-1)
    return [int(j in range(1-l,1-l+m)) for j in range(-3,1)]+[int(j in range(1-k,1-k+m)) for j in range(-3,1)]+[k*l,m,k*l-m,112*h-4*b]
A=Matrix([features(k,l) for k,l in K]).T
v=A.nullspace()[0]; from sympy import ilcm
v=v*ilcm(*[x.q for x in v]);assert A*v==Matrix.zeros(A.rows,1)
pos={K[i]:int(x) for i,x in enumerate(v) if x>0};negv={K[i]:-int(x) for i,x in enumerate(v) if x<0}
assert pos and negv
print('collision',pos,negv,'feature rank',A.rank())
print(dict(checks),dict(work))
