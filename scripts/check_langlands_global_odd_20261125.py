"""Exact global radical-family and odd-conductor stationary-phase controls."""
from collections import Counter
from itertools import product
from math import gcd, lcm
from sympy import Poly, symbols, cyclotomic_poly, factorint
from sympy.polys.numberfields import round_two

X,T=symbols('X T')
units=[a for a in range(15) if gcd(a,15)==1]
assert len(units)==8
Phi=Poly(cyclotomic_poly(15,X),X)
# Affine action on all roots, and primitive-character block in Fourier chart.
def cycles(items,perm):
    todo=set(items); out=[]
    while todo:
        x=min(todo); c=[]; y=x
        while y in todo:
            todo.remove(y);c.append(y);y=perm(y)
        assert y==x;out.append(c)
    return out

def perm_poly(d,a,b):
    p=Poly(1,T)
    for c in cycles(range(d),lambda i:(a*i+b)%d):p*=Poly(1-T**len(c),T)
    return p

def primitive_poly(a,b):
    # Fourier basis f_j=sum_x zeta^(-jx)e_x, maps to zeta^(j*a^-1*b) f_(j*a^-1).
    ai=pow(a,-1,15); p=Poly(1,T,domain='QQ')
    # compute in Q(zeta15)[T], sparse degrees of T, coefficient reduced in X.
    coeff={0:Poly(1,X)}
    for c in cycles(units,lambda j:j*ai%15):
        phase=sum(j*ai*b for j in c)%15;z=Poly(X**phase,X)%Phi
        nxt=dict(coeff)
        for k,v in coeff.items():nxt[k+len(c)]=(nxt.get(k+len(c),Poly(0,X))-v*z)%Phi
        coeff=nxt
    assert all(c.degree()<=0 for c in coeff.values())
    return Poly(sum(c.as_expr()*T**k for k,c in coeff.items()),T)

checks=0; spectra=Counter()
for a,b in product(units,range(15)):
    q,r=(perm_poly(15,a,b)*perm_poly(1,a,b)).div(perm_poly(3,a,b)*perm_poly(5,a,b))
    assert r.is_zero and q==primitive_poly(a,b) and q.degree()==8 and q.nth(8)==1
    spectra[str(q.as_expr())]+=1;checks+=1
# complex conjugation can be chosen as x -> -x in the real radical chart.
assert primitive_poly(14,0)==Poly((1-T*T)**4,T)
# Independent maximal-order discriminants, not polynomial discriminants.
discs={}
for d in (3,5,15):
    _,D=round_two(Poly(X**d-3,X));discs[d]=int(D)
assert discs=={3:-3**5,5:3**4*5**5,15:-3**29*5**15}
assert abs(discs[15]//(discs[3]*discs[5]))==3**20*5**10
# At 5: cubic unit is a cube by Hensel; 3/Teich(3) has valuation exactly one.
assert pow(3,4,25)==6 and pow(2,3,5)==3
# At 3: exponent 2 of uniformizer in 3 gives full Kummer class order 15.
assert gcd(2,15)==1 and pow(3,4,5)==1 and pow(3,2,5)!=1
# Example unramified Euler polynomials from root counts over F_p^f, via cycle type
# on roots of x^15-3 for actual primes, using factor degrees over F_p.
from sympy import factor_list
prime_checks=0
for p in (2,7,11,13,17,19,23,31,37,41,61,71,101):
    def factor_poly(d):
        fs=factor_list(X**d-3,modulus=p)[1];z=Poly(1,T)
        for f,m in fs:z*=Poly((1-T**Poly(f,X).degree())**m,T)
        return z
    q,r=(factor_poly(15)*Poly(1-T,T)).div(factor_poly(3)*factor_poly(5));assert r.is_zero
    assert any(q==primitive_poly(p%15,b) for b in range(15));prime_checks+=1
print('global',checks,'affine Frobenius controls',prime_checks,'prime factor controls',len(spectra),'Euler spectra',discs,flush=True)

# Primitive rank-one characters of Q3 at a=2..5. 2 generates (Z/3^a)^*.
# Exact exponent histogram modulo cyclotomic polynomial, no floating roots.
def gauss_poly(exps,N):
    c=Counter(e%N for e in exps);return Poly(sum(v*X**k for k,v in c.items()),X)%Poly(cyclotomic_poly(N,X),X)
odd=even=0
for a in range(2,6):
    Q=3**a; order=2*3**(a-1); N=lcm(Q,order); logs={pow(2,i,Q):i for i in range(order)};assert len(logs)==order
    m=a//2;j=(a+1)//2; inner=3**m
    for h in (1,2,4,5,7,8):
        if h>=order or h%3==0:continue
        def exponent(u):return (N//Q*u-N//order*h*logs[u%Q])%N
        full=gauss_poly([exponent(u) for u in logs],N)
        active=[];outer=[]
        for v in range(1,3**j):
            if v%3==0:continue
            ex=[exponent(v*(1+3**j*t)%Q) for t in range(inner)]
            p=gauss_poly(ex,N)
            if p.is_zero:continue
            assert p==inner*gauss_poly([exponent(v)],N)
            active.append(v);outer.append(exponent(v))
        assert len(active)==(3 if a%2 else 1)
        assert len({v%3**m for v in active})==1
        assert full==inner*gauss_poly(outer,N) and not full.is_zero
        if a%2:odd+=1
        else:even+=1
print('stationary Gauss exact controls',dict(even=even,odd=odd),flush=True)

# Original-history DAG: reuse the R283 source residual and affine row chart.
from pathlib import Path
from runpy import run_path
from random import Random
A0=run_path(str(Path(__file__).with_name('check_langlands_affine_seed_20261125.py')))
rref,mv,add,project,seedsolve,norm,step,sat=[A0[k] for k in ('rref','mv','add','project','seedsolve','norm','step','sat')]
rng=Random(313); totals=Counter()
for n in range(1,5):
    for trial in range(6):
        d=1+trial%3; m=2+trial%2
        M=[[rng.randrange(3) for _ in range(d)] for _ in range(m)]
        B=[[rng.randrange(3) for _ in range(n)] for _ in range(m)]
        C=[[rng.randrange(3) for _ in range(n)] for _ in range(m)]
        u=tuple(rng.randrange(3) for _ in range(m)); R,E,piv=rref(M,d);Q=E[len(piv):]
        U,V=project(Q,B,n),project(Q,C,n);target=tuple(-a%3 for a in mv(Q,u));free=[i for i in range(d) if i not in piv];mult=3**len(free)
        def cnf():return [tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,min(3,n)+1))) for _ in range(rng.randrange(4))]
        F=[cnf() for _ in range(4)];w=[rng.randrange(3) for _ in range(n)];v=[rng.randrange(3) for _ in range(n)]
        for diag in (False,True):
            ds=((0,0),(1,1)) if diag else tuple(product(range(2),repeat=2))
            initial=(tuple(norm(f) for f in F),(0,)*len(target),0,0,0)
            layers=[{initial}]; edges=[]
            for i in range(n):
                e={}; nxt=set()
                for state in layers[-1]:
                    rs,s,t,k,l=state;row=[]
                    for x,y in ds:
                        rr=tuple(step(r,i,(x,y)[a//2]) for a,r in enumerate(rs))
                        if (rr[0] is None or rr[2] is None) and (rr[1] is None or rr[3] is None):continue
                        ss=add(s,tuple((x*a+y*b)%3 for a,b in zip(U[i],V[i])))
                        q=(rr,ss,(t+w[i]*x-v[i]*y)%3,k+x*(i==0),l+y*(i==0));row.append(((x,y),q));nxt.add(q)
                    e[state]=row;totals['edges']+=len(row)
                edges.append(e);layers.append(nxt)
            labels={}
            for state in layers[-1]:
                rs,s,t,k,l=state;st=int(rs[0]==() and rs[2]==())+2*int(rs[1]==() and rs[3]==())
                if s==target and st:labels[state]=(t,k+1,l+1,st)
            ref={}
            for pairs in product(ds,repeat=n):
                x,y=zip(*pairs);st=int(sat(F[0],x) and sat(F[2],y))+2*int(sat(F[1],x) and sat(F[3],y))
                if not st:continue
                key=(sum(a*b-c*d for a,b,c,d in zip(w,x,v,y))%3,x[0]+1,y[0]+1,st)
                rhs=add(add(mv(B,x),mv(C,y)),u)
                for s in product(range(3),repeat=d):
                    if mv(M,s)==rhs:ref.setdefault(key,set()).add((pairs,s))
            assert set(labels.values())==set(ref)
            for label in ref:
                # Output-conditioned suffix counts, preserving every labelled edge.
                S=[{} for _ in range(n+1)];S[n]={q:mult*int(k==label) for q,k in labels.items()}
                for i in reversed(range(n)):
                    S[i]={q:sum(S[i+1].get(t,0) for _,t in row) for q,row in edges[i].items()}
                assert S[0][initial]==len(ref[label]);seen=set()
                for ordinal in range(S[0][initial]):
                    r=ordinal;q=initial;pairs=[];rank=0
                    for i in range(n):
                        for bit,t in edges[i][q]:
                            count=S[i+1].get(t,0)
                            if r<count:break
                            r-=count;rank+=count
                        else:raise AssertionError('bad ordinal')
                        pairs.append(bit);q=t
                    assert labels[q]==label and r<mult
                    f=tuple((r//3**i)%3 for i in range(len(free)));x,y=zip(*pairs);rhs=add(add(mv(B,x),mv(C,y)),u)
                    s=seedsolve(R,E,piv,rhs,d,f);assert mv(M,s)==rhs
                    assert rank+sum(s[j]*3**i for i,j in enumerate(free))==ordinal
                    seen.add((tuple(pairs),s));totals['ordinal_reopens']+=1
                assert seen==ref[label];totals['history_fibres']+=1
            # Signed consumer: common-mode vector removed, no support collapse.
            coeff=(2,-1,-1);terminal={q:tuple(mult*coeff[(i-k[0])%3] for i in range(3)) for q,k in labels.items()}
            for i in reversed(range(n)):
                terminal={q:tuple(sum(terminal.get(t,(0,0,0))[j] for _,t in row) for j in range(3)) for q,row in edges[i].items()}
            got=terminal[initial];expected=tuple(sum(len(paths)*coeff[(i-k[0])%3] for k,paths in ref.items()) for i in range(3))
            assert got==expected and sum(got)==0;totals['signed_consumers']+=1
            totals['modes']+=1
print('history DAG',dict(totals),flush=True)
