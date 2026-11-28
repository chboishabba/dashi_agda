"""Section 81: actual bounded ideal -> affine descent -> parity CNF -> closure."""
from collections import defaultdict
from random import Random
import check_p0_intrinsic_hull_20261125 as A
import check_p0_singleton_sign_ideal_20261125 as I
import check_p0_gauge_discovery_20261125 as G
from check_p0_signed_horn_closure_20261125 import canonical,repair,sat,original7


def patches(F,n,cap=7):
    # Dense scope heuristic, not a decomposition promise. Every selected patch
    # has only original clauses; all cross-patch clauses remain in the source.
    scopes=defaultdict(set)
    for c in F:scopes[tuple(sorted(map(abs,c)))].add(c)
    parent=list(range(n))
    def root(i):
        while parent[i]!=i:parent[i]=parent[parent[i]];i=parent[i]
        return i
    for V,cs in scopes.items():
        if len(V)==3 and len(cs)>=4:
            for j in V[1:]:parent[root(j-1)]=root(V[0]-1)
    groups=defaultdict(list)
    for j in range(n):groups[root(j)].append(j+1)
    P={tuple(V) for V in groups.values() if len(V)<=cap}
    P.update(V for V in scopes if V and len(V)<=cap)
    if n<=cap:P.add(tuple(range(1,n+1)))
    return sorted(P)


def ideal_chart(F,n):
    rows=[];P=patches(F,n)
    for V in P:
        loc={j:i+1 for i,j in enumerate(V)}
        H=[tuple(loc[abs(l)]*(1 if l>0 else -1) for l in c) for c in F if all(abs(l) in loc for l in c)]
        R=I.coordinate_image(H,len(V),min(4,len(V)))
        if R is None:return None,len(P)
        a,K=R
        _,orth=A.chart([(v,0) for v in K],len(V))
        for w in orth:
            rows.append((sum(1<<(j-1) for i,j in enumerate(V) if w>>i&1),A.dot(w,a)))
    return A.chart(rows,n),len(P)


def compile_parity(k,R):
    F=[];gates=[];cache={};n=k
    def label(v):
        nonlocal n
        if v in cache:return cache[v]
        bits=[i+1 for i in range(k) if v>>i&1]
        if not bits:
            n+=1;F.append((-n,));gates.append((n,0,0));u=n
        else:
            u=bits[0]
            for b in bits[1:]:
                n+=1;w=n
                F.extend([(u,b,-w),(u,-b,w),(-u,b,w),(-u,-b,-w)])
                gates.append((w,u,b));u=w
        cache[v]=u;return u
    for B,S in R:
        L=[label(v) for v in B]
        for p in range(1<<len(B)):
            if p not in S:F.append(tuple(-l if p>>i&1 else l for i,l in enumerate(L)))
    def lift(p):
        for w,u,v in gates:
            b=0 if u==0 else ((p>>(u-1))^(p>>(v-1)))&1
            p|=b<<(w-1)
        return p
    return n,canonical(F),lift


def normalize(F,n):
    F=canonical(F);C,count=ideal_chart(F,n)
    if C is None:return None
    a,K=C
    D=A.descend(A.project(A.cnf(F),a,K),len(K))
    if D is None:return None
    k,f,R,reopen,*_=D
    def back(p,t=0):return a^A.lin(K,reopen(p,t))
    # Affine composite, with independent columns for active and invisible bits.
    b=back(0);B=tuple(back(1<<i)^b for i in range(k));T=tuple(back(0,1<<i)^b for i in range(f))
    assert len(A.basis(B+T))==k+f
    def forward(x):
        S=A.chart([(A.observe(B+T,1<<i),((x^b)>>i)&1) for i in range(n)],k+f)
        if S is None:return None
        q,H=S;assert not H
        return q&((1<<k)-1),q>>k
    return k,f,R,back,forward,len(K),count


def solve(F,n,cap=8):
    N=normalize(F,n)
    if N is None:return 'UNSAT',None,None
    k,f,R,back,forward,d,patchcount=N
    m,C,lift=compile_parity(k,R);a,q=G.greedy(C,m)
    stats=(d,k,f,m,q,patchcount)
    if q>cap:return 'UNKNOWN',None,stats
    x,c=repair(C,m,a,q)
    if x is None:return 'UNSAT',None,stats
    p=x&((1<<k)-1);assert x==lift(p)
    y=back(p);assert sat(F,y) and forward(y)==(p,0)
    return 'SAT',y,stats


def main():
    rng=Random(81);fixtures=lifts=auxchecks=returns=unknown=0
    for n in range(1,8):
        for _ in range(25):
            F=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(1,4))) for _ in range(rng.randrange(11))]
            S={x for x in range(1<<n) if sat(F,x)};N=normalize(F,n)
            if N is None:assert not S
            else:
                k,f,R,back,forward,d,pc=N;m,C,lift=compile_parity(k,R);V=[];expected=set()
                for p in range(1<<k):
                    y=lift(p);assert sat(C,y)==A.accepted(R,p)
                    if not sat(C,y):continue
                    expected.add(y)
                    for t in range(1<<f):
                        x=back(p,t);assert forward(x)==(p,t);V.append(x);lifts+=1
                assert set(V)==S and len(V)==len(S)
                if m<=12:
                    assert {y for y in range(1<<m) if sat(C,y)}==expected;auxchecks+=1
            status,x,stats=solve(F,n)
            if status=='SAT':assert x in S;returns+=1
            elif status=='UNSAT':assert not S
            else:unknown+=1
            fixtures+=1
    print(dict(fixtures=fixtures,original_lifts=lifts,exhaustive_compiled_fibres=auxchecks,verified_returns=returns,unknown=unknown))
    # Test dense parity observations independently of the normalization choices.
    for k in range(2,6):
        for _ in range(12):
            R=[(tuple(rng.randrange(1<<k) for _ in range(3)),{0,2,5,7})]
            m,C,lift=compile_parity(k,R)
            E={lift(p) for p in range(1<<k) if A.accepted(R,p)}
            assert all(sat(C,lift(p))==A.accepted(R,p) for p in range(1<<k))
            if m<=15:assert {x for x in range(1<<m) if sat(C,x)}==E
    print('dense parity controls',48)
    for g in (4,8,16,32):
        n=7*g;ts=[rng.randrange(128) for _ in range(g)]
        F=[c for i,t in enumerate(ts) for c in original7(t,7*i)]
        target=sum(t<<(7*i) for i,t in enumerate(ts))
        # Ternary bridges make the old full ternary component too large.
        for i in range(g-1):
            V=(7*i+1,7*i+2,7*(i+1)+1)
            F.append(tuple(j if target>>(j-1)&1 else -j for j in V))
        assert G.local_pins(F,n)==[]
        status,x,stats=solve(F,n);assert status=='SAT' and x==target and stats[:5]==(0,0,0,0,0)
        print('connected nonlinear',n,stats)
    # Exact affine correlation, then a residual nonlinear constraint; not merely pins.
    F=[(-1,-2,-3),(-1,2,3),(1,-2,3),(1,2,-3),(3,4)]
    N=normalize(F,4);assert N is not None and N[5]==3
    status,x,stats=solve(F,4);assert status=='SAT' and sat(F,x)
    print('affine correlation control',stats)


if __name__=='__main__':main()
