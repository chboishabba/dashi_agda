"""Section 80: exact signed gauge producer and original closure consumer."""
from itertools import combinations
from random import Random
from check_p0_signed_horn_closure_20261125 import canonical, gauge, repair, sat, original7


def pairs(F):
    return [(i, p) for i,c in enumerate(F) for p in combinations(c,2)]


def solve2(n, F):
    # Gauge bit is a_i: original positive literal becomes negative iff a_i=1.
    # Thus the gauge constraint for a pair has the original two literal signs.
    G=[[] for _ in range(2*n)]; H=[[] for _ in G]
    def idx(l):return 2*(abs(l)-1)+(l<0)
    for a,b in F:
        u,v=idx(a),idx(b)
        for x,y in ((u^1,v),(v^1,u)):G[x].append(y);H[y].append(x)
    order=[];seen=set()
    for i in range(2*n):
        if i in seen:continue
        seen.add(i);stack=[(i,0)]
        while stack:
            u,j=stack[-1]
            if j==len(G[u]):order.append(u);stack.pop();continue
            v=G[u][j];stack[-1]=(u,j+1)
            if v not in seen:seen.add(v);stack.append((v,0))
    C=[-1]*(2*n);k=0
    for i in reversed(order):
        if C[i]>=0:continue
        C[i]=k;todo=[i]
        while todo:
            for v in H[todo.pop()]:
                if C[v]<0:C[v]=k;todo.append(v)
        k+=1
    if any(C[2*i]==C[2*i+1] for i in range(n)):return None
    a=sum(1<<i for i in range(n) if C[2*i]>C[2*i+1]);assert sat(F,a)
    return a


def defects(F,a):return sum(sum(l>0 for l in c)>1 for c in gauge(F,a))


def discover(F,n,k):
    # Exact small-budget REFERENCE, not the external single-exponential FPT algorithm.
    F=canonical(F);P=pairs(F);m=len(P)
    for q in range(min(k,m)+1):
        for D in combinations(range(m),q):
            D=set(D);a=solve2(n,[p for j,(_,p) in enumerate(P) if j not in D])
            if a is not None:
                assert defects(F,a)<=q
                return a,q
    return None


def greedy(F,n):
    # Polynomial heuristic: retain complete original clause groups if possible.
    P=[];F=canonical(F)
    for c in F:
        Q=P+list(combinations(c,2))
        if solve2(n,Q) is not None:P=Q
    a=solve2(n,P);assert a is not None
    return a,defects(F,a)


def local_pins(F,n,cap=7):
    # Scope components of genuine ternary clauses, NOT full primal components.
    # All original clauses contained in each scope are included, and exact local
    # supports yield sound unary consequences (not the degree-4 ideal engine).
    F=canonical(F);parent=list(range(n))
    def root(i):
        while parent[i]!=i:parent[i]=parent[parent[i]];i=parent[i]
        return i
    for c in F:
        if len(c)==3:
            u=abs(c[0])-1
            for l in c[1:]:parent[root(abs(l)-1)]=root(u)
    groups={}
    for i in range(n):groups.setdefault(root(i),[]).append(i+1)
    out=[]
    for V in groups.values():
        if len(V)>cap:continue
        I={j:i+1 for i,j in enumerate(V)}
        H=[tuple(I[abs(l)]*(1 if l>0 else -1) for l in c) for c in F if all(abs(l) in I for l in c)]
        S=[x for x in range(1<<len(V)) if sat(H,x)]
        if not S:return None
        for i,j in enumerate(V):
            b=S[0]>>i&1
            if all(x>>i&1==b for x in S):out.append(j if b else -j)
    return out


def restrict(F,pins):
    A=set(pins);return canonical([tuple(l for l in c if -l not in A) for c in F if not any(l in A for l in c)])


def pipeline(F,n):
    P=local_pins(F,n)
    if P is None:return None,None,0
    R=restrict(F,P);a,k=greedy(R,n)
    # Unit pins in original coordinates are kept through the actual section79 consumer.
    if k>8:return None,k,0
    x,c=repair(R+[(l,) for l in P],n,a,k)
    if x is not None:assert sat(F,x)
    return x,k,c


def main():
    rng=Random(80);pairs_checked=opt=ball=ret=0
    for n in range(1,7):
        for _ in range(30):
            F=canonical([tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(4))) for _ in range(rng.randrange(7))]);P=pairs(F)
            S=[x for x in range(1<<n) if sat(F,x)]
            costs=[]
            for a in range(1<<n):
                q=sum(not sat([p],a) for _,p in P);k=defects(F,a)
                assert k<=q<=3*k;costs.append(q);pairs_checked+=1
            mn=min(costs);assert (solve2(n,[p for _,p in P]) is not None)==(mn==0)
            if mn<=2:
                a,q=discover(F,n,mn);assert q==mn and defects(F,a)<=mn
                if mn:assert discover(F,n,mn-1) is None
                x,c=repair(F,n,a,mn);assert (x is not None)==bool(S);opt+=1
            pins=local_pins(F,n)
            if pins is None:assert not S
            else:assert all(sat([(l,) for l in pins],x) for x in S)
            a,k=greedy(F,n);x,c=repair(F,n,a,k);assert (x is not None)==bool(S);ball+=1
            x,k,c=pipeline(F,n);assert (x is not None)==bool(S);ret+=x is not None
    print(dict(sources=180,gauge_pair_checks=pairs_checked,minimum_pair_deletion_controls=opt,greedy_closure_controls=ball,pipeline_returns=ret))
    # All four binary clauses on a pair: unavoidable one pair defect and UNSAT.
    F=[(1,2),(1,-2),(-1,2),(-1,-2)];a,q=discover(F,2,1);assert q==1 and repair(F,2,a,q)[0] is None
    # Satisfiable non-renamable-Horn unique source (three pair constraints plus unit).
    F=[(1,2),(1,-2),(-1,2),(-1,-2,3),(3,)]
    # The gauge constraints contain all four binary signs on (1,2).
    a,q=discover(F,3,1);assert q==1 and repair(F,3,a,q)[0]==7
    # Genuine unknown signed gauge on a large binary equality star with a unit.
    for n in (32,128,512):
        target=rng.getrandbits(n);F=[(1,)]+[c for i in range(2,n+1) for c in ((-1,i),(1,-i))]
        F=gauge(F,target^((1<<n)-1));a=solve2(n,[p for _,p in pairs(F)]);assert a is not None and defects(F,a)==0
        x,c=repair(F,n,a,0);assert x==target and c==1
        print('discovered gauge',n,'repair calls',c)
    # Actual signed nonlinear blocks connected through binary links; local scopes
    # discovered without witness, all translated coordinates pinned independently.
    for g in (4,16,32):
        n=7*g;ts=[rng.randrange(128) for _ in range(g)]
        F=[c for i,t in enumerate(ts) for c in original7(t,7*i)]
        target=sum(t<<(7*i) for i,t in enumerate(ts))
        for i in range(g-1):
            j=7*i+1;k=7*(i+1)+1;F.append((j if target>>(j-1)&1 else -j,k if target>>(k-1)&1 else -k))
        P=local_pins(F,n);assert len(P)==n
        x,k,c=pipeline(F,n);assert x==target and k==0 and c==1
        print('nonlinear connected',n,'derived pins',len(P),'repair calls',c)


if __name__=='__main__':main()
