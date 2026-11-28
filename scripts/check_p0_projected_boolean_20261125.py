"""Section 66: exact Toeplitz prefix projection and sufficient bijunctive exit."""
from itertools import product, combinations
from random import Random


def accepts(F,x):
    return all(any(bool(x[abs(l)-1])==(l>0) for l in c) for c in F)


def hashval(n,k,s,x):
    return tuple((sum(s[n-1+i-j]*x[j] for j in range(n))+s[n+k-1+i])%3 for i in range(k))


def reduce(v,B):
    v=tuple(z%3 for z in v)
    for i,u in sorted(B.items()):
        a=v[i];v=tuple((x-a*y)%3 for x,y in zip(v,u))
    return v


def insert(v,B):
    v=reduce(v,B)
    if not any(v):return False
    i=next(i for i,z in enumerate(v) if z);B[i]=tuple(z*v[i]%3 for z in v)
    return True


def low_support_basis(rows,n):
    B={}
    for r in rows:insert(r,B)
    if not any(reduce((0,)*n+(1,),B)):return 'unsat',[]
    C={};out=[]
    for d in (1,2):
        for I in combinations(range(n),d):
            for a in product((1,2),repeat=d-1):
                for rhs in range(3):
                    v=[0]*(n+1);v[I[0]]=1;v[-1]=rhs
                    for i,z in zip(I[1:],a):v[i]=z
                    if not any(reduce(v,B)) and insert(v,C):out.append(tuple(v))
                    if len(C)==len(B):return 'ok',out
    return ('ok',out) if len(C)==len(B) else ('unknown',[])


def row_clauses(rows,n):
    out=[]
    for r in rows:
        I=[i for i in range(n) if r[i]];assert len(I)<=2
        for x in product((0,1),repeat=len(I)):
            if sum(r[i]*z for i,z in zip(I,x))%3!=r[-1]:
                out.append(tuple((i+1)*(-1 if z else 1) for i,z in zip(I,x)))
    return out


def feasible2(F,n):
    adj={i:[] for j in range(1,n+1) for i in (j,-j)}
    for c in F:
        if not c:return False
        a,b=(c[0],c[-1]);adj[-a].append(b);adj[-b].append(a)
    def reaches(a,b):
        seen={a};stack=[a]
        while stack:
            for v in adj[stack.pop()]:
                if v==b:return True
                if v not in seen:seen.add(v);stack.append(v)
        return False
    return not any(reaches(i,-i) and reaches(-i,i) for i in range(1,n+1))


def solve2(F,n):
    F=list(F)
    if not feasible2(F,n):return None
    x=[]
    for i in range(1,n+1):
        z=int(not feasible2(F+[(-i,)],n));x.append(z);F.append((i if z else -i,))
    assert accepts(F,x);return tuple(x)


def projected(F,n,k,p):
    m=n+k-1;q=max(0,len(p)-m)
    rows=[tuple(p[n-1+i-j] for j in range(n))+((-p[m+i])%3,) for i in range(q)]
    if any(len(c)>2 for c in F):return 'unknown',None
    status,R=low_support_basis(rows,n)
    if status!='ok':return status,None
    x=solve2(list(F)+row_clauses(R,n),n)
    if x is None:return 'unsat',None
    a=tuple(p[:m])+(0,)*max(0,m-len(p))
    b=tuple((-sum(a[n-1+i-j]*x[j] for j in range(n)))%3 for i in range(k))
    s=a+b
    assert s[:len(p)]==tuple(p) and accepts(F,x) and not any(hashval(n,k,s,x))
    return 'sat',(x,s)


def main():
    rng=Random(660);checks=0;statuses={z:0 for z in ('sat','unsat','unknown')};rowchecks=0
    for n in range(1,4):
        for k in range(1,3):
            L=n+2*k-1
            for _ in range(16):
                F=[tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randint(1,min(2,n)))) for _ in range(rng.randrange(6))]
                p=tuple(rng.randrange(3) for _ in range(rng.randrange(L+1)))
                q=max(0,len(p)-(n+k-1));X=[x for x in product((0,1),repeat=n) if accepts(F,x)]
                for x in X:
                    a=any(not any(hashval(n,k,p+t,x)) for t in product(range(3),repeat=L-len(p)))
                    b=all((sum(p[n-1+i-j]*x[j] for j in range(n))+p[n+k-1+i])%3==0 for i in range(q))
                    assert a==b;checks+=1
                ref=any(not any(hashval(n,k,p+t,x)) for x in X for t in product(range(3),repeat=L-len(p)))
                status,_=projected(F,n,k,p);statuses[status]+=1
                if status!='unknown':assert (status=='sat')==ref
    for n in range(1,8):
        for _ in range(30):
            rows=[tuple(rng.randrange(3) for _ in range(n+1)) for _ in range(rng.randrange(n+1))]
            status,R=low_support_basis(rows,n)
            for x in product((0,1),repeat=n):
                ref=all(sum(a*b for a,b in zip(r,x))%3==r[-1] for r in rows)
                if status=='ok':assert ref==accepts(row_clauses(R,n),x);rowchecks+=1
                elif status=='unsat':assert not ref;rowchecks+=1
    # Dense row representation of x0=x1=x2: invertible row operations.
    status,R=low_support_basis([(1,1,1,0),(1,2,0,0)],3)
    assert status=='ok' and solve2(row_clauses(R,3),3)==(0,0,0)
    assert low_support_basis([(1,1,1,1)],3)[0]=='unknown'
    # Original Toeplitz A=[I I], two hubs constrain canonical ternary lifts.
    controls=[]
    for k in (5,8,16,32,64):
        n=2*k;p=[0]*(n+k-1);p[n-1]=p[n-1-k]=1
        F=[(i+1,-(k+i+1)) for i in range(k)]+[(h+1,-(k+i+1)) for h in (0,1) for i in range(2,k)]
        status,ans=projected(F,n,k,p);assert status=='sat' and ans is not None
        # At least 4/9 of translation fibres have exactly one original lift.
        if k==5:
            counts=[0]*3**k
            for x in product((0,1),repeat=n):
                if accepts(F,x):
                    code=sum(((x[i]+x[i+k])%3)*3**i for i in range(k));counts[code]+=1
            assert max(counts)==1 and 9*sum(counts)>=4*3**k
        # Original support graph: each Boolean pair and its seed form a triangle.
        edges=[(i,k+i) for i in range(k)]+[(h,k+i) for h in (0,1) for i in range(2,k)]+[(i,2*k+i) for i in range(k)]+[(k+i,2*k+i) for i in range(k)]
        # A cut at either hub can remove incident clauses only; other hub survives.
        # For a seed pin row still joins its original bit pair. Worst-value branch
        # has at least this connected component, so no universally balanced cut.
        minimum=3*k
        for pin in range(3*k):
            adj={i:[] for i in range(3*k) if i!=pin}
            for i,j in edges:
                if pin not in (i,j):adj[i].append(j);adj[j].append(i)
            seen=set();best=0
            for i in adj:
                if i in seen:continue
                stack=[i];seen.add(i);size=0
                while stack:
                    v=stack.pop();size+=1
                    for u in adj[v]:
                        if u not in seen:seen.add(u);stack.append(u)
                best=max(best,size)
            minimum=min(minimum,best)
        assert minimum>2*k
        controls.append((k,minimum))
    print(dict(prefix_checks=checks,fixtures=96,statuses=statuses,rowspace_boolean_checks=rowchecks,controls=controls))

if __name__=='__main__':main()
