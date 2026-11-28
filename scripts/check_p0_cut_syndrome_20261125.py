from itertools import product
from collections import defaultdict
from random import Random
from fractions import Fraction as Q

# Exact F3 vector arithmetic; basis indexed by pivot.
def add(a,b): return tuple((x+y)%3 for x,y in zip(a,b))
def sub(a,b): return tuple((x-y)%3 for x,y in zip(a,b))
def basis(cols):
    B={}
    for col in cols:
        z=list(col)
        for i,b in sorted(B.items()):
            t=z[i]
            if t:z=[(x-t*y)%3 for x,y in zip(z,b)]
        if any(z):
            i=next(i for i,x in enumerate(z) if x);B[i]=tuple(x*z[i]%3 for x in z)
    return B

def contains(B,col):
    z=list(col)
    for i,b in sorted(B.items()):
        t=z[i]
        if t:z=[(x-t*y)%3 for x,y in zip(z,b)]
    return not any(z)

def tree(order):
    if len(order)==1:return order[0]
    h=len(order)//2;return tree(order[:h]),tree(order[h:])

def solve(domains,columns,contrib,factors,target,order):
    # columns[i] spans all possible local contributions; contrib[i][state] is actual contribution.
    n=len(domains);allv=set(range(n));zero=(0,)*len(target)
    stats={'nodes':0,'entries':0,'joins':0,'peak':0,'lambda':0,'bound':0}
    def node(t):
        if isinstance(t,int):U={t};children=None
        else:
            l=node(t[0]);r=node(t[1]);U=l[0]|r[0];children=(l,r)
        outside=allv-U
        boundary=tuple(sorted({i for scope,pred in factors if set(scope)&outside for i in scope if i in U}))
        I=U-set(boundary)
        BI=basis(c for i in I for c in columns[i]);BO=basis(c for i in outside for c in columns[i]);BR=basis([*BI.values(),*BO.values()])
        lam=len(BI)+len(BO)-len(BR)
        table={}
        def save(a,s,count,w):
            # s includes boundary contributions; after fixing a, possible interior syndromes form affine intersection.
            if not contains(BO,sub(target,s)):return
            key=(tuple(a[i] for i in boundary),s)
            if key in table:table[key]=(table[key][0]+count,table[key][1])
            else:table[key]=(count,w)
        if children is None:
            i=t;local=[(scope,pred) for scope,pred in factors if set(scope)<=U]
            for d in domains[i]:
                a={i:d}
                if all(pred(*(a[j] for j in sc)) for sc,pred in local):save(a,contrib[i][d],1,a)
        else:
            (UL,BL,TL),(UR,BRD,TR)=children
            crossing=[(sc,pred) for sc,pred in factors if set(sc)<=U and not set(sc)<=UL and not set(sc)<=UR]
            for (al,sl),(nl,wl) in TL.items():
                for (ar,sr),(nr,wr) in TR.items():
                    stats['joins']+=1
                    a=dict(zip(BL,al));a.update(zip(BRD,ar))
                    if all(pred(*(a[j] for j in sc)) for sc,pred in crossing):save(a,add(sl,sr),nl*nr,wl|wr)
        bound=3**lam
        for i in boundary:bound*=len(domains[i])
        assert len(table)<=bound,(U,bound,len(table))
        stats['nodes']+=1;stats['entries']+=len(table);stats['peak']=max(stats['peak'],len(table));stats['lambda']=max(stats['lambda'],lam);stats['bound']=max(stats['bound'],bound)
        return U,boundary,table
    _,_,T=node(tree(order));count,w=T.get(((),target),(0,None))
    if w is not None:
        assert len(w)==n and all(pred(*(w[i] for i in sc)) for sc,pred in factors)
        s=zero
        for i in range(n):s=add(s,contrib[i][w[i]])
        assert s==target
    return count,w,stats

def compile_problem(n,clauses,rows,target,paired=False,j=None,pins=None):
    # paired constraints: row matrix applies to x-y, optional prefix rows apply to x only.
    pins=pins or []
    domains=[tuple((a,a) for a in range(2)) if paired and j is not None and i<j else tuple(product(range(2),repeat=2)) if paired else (0,1) for i in range(n)]
    cols=[];con=[]
    for i in range(n):
        a=tuple(row[i]%3 for row in rows);p=tuple(row[i]%3 for row in pins)
        if paired:
            c=a+p;d=tuple(-z%3 for z in a)+(0,)*len(p)
            if j is not None and i<j:cols.append([add(c,d)])
            else:cols.append([c,d])
            con.append({(x,y):add(tuple(x*z%3 for z in c),tuple(y*z%3 for z in d)) for x,y in domains[i]})
        else:
            assert not pins;cols.append([a]);con.append({x:tuple(x*z%3 for z in a) for x in domains[i]})
    fs=[]
    for cl in clauses:
        sc=tuple(i for i,b in cl);bs=tuple(b for i,b in cl)
        if paired:
            fs.append((sc,lambda *v,bs=bs:all(any(x[c]==b for x,b in zip(v,bs)) for c in (0,1))))
        else:fs.append((sc,lambda *v,bs=bs:any(x==b for x,b in zip(v,bs))))
    if paired and j is not None:fs.append(((j,),lambda v:v[0]!=v[1]))
    return domains,cols,con,fs,tuple(target)

def calc(n,clauses,rows,target,order,paired=False,j=None,pins=None):
    return solve(*compile_problem(n,clauses,rows,target,paired,j,pins),order)

def mat(rows,x):return tuple(sum(a*b for a,b in zip(row,x))%3 for row in rows)
def toeplitz(n,k,a):return [[a[n-1+i-j] for j in range(n)] for i in range(k)]

def ref(n,clauses):return [x for x in product(range(2),repeat=n) if all(any(x[i]==b for i,b in cl) for cl in clauses)]

rng=Random(369);checks=coef=trans=back=nodes=entries=joins=peak=0
for n in range(1,6):
    for k in range(1,4):
        for trial in range(4):
            clauses=[tuple((i,rng.randrange(2)) for i in sorted(rng.sample(range(n),rng.randrange(1,min(3,n)+1)))) for _ in range(rng.randrange(6))]
            S=ref(n,clauses);order=list(range(n));rng.shuffle(order)
            a=tuple(rng.randrange(3) for _ in range(n+k-1));A=toeplitz(n,k,a)
            def run(rows,target,expected,paired=False,j=None,pins=None):
                global checks,back,nodes,entries,joins,peak
                v,w,st=calc(n,clauses,rows,target,order,paired,j,pins)
                assert v==expected,(n,k,rows,target,v,expected)
                checks+=1;back+=int(w is not None);nodes+=st['nodes'];entries+=st['entries'];joins+=st['joins'];peak=max(peak,st['peak'])
                return v
            m=run([],(),len(S))
            for p in range(len(a)+1):
                nu=Q(0)
                for j in range(n):
                    t=min(k,max(0,p-n+1+j));B=A[:t]
                    expected=sum(x[:j]==y[:j] and x[j]!=y[j] and mat(B,x)==mat(B,y) for x in S for y in S)
                    C=run(B,(0,)*t,expected,True,j);nu+=Q(C,3**(2*k-t))
                # independent explicit free-diagonal enumeration
                total=0
                for tail in product(range(3),repeat=len(a)-p):
                    AA=toeplitz(n,k,a[:p]+tail);W=defaultdict(int)
                    for x in S:W[mat(AA,x)]+=1
                    total+=sum(h*(h-1) for h in W.values())
                assert nu==Q(total,3**(len(a)-p+k));coef+=1
            for e in range(k+1):
                b=tuple(rng.randrange(3) for _ in range(e));pin=tuple(-z%3 for z in b)
                X=[x for x in S if mat(A[:e],x)==pin]
                z1=run(A[:e],pin,len(X));z2=run(A,(0,)*k+pin,sum(mat(A,x)==mat(A,y) for x in X for y in S),True,pins=A[:e]);D=3**(k-e)
                W=defaultdict(int)
                for x in X:W[mat(A,x)]+=1
                assert Q(2*z1-z2,D)==Q(sum(h*(2-h) for h in W.values()),D);trans+=1
# Large rank, tiny interface: identity fixes original variables independently, paired equality grouped by original coordinates.
large=[]
for n in (16,32,64):
    A=[[int(i==j) for j in range(n)] for i in range(n)];v=tuple(i%2 for i in range(n))
    c,w,s=calc(n,[],A,v,list(range(n)));assert c==1 and s['lambda']==0 and s['peak']==1
    c2,w2,s2=calc(n,[],A,(0,)*n,list(range(n)),True);assert c2==2**n and s2['lambda']==0 and s2['peak']==1
    large.append((n,c2,s['entries'],s2['entries'],s2['joins']))
print(dict(count_checks=checks,coefficient_prefixes=coef,translation_prefixes=trans,witness_backpointers=back,tree_nodes=nodes,table_entries=entries,join_candidates=joins,peak_table=peak,large_rank_controls=large))
