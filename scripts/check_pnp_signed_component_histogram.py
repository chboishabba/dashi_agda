"""F3 source component histograms for the existing signed contrast observer.
Only original CNF and affine constraints determine components; the observable
is an additive label, not a coupling constraint. Fixed local free-width cap.
"""
from itertools import product
from check_p0_budgeted_residual_20261125 import cap as source_cap


def convolve(a,b):
    return tuple(sum(a[i]*b[(j-i)%3] for i in range(3)) for j in range(3))


def energy(h):
    # |H0 + omega H1 + omega^2 H2|^2, entirely in Z.
    a,b=h[0]-h[2],h[1]-h[2]
    return a*a-a*b+b*b

def rref(rows,n):
    A=[list(row) for row in rows]; p=0; piv=[]
    for j in range(n):
        i=next((i for i in range(p,len(A)) if A[i][j]),None)
        if i is None:continue
        A[p],A[i]=A[i],A[p]; a=A[p][j]
        A[p]=[a*v%3 for v in A[p]]
        for i in range(len(A)):
            if i!=p and A[i][j]:
                a=A[i][j]; A[i]=[(v-a*w)%3 for v,w in zip(A[i],A[p])]
        piv.append(j);p+=1
    if any(row[-1] for row in A[p:]):return None
    return tuple(tuple(row) for row in A[:p]),tuple(piv)


def local(F,rows,obs,width):
    n=len(obs); piv=tuple(next(i for i,a in enumerate(row[:-1]) if a) for row in rows)
    free=tuple(i for i in range(n) if i not in piv)
    if not F and not rows:
        h=(1,0,0)
        for a in obs:h=tuple(h[j]+h[(j-a)%3] for j in range(3))
        return True,2**n,h
    if len(free)<=width:
        h=[0]*3
        for bits in product(range(2),repeat=len(free)):
            x=[0]*n
            for i,b in zip(free,bits):x[i]=b
            for j,row in zip(piv,rows):x[j]=(row[-1]-sum(row[i]*x[i] for i in free))%3
            if 2 in x or not all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F):continue
            h[sum(a*b for a,b in zip(obs,x))%3]+=1
        return True,sum(h),tuple(h)
    cols=tuple(tuple(row[i] for row in rows) for i in range(n)); t=tuple(row[-1] for row in rows)
    C=source_cap(F,range(n),cols,t)
    ext=tuple(col+(a,) for col,a in zip(cols,obs))
    h=tuple(min(C,source_cap(F,range(n),ext,t+(d,))) for d in range(3))
    C=min(C,sum(h))
    return C==0,C,h


def component_bounds(F,cols,target,offset,remaining,width=6,spectral=False):
    """Return exactness, common cap, three componentwise count caps.
    For a refused local component retain upper mass, never infer emptiness
    from width refusal. No global product of local assignments is formed.
    """
    def receipt(done,C,H,E):
        return (done,C,H,E) if spectral else (done,C,H)
    R=tuple(sorted(remaining)); n=len(R); pos={v:i for i,v in enumerate(R)}
    rows=tuple(tuple(cols[v][i] for v in R)+(b,) for i,b in enumerate(target))
    rr=rref(rows,n)
    if rr is None or () in F:return receipt(True,0,(0,0,0),0)
    A,_=rr; clauses=tuple(tuple((pos[abs(l)-1]+1)*(1 if l>0 else -1) for l in c) for c in F)
    parent=list(range(n))
    def root(i):
        while parent[i]!=i:parent[i]=parent[parent[i]];i=parent[i]
        return i
    def join(I):
        for j in I[1:]:parent[root(j)]=root(I[0])
    for row in A:join([i for i,a in enumerate(row[:-1]) if a])
    for c in clauses:join([abs(l)-1 for l in c])
    groups={}
    for i in range(n):groups.setdefault(root(i),[]).append(i)
    gs={k:([],[]) for k in groups}
    for row in A:gs[root(next(i for i,a in enumerate(row[:-1]) if a))][0].append(row)
    for c in clauses:gs[root(abs(c[0])-1)][1].append(c)
    H=(1,0,0); C=1; exact=True; E=1
    for k,I in groups.items():
        remap={i:j for j,i in enumerate(I)}; ar,cl=gs[k]
        G=tuple(tuple((remap[abs(l)-1]+1)*(1 if l>0 else -1) for l in c) for c in cl)
        ar=tuple(tuple(row[i] for i in I)+(row[-1],) for row in ar)
        done,c,h=local(G,ar,tuple(cols[R[i]][-1] for i in I),width)
        if c==0:return receipt(True,0,(0,0,0),0)
        E*=energy(h) if done else c*c
        exact=exact and done; C*=c; H=convolve(H,h)
        H=tuple(min(C,h) for h in H)
    C=min(C,sum(H)); H=tuple(min(C,h) for h in H)
    return receipt(exact or C==0,C,tuple(H[(j-offset)%3] for j in range(3)),min(E,C*C))
