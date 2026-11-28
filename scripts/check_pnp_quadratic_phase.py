"""Exact structured character contraction on affine F3 supports.

Each local character table is derived from original Boolean lifts. An affine
support and quadratic phase are accepted only after checking EVERY local
entry. Nonconforming tables can be retained as disjoint singleton pieces,
subject to a total branch/work cap; refusal is not emptiness. No Fourier
coefficient oracle, no universal bound on nonlinear component size.
"""
from itertools import product
from check_pnp_f3_syndrome_boundary import blocks, span, chart
from check_pnp_f3_normal_fold import normal_fold
from check_pnp_dual_syndrome_fourier import Z, ONE, OMEGA, add, mul, phase, contrast


class Refusal(Exception):pass


def put(P,m,a):
    a=(P.get(m,0)+a)%3
    if a:P[m]=a
    else:P.pop(m,None)


def evaluate(P,x):
    return sum(a*(1 if not m else x[m[0]] if len(m)==1 else x[m[0]]*x[m[1]]) for m,a in P.items())%3


def linear(c,v):
    return {m:a for m,a in [((),c%3)]+[((i,),b%3) for i,b in enumerate(v)] if a}


def addprod(P,A,B,k,pay):
    pay(len(A)*len(B))
    for m,a in A.items():
        for n,b in B.items():put(P,tuple(sorted(m+n)),k*a*b)


def pull(P,forms,pay):
    Q={}
    for m,a in P.items():
        if not m:pay(1);put(Q,(),a)
        elif len(m)==1:
            pay(len(forms[m[0]]))
            for j,b in forms[m[0]].items():put(Q,j,a*b)
        else:addprod(Q,forms[m[0]],forms[m[1]],a,pay)
    return Q


def gauss(P,n,pay):
    """Sum omega^P over F3^n by invertible shear and square completion."""
    P={m:a%3 for m,a in P.items() if a%3};live=set(range(n));z=ONE
    while True:
        pay(1+len(P));i=next((m[0] for m in P if len(m)==2 and m[0]==m[1]),None)
        if i is None:
            cross=next((m for m in P if len(m)==2),None)
            if cross is None:break
            i,j=cross
            # Old x_j = new x_j + new x_i: invertible, creates a square.
            forms=[{(h,):1} for h in range(n)];forms[j][(i,)]=1
            P=pull(P,forms,pay)
        a=P.pop((i,i));L={}
        for m,b in tuple(P.items()):
            if i in m:
                del P[m];put(L,tuple(j for j in m if j!=i),b)
        # 4=1 and a^-1=a in F3. Sum over xi leaves -a L^2.
        addprod(P,L,L,-a,pay);z=mul(z,add(ONE,add(OMEGA[a],OMEGA[a])))
        live.remove(i)
    if any(len(m)==1 for m in P):return Z
    return phase(mul(z,(3**len(live),0)),P.get((),0))


def recognize(T,r,pay):
    """T is a sparse complete local table; absent entries are exactly zero.
    Return (amplitude, offset, support directions, quadratic) or None.
    Empty tables are handled by the caller.
    """
    u=min(T);c=T[u];V=span((tuple((a-b)%3 for a,b in zip(s,u)) for s in T),r);d=len(V)
    if len(T)!=3**d:return None
    piv=tuple(next(i for i,a in enumerate(v) if a) for v in V)
    D={}
    for s,a in T.items():
        pay(1+r)
        z=tuple((s[i]-u[i])%3 for i in piv)
        if tuple((b+sum(t*v[i] for t,v in zip(z,V)))%3 for i,b in enumerate(u))!=s:return None
        e=next((e for e in range(3) if phase(c,e)==a),None)
        if e is None:return None
        D[z]=e
    if len(D)!=3**d:return None
    # Degree <=2 interpolation in the unique reduced polynomial basis.
    def point(vals):return tuple(vals.get(i,0) for i in range(d))
    P={};base=D[point({})];put(P,(),base)
    for i in range(d):
        a=(D[point({i:1})]-base)%3;b=(D[point({i:2})]-base)%3
        put(P,(i,),2*(a-b));put(P,(i,i),2*(a+b))
    for i in range(d):
        for j in range(i+1,d):
            z=point({i:1,j:1});put(P,(i,j),D[z]-evaluate(P,z))
    for z,e in D.items():
        pay(1+len(P))
        if evaluate(P,z)!=e:return None
    return c,u,V,P


def singleton(s,a):return a,s,(),{}


def contract(pieces,target,offset,pay):
    r=len(target);u=[0]*r;V=[];P={};c=ONE
    for a,s,W,Q in pieces:
        c=mul(c,a);u=[(x+y)%3 for x,y in zip(u,s)];d=len(V);V.extend(W)
        for m,b in Q.items():put(P,tuple(i+d for i in m),b)
    rhs=tuple((t-x)%3 for t,x in zip(target,u));n=len(V)
    pay(1+r+n+r*n)
    q=chart(tuple(tuple(v[i] for v in V) for i in range(r)),rhs,n)
    if q is None:return Z
    a,B=q;forms=[linear(a[i],tuple(v[i] for v in B)) for i in range(n)]
    Q=pull(P,forms,pay);put(Q,(),offset)
    return mul(c,gauss(Q,len(B),pay))


def structured_contrast(F,cols,target,offset,R,w,local_width=6,branch_cap=64,work_cap=16384,normal_label_width=3,normal_boundary_width=3):
    """Exact character via local affine/quadratic recognition and Gauss sums.
    Exceptional local tables partition into singleton labels; the entire
    branch product must fit the cap. Each original witness contributes once.
    Work units are explicit point visits and polynomial term operations,
    NOT a physical bit clock; linear algebra and integer sizes are separate.
    """
    R=tuple(sorted(R));r=len(target);stats=dict(work=0,blocks=0,structured=0,exceptional=0,branches=0,phase_rank=0,normal_queries=0)
    def pay(n):
        if stats['work']+n>work_cap:raise Refusal('work')
        stats['work']+=n
    def result(z):
        a=tuple(w*t for t in contrast(z));return a,a,dict(stats,character=z)
    try:
        pay(1+len(R)+r+sum(1+len(c) for c in F))
        if () in F:return result(Z)
        G=blocks(F,R);stats['blocks']=len(G);choices=[];branches=1
        for I,C in G:
            T={}
            if len(I)<=local_width:
                pay(2**len(I))
                for bits in product(range(2),repeat=len(I)):
                    x=dict(zip(I,bits))
                    if not all(any(x[abs(l)-1]==int(l>0) for l in cl) for cl in C):continue
                    s=tuple(sum(cols[j][a]*x[j] for j in I)%3 for a in range(r));o=sum(cols[j][-1]*x[j] for j in I)%3
                    T[s]=add(T.get(s,Z),OMEGA[o])
            else:
                # Large connected CNF block: use the existing original
                # normal-fold producer on its bounded-rank syndrome image.
                # All actual image labels are queried; no missing label
                # is assumed zero and the subcalls share the work cap.
                B=span((cols[j][:-1] for j in I),r)
                if len(B)>normal_label_width:raise Refusal('local image width')
                pay(3**len(B))
                for v in product(range(3),repeat=len(B)):
                    s=tuple(sum(a*b[i] for a,b in zip(v,B))%3 for i in range(r))
                    H,st=normal_fold(C,cols,s,0,I,local_width,normal_boundary_width,work_cap-stats['work'])
                    pay(st['work']);stats['normal_queries']+=1
                    if H is None:raise Refusal('normal producer')
                    T[s]=(H[0]-H[2],H[1]-H[2])
            T={s:a for s,a in T.items() if a!=Z}
            if not T:return result(Z) # exact character, NOT source emptiness
            q=recognize(T,r,pay)
            if q is not None:
                stats['structured']+=1;stats['phase_rank']+=len(q[2]);choices.append((q,))
            else:
                stats['exceptional']+=1;branches*=len(T)
                if branches>branch_cap:raise Refusal('exception product')
                choices.append(tuple(singleton(s,a) for s,a in sorted(T.items())))
        if branches>branch_cap:raise Refusal('exception product')
        z=Z
        for p in product(*choices):
            pay(1);stats['branches']+=1;z=add(z,contract(p,target,offset,pay))
        return result(z)
    except Refusal:return None
