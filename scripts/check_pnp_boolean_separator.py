"""Original rational Boolean chart: exact bucket elimination and replay.
Selected induced width, not minimum width. Logical allowance, not bit clock.
"""
from itertools import product
from math import prod
from check_pnp_boolean_fibre import chart
from check_pnp_source_derived_cover import Reservation, Refused


def source(A,b,n,F,H,t,O,B):
    if n<0 or len(A)!=len(b) or len(H)!=len(t) or any(len(r)!=n for r in A+H) or any(not 1<=abs(l)<=n for c in F for l in c) or any(len(set(c))!=len(c) or any(not 0<=i<n for i in c) for c in O):raise ValueError('source')
    B.pay(1+n+sum(1+len(c) for c in F+O)+(len(A)+len(H))*(n+1))
    q,R=chart(A,b,n,B)
    if q is None:return None,R
    J,C=q;factors=[]
    def add(kind,ids,data):
        B.pay(1+len(ids)*(n+1));S=tuple(sorted({k for j in ids for k in C[j][1]}))
        factors.append((S,kind,ids,data))
    for j in range(n):add('bit',(j,),None)
    for c in F:add('cnf',tuple(abs(l)-1 for l in c),c)
    for r,v in zip(H,t):add('f3',tuple(j for j,a in enumerate(r) if a%3),(r,v))
    for c in O:add('one',c,None)
    return (J,C,tuple(factors)),R


def value(C,j,u):return C[j][0]+sum(a*u[k] for k,a in C[j][1].items())


def evaluate(C,f,u,B):
    S,kind,ids,data=f;B.pay(1+sum(1+len(C[j][1]) for j in ids));v=tuple(value(C,j,u) for j in ids)
    if any(a not in (0,1) for a in v):return 0
    if kind=='bit':return 1
    if kind=='cnf':return int(any(a==int(l>0) for a,l in zip(v,data)))
    if kind=='f3':return int(sum(data[0][j]*a for j,a in zip(ids,v))%3==data[1]%3)
    return int(sum(v)==1)


def audit(A,b,n,F,H,t,O,x,B):
    B.pay(1+n+(len(A)+len(H))*(n+1)+sum(1+len(c) for c in F+O))
    return len(x)==n and all(v in (0,1) for v in x) and all(sum(a*v for a,v in zip(r,x))==s for r,s in zip(A,b)) and all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and all(sum(a*v for a,v in zip(r,x))%3==s%3 for r,s in zip(H,t)) and all(sum(x[j] for j in c)==1 for c in O)


def choose(remaining,active,B):
    # Source-derived min induced degree (not a claim of optimality).
    B.pay(1+len(remaining)*(1+sum(1+len(s) for s in active.values())))
    def score(j):return len(set().union(*(set(s) for s in active.values() if j in s))),j
    return min(remaining,key=score)


def fold(A,b,n,F=(),H=(),t=(),O=(),cap=1000000,max_width=12,clip=None,order=None):
    if max_width<0 or clip not in (None,2):raise ValueError('limits')
    B=Reservation(cap);width=points=0;trace=[]
    try:
        q,R=source(A,b,n,F,H,t,O,B)
        if q is None:return dict(status='EMPTY',count=0,used=cap-B.left,trace=None)
        J,C,fs=q;remaining=set(J);active={i:f[0] for i,f in enumerate(fs)};tables={};witness={}
        if order is not None and (len(order)!=len(J) or set(order)!=remaining):raise ValueError('order')
        def get(i,u):
            if i<len(fs):return evaluate(C,fs[i],u,B)
            B.pay(1+len(active[i]));return tables[i].get(tuple(u[j] for j in active[i]),0)
        def mul(a,b):return a*b if clip is None else min(clip,a*b)
        def add(a,b):return a+b if clip is None else min(clip,a+b)
        while remaining:
            j=choose(remaining,active,B) if order is None else order[len(trace)]
            B.pay(1+sum(1+len(s) for s in active.values()));ids=tuple(i for i,s in active.items() if j in s)
            S=tuple(sorted(set().union(*(set(active[i]) for i in ids))-{j}));width=max(width,len(S)+1)
            if width>max_width:raise Refused()
            T={};W={}
            for bits in product((0,1),repeat=len(S)):
                u=dict(zip(S,bits));mass=0
                for v in (0,1):
                    B.pay(1+len(S)+len(ids));points+=1;u[j]=v;p=1
                    for i in ids:
                        p=mul(p,get(i,u))
                        if not p:break
                    if p:W[bits]=v;mass=add(mass,p)
                if mass:T[bits]=mass
            out=len(fs)+len(trace);trace.append((j,ids,S,T,W))
            for i in ids:del active[i];tables.pop(i,None)
            active[out]=S;tables[out]=T;remaining.remove(j)
        mass=1
        for i in active:assert not active[i];mass=mul(mass,get(i,{}))
        if not mass:return dict(status='EMPTY',count=0,width=width,points=points,trace=tuple(trace),used=cap-B.left)
        u={}
        for j,ids,S,T,W in reversed(trace):
            B.pay(1+len(S));u[j]=W[tuple(u[k] for k in S)]
        B.pay(1+sum(1+len(c[1]) for c in C));z=tuple(value(C,j,u) for j in range(n));assert all(v in (0,1) for v in z);x=tuple(map(int,z));assert audit(A,b,n,F,H,t,O,x,B)
        return dict(status='WITNESS',count=mass,witness=x,width=width,points=points,trace=tuple(trace),used=cap-B.left)
    except Refused:return dict(status='UNKNOWN',width=width,points=points,used=cap-B.left)


def replay(A,b,n,F,H,t,O,result,cap,clip=None):
    """Independently rebuild scopes and each table entry, including zeros.
    Replays full row operations via chart; no trust in claimed width/order.
    """
    B=Reservation(cap)
    try:
        q,_=source(A,b,n,F,H,t,O,B)
        if q is None:return result['status']=='EMPTY' and result['count']==0 and result['trace'] is None
        J,C,fs=q;active={i:(f[0],None) for i,f in enumerate(fs)};remaining=set(J)
        trace=result['trace'];width=points=0
        if trace is None or len(trace)!=len(J):return False
        def val(i,u):
            S,T=active[i]
            if T is None:return evaluate(C,fs[i],u,B)
            B.pay(1+len(S));return T.get(tuple(u[k] for k in S),0)
        for idx,(j,ids,S,T,W) in enumerate(trace):
            B.pay(1+sum(1+len(s) for s,t in active.values()))
            if j not in remaining or ids!=tuple(i for i,(s,t) in active.items() if j in s):return False
            if S!=tuple(sorted(set().union(*(set(active[i][0]) for i in ids))-{j})):return False
            width=max(width,len(S)+1);expected={};choices={}
            for a in product((0,1),repeat=len(S)):
                B.pay(1+len(S)+len(ids));u=dict(zip(S,a));p=[]
                for v in (0,1):
                    B.pay(1+len(S)+len(ids));u[j]=v;p.append(prod(val(i,u) for i in ids));points+=1
                mass=sum(p);mass=mass if clip is None else min(clip,mass)
                if mass:expected[a]=mass;choices[a]=tuple(v for v in (0,1) if p[v])
            if T!=expected or set(W)!=set(expected) or any(W[a] not in choices[a] for a in W):return False
            for i in ids:del active[i]
            active[len(fs)+idx]=(S,expected);remaining.remove(j)
        mass=prod(val(i,{}) for i in active);mass=mass if clip is None else min(clip,mass)
        if remaining or result['count']!=mass or result['width']!=width or result['points']!=points:return False
        if not mass:return result['status']=='EMPTY'
        return result['status']=='WITNESS' and audit(A,b,n,F,H,t,O,result['witness'],B)
    except (Refused,KeyError,TypeError,ValueError):return False
