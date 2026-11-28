"""Original rational chart and exact independent free-coordinate components.
Logical operation cap; Fraction bit costs are not metered here.
"""
from fractions import Fraction as Q
from itertools import product
from math import prod


class Refusal(Exception):pass
class Budget:
    def __init__(self,cap):
        if cap<0:raise ValueError('cap')
        self.left=cap
    def pay(self,k):
        if k>self.left:raise Refusal()
        self.left-=k


def chart(A,b,n,B):
    m=len(A);B.pay(1+m*(n+m+1));D=[[Q(v) for v in a]+[Q(t)]+[Q(i==j) for j in range(m)] for i,(a,t) in enumerate(zip(A,b))];P=[]
    for j in range(n):
        B.pay(1+m);k=next((i for i in range(len(P),m) if D[i][j]),None)
        if k is None:continue
        i=len(P);P.append(j);D[i],D[k]=D[k],D[i];B.pay(1+m*(n+m+1));u=D[i][j];D[i]=[v/u for v in D[i]]
        for k in range(m):
            if k!=i:
                u=D[k][j];D[k]=[v-u*w for v,w in zip(D[k],D[i])]
    B.pay(1+m*m*(n+1));assert all(sum(c*a[j] for c,a in zip(row[n+1:],A))==row[j] for row in D for j in range(n))
    assert all(sum(c*t for c,t in zip(row[n+1:],b))==row[n] for row in D)
    if any(not any(row[:n]) and row[n] for row in D):return None,tuple(map(tuple,D))
    J=tuple(j for j in range(n) if j not in P);C=[(Q(0),{j:Q(1)}) for j in range(n)]
    for i,j in enumerate(P):C[j]=(D[i][n],{k:-D[i][k] for k in J if D[i][k]})
    # Reverse inclusion: every rational chart point satisfies original A x=b.
    B.pay(1+m*n*(len(J)+1));assert all(sum(a[j]*C[j][0] for j in range(n))==t for a,t in zip(A,b))
    assert all(sum(a[j]*C[j][1].get(k,0) for j in range(n))==0 for a in A for k in J)
    return (J,C),tuple(map(tuple,D))


def solve(A,b,n,F=(),H=(),t=(),O=(),cap=1000000,max_width=12):
    if n<0 or len(A)!=len(b) or len(H)!=len(t) or any(len(r)!=n for r in A+H) or any(not 1<=abs(l)<=n for c in F for l in c) or any(len(set(c))!=len(c) or any(not 0<=i<n for i in c) for c in O):raise ValueError('source')
    B=Budget(cap);width=None
    try:
        q,receipt=chart(A,b,n,B)
        if q is None:return dict(status='EMPTY',used=cap-B.left,receipt=receipt)
        J,C=q;parent={j:j for j in J};factors=[]
        def root(j):
            while parent[j]!=j:j=parent[j]
            return j
        def factor(kind,ids,data):
            S=tuple(sorted({k for j in ids for k in C[j][1]}));B.pay(1+len(ids)*(n+1)+len(S)**2)
            for k in S[1:]:parent[root(k)]=root(S[0])
            factors.append((kind,ids,data,S))
        for j in range(n):factor('bit',(j,),None)
        for c in F:factor('cnf',tuple(abs(l)-1 for l in c),c)
        for r,v in zip(H,t):factor('f3',tuple(j for j,a in enumerate(r) if a%3),(r,v))
        for c in O:factor('one',c,None)
        groups={}
        for j in J:groups.setdefault(root(j),[]).append(j)
        width=max(map(len,groups.values()),default=0);buckets={k:[] for k in groups};const=[]
        for f in factors:
            if not f[3]:const.append(f)
            else:
                k=root(f[3][0]);assert all(root(j)==k for j in f[3]);buckets[k].append(f)
        def value(j,u):return C[j][0]+sum(a*u[k] for k,a in C[j][1].items())
        def check(f,u):
            kind,ids,data,S=f;B.pay(1+len(ids)*(n+1));v=tuple(value(j,u) for j in ids)
            if any(a not in (0,1) for a in v):return False
            if kind=='bit':return True
            if kind=='cnf':return any(a==int(l>0) for a,l in zip(v,data))
            if kind=='f3':return sum(data[0][j]*a for j,a in zip(ids,v))%3==data[1]%3
            return sum(v)==1
        if not all(check(f,{}) for f in const):return dict(status='EMPTY',used=cap-B.left,width=width,receipt=receipt)
        if width>max_width:return dict(status='UNKNOWN',used=cap-B.left,width=width,free=len(J))
        u={};counts=[];points=0
        for k,G in groups.items():
            c=0;w=None
            # Pay before each point; no construction of huge 2**width bound.
            for bits in product((0,1),repeat=len(G)):
                B.pay(1+len(G));points+=1;v=dict(zip(G,bits))
                if all(check(f,v) for f in buckets[k]):c+=1;w=v
            if not c:return dict(status='EMPTY',used=cap-B.left,width=width,free=len(J),points=points,receipt=receipt)
            counts.append(c);u.update(w)
        B.pay(1+n*(n+1));x=tuple(int(value(j,u)) for j in range(n))
        assert all(sum(a*v for a,v in zip(r,x))==s for r,s in zip(A,b)) and all(check(f,u) for f in factors)
        return dict(status='WITNESS',witness=x,count=prod(counts),width=width,free=len(J),points=points,used=cap-B.left,receipt=receipt)
    except Refusal:return dict(status='UNKNOWN',used=cap-B.left,width=width)


def main():
    from random import Random
    rng=Random(3693402);C={}
    for n in range(9):
        for _ in range(32):
            A=tuple(tuple(rng.randrange(-2,3) for j in range(n)) for i in range(rng.randrange(4)));b=tuple(rng.randrange(-2,3) for r in A)
            F=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for j in range(3)) for i in range(rng.randrange(4))) if n else ()
            H=tuple(tuple(rng.randrange(3) for j in range(n)) for i in range(rng.randrange(2)));t=tuple(rng.randrange(3) for r in H);O=tuple(tuple(j for j in range(n) if rng.randrange(2)) for i in range(rng.randrange(2)))
            W=[x for x in product((0,1),repeat=n) if all(sum(a*v for a,v in zip(r,x))==s for r,s in zip(A,b)) and all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and all(sum(a*v for a,v in zip(r,x))%3==s for r,s in zip(H,t)) and all(sum(x[j] for j in c)==1 for c in O)]
            q=solve(A,b,n,F,H,t,O,cap=10**7);assert q['status']==('WITNESS' if W else 'EMPTY')
            if W:assert q['witness'] in W and q['count']==len(W)
            C[q['status']]=C.get(q['status'],0)+1
    # Large global nullity but independent original pair factors.
    for k in (8,16,32,64):
        n=2*k;A=tuple(tuple(int(j//2==i) for j in range(n)) for i in range(k));b=(1,)*k
        q=solve(A,b,n,cap=10**8,max_width=1);assert q['count']==2**k and q['free']==k and q['width']==1 and q['points']==2*k
        print('independent',k,q['points'],q['used'])
    # Growing connected free dimension: do not silently claim completeness.
    q=solve((),(),32,F=(tuple(range(1,33)),),max_width=12);assert q['status']=='UNKNOWN' and q['width']==32
    assert solve(((1,),),(1,),1,cap=0)['status']=='UNKNOWN'
    print(C,'connected and budget refusal PASS')
if __name__=='__main__':main()
