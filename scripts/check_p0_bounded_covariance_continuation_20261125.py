"""Bounded isolation continuation: exact finite support tests, not a SAT solver."""
from itertools import product
from fractions import Fraction as Q
from random import Random
from sympy import symbols, expand


def occupancy(S,n,k,s):
    A=s[:n+k-1]; b=s[n+k-1:]
    return sum(all((sum(A[i-j+n-1]*x[j] for j in range(n))+b[i])%3==0
                   for i in range(k)) for x in S)


def descend(values,L):
    values=list(values); u=[]
    for _ in range(L):
        w=len(values)//3
        blocks=[values[d*w:(d+1)*w] for d in range(3)]
        d=max(range(3),key=lambda d:sum(blocks[d]))
        assert 3*sum(blocks[d])>=sum(values)
        u.append(d); values=blocks[d]
    return tuple(u),values[0]


def main():
    f0,f1,f2=symbols('f0 f1 f2')
    parent=(f0+f1+f2)/3
    assert expand(3*(f0/3-parent/3)-(f0-parent))==0
    rng=Random(86)
    controls=0
    # Integer masses scaled by 1/total; TV for normalized finite measures.
    for _ in range(3000):
        n=12; child=[i%3 for i in range(n)]
        f=[rng.randrange(2) for _ in range(n)]
        g=[Q(rng.randrange(9),8) for _ in range(n)]
        w=[1]*n; v=w.copy()
        for _ in range(4):
            a,b=rng.sample(range(n),2)
            if v[a]: v[a]-=1;v[b]+=1
        eta=sum(abs(Q(f[i])-g[i])*w[i] for i in range(n))/n
        tv=Q(sum(abs(a-b) for a,b in zip(w,v)),2*n)
        true=[Q(sum(f[i] for i in range(n) if child[i]==d),n) for d in range(3)]
        est=[sum(g[i]*v[i] for i in range(n) if child[i]==d)/n for d in range(3)]
        d=max(range(3),key=lambda d:est[d]); e=max(range(3),key=lambda d:true[d])
        assert 3*(true[e]-true[d])<=3*eta+6*tv
        controls+=1
    supports=seeds=good=0
    for n in (1,2,3):
        xs=list(product((0,1),repeat=n))
        masks=range(1,1<<len(xs)) if n<=2 else rng.sample(range(1,256),20)
        for mask in masks:
            S=[x for i,x in enumerate(xs) if (mask>>i)&1]; m=len(S)
            supports+=1
            k=1
            while 3**k<2*m:k+=1
            L=n+2*k-1
            vals=[]; psi=0
            for s in product(range(3),repeat=L):
                h=occupancy(S,n,k,s); vals.append(int(h==1));psi+=h*(2-h)
            q=3**k
            assert Q(psi,3**L)==Q(m,q)-Q(m*(m-1),q*q)
            assert Q(sum(vals),len(vals))>=Q(psi,len(vals))>Q(1,12)
            s,b=descend(vals,L);assert b==1 and occupancy(S,n,k,s)==1
            seeds+=len(vals);good+=1
    # Equal first and second factorial moments; different singleton masses.
    A=[1,1,1,3,1,0,0,0,0]; B=[0,2,2,2,1,0,0,0,0]
    for z in (A,B):
        assert len(z)==9 and sum(z)==7 and sum(h*(h-1) for h in z)==6
    assert A.count(1)==4 and B.count(1)==1
    print(dict(transport_controls=controls,supports=supports,seed_evaluations=seeds,successful_descents=good,moment_collision=1))

if __name__=='__main__':main()
