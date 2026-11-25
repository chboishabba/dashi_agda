"""Exact dual-space binary splitting on affine forbidden-flat clauses."""
from itertools import product
from random import Random


def basis(vs):
    B={}
    for v in vs:
        while v:
            i=v.bit_length()-1
            if i in B:v^=B[i]
            else:B[i]=v;break
    return tuple(B[i] for i in sorted(B,reverse=True))


def intersection(A,B):
    # Eliminate projected B modulo A, carrying the original B vector.
    D={};out=[]
    for w in B:
        v=w
        for a in A:
            if v>>(a.bit_length()-1)&1:v^=a
        while v:
            i=v.bit_length()-1
            if i in D:
                u,t=D[i];v^=u;w^=t
            else:D[i]=(v,w);break
        else:out.append(w)
    return basis(out)


def key(B,z):return tuple((v&z).bit_count()%2 for v in B)


def lift(rows):
    D={}
    for v,b in rows:
        while v:
            i=v.bit_length()-1
            if i in D:w,c=D[i];v^=w;b^=c
            else:D[i]=(v,b);break
        else:
            if b:return None
    z=0
    for i,(v,b) in sorted(D.items()):
        if (v&z).bit_count()%2!=b:z|=1<<i
    return z


def solve(E,d,cap):
    if not E:return 1<<d,0,0,0
    U=[basis(v for v,b in e) for e in E];peak=joins=0
    def rec(lo,hi):
        nonlocal peak,joins
        A=basis(v for B in U[lo:hi] for v in B)
        O=basis(v for B in U[:lo]+U[hi:] for v in B)
        C=intersection(A,O)
        if len(C)>cap:raise OverflowError
        out={}
        def add(z,n):
            k=key(C,z);old=out.get(k,(0,z));out[k]=(old[0]+n,old[1])
        if hi-lo==1:
            for b in product((0,1),repeat=len(A)):
                z=lift(zip(A,b));assert z is not None
                if not all((v&z).bit_count()%2==t for v,t in E[lo]):add(z,1)
        else:
            mid=(lo+hi)//2;L,P=rec(lo,mid);R,Q=rec(mid,hi)
            # Representatives agree on overlap iff their full restrictions glue.
            for n,z in P.values():
                for m,w in Q.values():
                    joins+=1
                    t=lift(list(zip(L,key(L,z)))+list(zip(R,key(R,w))))
                    if t is not None:add(t,n*m)
        peak=max(peak,len(out));return A,out
    A,P=rec(0,len(E));n,z=P.get((),(0,None))
    return n*(1<<(d-len(A))),z,peak,joins


def main():
    rng=Random(70);checks=0
    for d in range(1,9):
        for _ in range(50):
            E=[[(rng.randrange(1<<d),rng.randrange(2)) for _ in range(rng.randrange(1,4))] for _ in range(rng.randrange(1,10))]
            good=[z for z in range(1<<d) if all(not all((v&z).bit_count()%2==b for v,b in e) for e in E)]
            n,z,p,j=solve(E,d,d);assert n==len(good);assert (z in good) if n else z is None;checks+=1
    print('random exact count/witness checks',checks)
    for g in (4,8,16,32):
        d=3*g;d+=d%2
        V=[((1<<d)-1)^(1<<i) for i in range(d)]
        assert len(basis(V))==d
        for singleton in (False,True):
            E=[]
            for i in range(g):
                for b in (list(product((0,1),repeat=3))[1:] if singleton else [(0,0,0)]):
                    E.append(list(zip(V[3*i:3*i+3],b)))
            n,z,p,j=solve(E,d,3);expected=(1 if singleton else 7**g)*(1<<(d-3*g));assert n==expected and z is not None
            assert all(not all((v&z).bit_count()%2==b for v,b in e) for e in E)
            print('dense',d,'events',len(E),'singleton blocks',singleton,'count',n,'peak',p,'joins',j)

if __name__=='__main__':main()
