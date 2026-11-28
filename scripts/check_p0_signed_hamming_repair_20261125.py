"""Section 78: original-clause bounded signed repair, exact local acceptance."""
from random import Random


def accepts(F,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in F)


def repair(F,n,a,r,packing=True):
    calls=0;prunes=0
    def walk(D,left):
        nonlocal calls,prunes
        calls+=1;x=a^D
        bad=[]
        for c in F:
            if any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c):continue
            A=tuple(sorted({abs(l)-1 for l in c if not D>>(abs(l)-1)&1}))
            if not A: return None
            bad.append(A)
        if not bad:return x
        if not left:return None
        bad.sort(key=lambda A:(len(A),A))
        if packing:
            used=set();count=0
            for A in bad:
                if used.isdisjoint(A):used.update(A);count+=1
            if count>left:prunes+=1;return None
        for j in bad[0]:
            y=walk(D|(1<<j),left-1)
            if y is not None:return y
        return None
    y=walk(0,min(r,n))
    if y is not None:assert accepts(F,y) and (a^y).bit_count()<=r
    return y,calls,prunes


def original7(t,off):
    S=[[0,4,5,6],[0,1,4,6],[0,4,5,7],[0,4,5,6],[0,4,5,6],[0,1,2,7],[0,3,4,6]]
    F=[tuple(-(j+1) if p>>k&1 else j+1 for k,j in enumerate((i,(i+1)%7,(i+3)%7))) for i,A in enumerate(S) for p in range(8) if p not in A]
    return [tuple((1 if (l>0)^bool(t>>(abs(l)-1)&1) else -1)*(abs(l)+off) for l in c) for c in F]


def main():
    rng=Random(78);checks=success=prunes=0
    for n in range(1,8):
        for _ in range(30):
            F=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(4))) for _ in range(rng.randrange(15))]
            S=[x for x in range(1<<n) if accepts(F,x)]
            for a in (0,(1<<n)-1,rng.randrange(1<<n)):
                for r in range(n+1):
                    want=any((a^x).bit_count()<=r for x in S)
                    for packing in (False,True):
                        y,c,p=repair(F,n,a,r,packing)
                        assert (y is not None)==want and c<=(3**(r+1)-1)//2
                        checks+=1;success+=want;prunes+=p
    print('random sources',210,'ball comparisons',checks,'successes',success,'packing prunes',prunes)
    assert all([x for x in range(128) if accepts(original7(1<<j,0),x)]==[1<<j] for j in range(7))
    for g in (4,8,16,32,64):
        n=7*g;r=g.bit_length()-1
        F=[c for i in range(g) for c in original7(1 if i<r else 0,7*i)]
        # Connect all blocks by a clique on their original second bits, known zero
        # in the analytical control; decoder receives only the resulting clauses.
        F += [(-(7*i+2),-(7*j+2)) for i in range(g) for j in range(i+1,g)]
        x=sum(1<<(7*i) for i in range(r))
        y,c,p=repair(F,n,0,r);assert y==x
        z,b,q=repair(F,n,0,r-1);assert z is None
        print('connected',n,'clique',g,'radius',r,'calls',c,'prunes',p,'smaller ball calls',b,'prunes',q)
    # Dense violated-clause packing: no radius-r witness even though source inhabited.
    for n in (8,32,128):
        F=[(j,) for j in range(1,n+1)]
        y,c,p=repair(F,n,0,n-1);assert y is None and (c,p)==(1,1)
    print('all passed')


if __name__=='__main__':main()
