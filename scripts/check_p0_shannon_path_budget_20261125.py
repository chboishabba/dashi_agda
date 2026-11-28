"""Section 75: source-conditioned Shannon routing with exact path budgets."""
from fractions import Fraction as Q
from random import Random


def sat(F,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in F)


def simplify(F,x,assigned):
    out=[]
    for c in F:
        c=set(c)
        if any(-l in c for l in c):continue
        if any(assigned>>(abs(l)-1)&1 and bool(x>>(abs(l)-1)&1)==(l>0) for l in c):continue
        out.append(tuple(sorted(l for l in c if not assigned>>(abs(l)-1)&1)))
    return out


def propagate(F,x,a):
    while True:
        R=simplify(F,x,a)
        if () in R:return None
        units=sorted(c[0] for c in R if len(c)==1)
        if not units:return x,a,R
        l=units[0];v=1<<(abs(l)-1);a|=v
        if l>0:x|=v
        else:x&=~v


def prefer(R,j,mode):
    if mode==0:return 0
    if mode==1:return 1
    p=sum(j in c for c in R);m=sum(-j in c for c in R)
    return int(p>m) if mode==2 else int(p>=m)


def search(F,n,threshold,mode=0,all_leaves=False):
    stats=[0,0,0];leaves=[];alpha=Q(1,2*max(1,n))
    def walk(x,a,w):
        stats[0]+=1
        if w<threshold:stats[1]+=1;return False
        state=propagate(F,x,a)
        if state is None:return False
        x,a,R=state
        if a==(1<<n)-1:
            assert sat(F,x);leaves.append((x,w));return True
        j=next(i for i in range(1,n+1) if not a>>(i-1)&1)
        p=prefer(R,j,mode);v=1<<(j-1)
        for b,t in ((p,1-alpha),(1-p,alpha)):
            stats[2]+=1
            if walk(x|v if b else x&~v,a|v,w*t) and not all_leaves:return True
        return False
    walk(0,0,Q(1));return leaves,stats


def path(F,n,x,mode):
    a=0;y=0;k=0;steps=0;alpha=Q(1,2*max(1,n))
    while True:
        state=propagate(F,y,a)
        if state is None:return Q(0),k,steps
        y,a,R=state
        if (y^x)&a:return Q(0),k,steps
        if a==(1<<n)-1:return alpha**k*(1-alpha)**(steps-k),k,steps
        j=next(i for i in range(1,n+1) if not a>>(i-1)&1);v=1<<(j-1)
        b=int(bool(x&v));k+=b!=prefer(R,j,mode);steps+=1;a|=v;y|=x&v


def original7(t=0,offset=0):
    S=[[0,4,5,6],[0,1,4,6],[0,4,5,7],[0,4,5,6],[0,4,5,6],[0,1,2,7],[0,3,4,6]]
    F=[tuple(-(j+1) if p>>k&1 else j+1 for k,j in enumerate((i,(i+1)%7,(i+3)%7))) for i,A in enumerate(S) for p in range(8) if p not in A]
    return [tuple((1 if (l>0)^bool(t>>(abs(l)-1)&1) else -1)*(abs(l)+offset) for l in c) for c in F]


def main():
    rng=Random(75);checks=0;paths=0
    for n in range(1,8):
        for _ in range(25):
            F=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(4))) for _ in range(rng.randrange(14))]
            truth=[x for x in range(1<<n) if sat(F,x)]
            for mode in range(4):
                W={x:path(F,n,x,mode)[0] for x in truth};assert all(W.values()) and sum(W.values())<=1
                for threshold in (Q(1,2),Q(1,2*n),Q(1,2*(2*n)**2)):
                    L,S=search(F,n,threshold,mode,True)
                    assert dict(L)=={x:w for x,w in W.items() if w>=threshold}
                    assert len(dict(L))==len(L) and S[0]<=1+2*n*(1//threshold)
                    checks+=1;paths+=len(L)
    print('random threshold comparisons',checks,'accepted path receipts',paths)
    for g in (1,2,4,8,16):
        n=7*g;F=[c for i in range(g) for c in original7(0,7*i)]
        w,k,t=path(F,n,0,0);assert k==0
        L,S=search(F,n,Q(1,2),0);assert L and L[0][0]==0
        print('zero route',n,k,t,S)
        # Fixed alternate policy produces all ones, with no forced-bit proof.
        H=[c for i in range(g) for c in original7(127,7*i)];x=(1<<n)-1
        w,k,t=path(H,n,x,0);w1,k1,t1=path(H,n,x,1)
        assert k>=g and k1==0
        L,S=search(H,n,Q(1,2),1);assert L and L[0][0]==x
        print('opposite route',n,k,k1,t1,S)
    for n in (16,32,64,128):
        # One early discrepancy then exact source-derived propagation along chain.
        F=[(1,2),(1,-2)] + [(-i,i+1) for i in range(1,n)]
        w,k,t=path(F,n,(1<<n)-1,0);assert (k,t)==(1,1)
        L,S=search(F,n,Q(1,4*n),0);assert L and L[0][0]==(1<<n)-1
        print('one discrepancy',n,k,t,str(w),S)

if __name__=='__main__':main()
