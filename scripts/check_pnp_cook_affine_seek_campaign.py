from check_pnp_cook_affine_seek import *
from random import Random
from collections import Counter

def reference(D):
    # Independent explicit layout of rows, selector blocks and witness bits.
    T,C,w,r=D.T,D.C,D.w,D.r;rows=[[[((t*C+j)*w+i) for i in range(w)] for j in range(C)] for t in range(T+1)]
    S=(T+1)*C*w;selectors=[list(range(S+t*r,S+(t+1)*r)) for t in range(T)];G=S+T*r
    clauses=[]
    for t in range(T):
        for j in range(C-2):
            I=selectors[t]+[v for h in (t,t+1) for k in range(j,j+3) for v in rows[h][k]]
            clauses.extend(tuple((I[i],b) for i,b in c) for c in D.trans)
    init=D.blank*T+D.middle+D.blank*T
    clauses.extend(((i,b),) for i,b in enumerate(init));clauses.append(tuple((G+j,1) for j in range(C)))
    for j in range(C):
        I=[G+j]+rows[T][j];clauses.extend(tuple((I[i],b) for i,b in c) for c in D.acc)
    out=[]
    for c in clauses:
        out.append(6)
        for v,b in c:
            out.append(7)
            if not b:out.append(5)
            out.append(2);out.extend([1]*v);out.append(0)
        out.append(3)
    return tuple(out)+(4,)

def main():
    C=Counter()
    for i in range(128):
        rng=Random(3692831+i);T=i%5;w=1+i%3;r=1+i%2
        def clauses(N):return tuple(tuple((j,rng.randrange(2)) for j in rng.sample(range(N),rng.randrange(min(N,4)+1))) for _ in range(i%4))
        D=CookSeek(T,w,r,clauses(r+6*w),clauses(1+w),tuple(rng.randrange(2) for _ in range(w)),tuple(rng.randrange(2) for _ in range(w*(3+i%4))))
        want=reference(D);assert D.length()==len(want)
        for k,t in enumerate(want):
            assert D.token(k)==t
            if k%7==0:
                for b in range(3):assert D.bit(3*k+b)==(t>>(2-b))&1;C['bit_checks']+=1
        assert D.token(-1) is None and D.token(len(want)) is None and D.bit(3*len(want)) is None
        C['fixtures']+=1;C['tokens']+=len(want)
    D=CookSeek(10**12,3,2,(((0,0),(2,1),(19,0)),),(((0,0),(1,1)),),(0,1,0),(0,1,0,1,1,0,0,1,0))
    for t,j in ((0,0),(D.T-1,D.J-1),(D.T//2,D.J//2)):
        k=D.transition_prefix(t)+D.window_prefix(t,j);assert D.token(k)==6
        want=tuple(v for i,b in D.trans[0] for v in (D.trans_coord(i,t,j),))
        assert D.token(k+1)==7 and D.token(k+2)==5 and D.token(k+3)==2 and D.token(k+4+want[0])==0
    for k in (D.transition_prefix(D.T),D.transition_prefix(D.T)+D.initial_prefix(D.R),D.length()-1):assert D.token(k) in (6,4)
    print(dict(C,huge_T=D.T,huge_columns=D.C,huge_tokens=str(D.length()),huge_bits=str(D.length()*3)))
if __name__=='__main__':main()
