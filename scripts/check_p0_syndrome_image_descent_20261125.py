"""Section 82: exact local syndrome image absorption and reverse witness lift."""
from itertools import product
from random import Random
import check_p0_dependency_phase_20261125 as D
import check_p0_affine_ideal_weld_20261125 as W
import check_p0_intrinsic_hull_20261125 as A
from check_p0_signed_horn_closure_20261125 import sat


def rem(x,H):
    for h in H:
        if x>>(h.bit_length()-1)&1:x^=h
    return x


def contract(C,r,cap):
    # C lists (original local option, full dependency syndrome) pairs.
    if any(not O for O in C):return 'UNSAT',None,(0,r,0,0,0)
    H=();c=0;left=list(range(len(C)));ledger=[];rounds=0
    while True:
        for i in left:
            O=C[i];t0=O[0][1]
            V={rem(t^t0,H) for p,t in O};K=D.basis(V)
            if len(V)!=1<<len(K):continue
            ledger.append((i,H,c));H=D.basis(H+tuple(t^t0 for p,t in O));c^=t0
            left.remove(i);rounds+=1;break
        else:break
    base=0;opts=[]
    for i in left:
        t0=C[i][0][1];base^=t0
        opts.append([(p,rem(t^t0,H),t) for p,t in C[i]])
    target=rem(c^base,H);K=D.basis(v for O in opts for p,v,t in O);w=len(K)
    stats=(rounds,r-len(H),w,len(left),0)
    if rem(target,K):return 'UNSAT',None,stats
    if w>cap:return 'UNKNOWN',None,stats
    M={0:()};work=0
    for O in opts:
        N={}
        for s,ps in M.items():
            for p,v,t in O:
                work+=1;N.setdefault(s^v,ps+((p,t),))
        M=N
    stats=stats[:-1]+(work,)
    if target not in M:return 'UNSAT',None,stats
    result=[None]*len(C);s=0
    for i,(p,t) in zip(left,M[target]):result[i]=(p,t);s^=t
    for i,H0,c0 in reversed(ledger):
        p,t=next((p,t) for p,t in C[i] if not rem(s^t^c0,H0))
        result[i]=(p,t);s^=t
    assert s==0 and all(pair in O for pair,O in zip(result,C))
    return 'SAT',[p for p,t in result],stats


def direct(k,R,cap=8):
    # Section 81 residual already consists of exact local functional tables.
    blocks=[(B,sorted(S)) for B,S in R]
    ranges,comps,rank=D.decompose(blocks);rows=[];stats=[];unknown=False
    for ids,rels in comps:
        status,P,S=contract(D.choices(blocks,ranges,ids,rels),len(rels),cap)
        stats.append((len(rels),)+S)
        if status=='UNSAT':return status,None,stats
        if status=='UNKNOWN':unknown=True;continue
        for i,p in zip(ids,P):rows.extend((v,p>>j&1) for j,v in enumerate(blocks[i][0]))
    if unknown:return 'UNKNOWN',None,stats
    p=D.lift(rows);assert p is not None and A.accepted(R,p)
    return 'SAT',p,stats


def original(F,n,cap=8):
    N=W.normalize(F,n)
    if N is None:return 'UNSAT',None,[]
    k,f,R,back,forward,*_=N
    s,p,stats=direct(k,R,cap)
    if s!='SAT':return s,None,stats
    x=back(p);assert sat(F,x) and forward(x)==(p,0)
    return s,x,stats


def main():
    rng=Random(82);tests=0;solved=0;absorb=0;unknown=0
    for r in range(1,7):
        for _ in range(70):
            C=[[(p,rng.randrange(1<<r)) for p in range(rng.randrange(0,5))] for _ in range(rng.randrange(0,6))]
            exists=any(not __import__('functools').reduce(int.__xor__,(t for p,t in ps),0) for ps in product(*C))
            for cap in (0,2,r):
                s,P,stats=contract(C,r,cap)
                if s=='SAT':assert exists;solved+=1
                elif s=='UNSAT':assert not exists
                else:unknown+=1;assert cap<r
                if cap==r:assert (s=='SAT')==exists
                tests+=1;absorb+=stats[0]
    print('syndrome fixtures',420,'budget comparisons',tests,'SAT',solved,'UNKNOWN',unknown,'absorptions',absorb)
    # A genuinely nonlinear image becomes affine only after another block is absorbed.
    C=[[(0,0),(1,2),(2,3)],[(0,0),(1,1)]]
    s,P,stats=contract(C,2,0);assert s=='SAT' and stats[:4]==(2,0,0,0)
    # Offsets and incompatible neutral sectors, not just zero-containing sets.
    assert contract([[(0,1)],[(0,2)]],2,0)[0]=='UNSAT'
    assert contract([[(0,1),(1,1)],[(0,1)]],2,0)[0]=='SAT'
    # Full-span local nonaffine sets can miss a target: {0,1,2} cannot realize 3.
    assert contract([[(0,0),(1,1),(2,2)],[(0,3)]],2,2)[0]=='UNSAT'
    assert contract([[(0,0),(1,1),(2,2)],[(0,3)]],2,0)[0]=='UNKNOWN'
    ncheck=0;nsat=0
    for n in range(1,8):
        for _ in range(25):
            F=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(4))) for _ in range(rng.randrange(11))]
            S=[x for x in range(1<<n) if sat(F,x)]
            s,x,stats=original(F,n,32);assert (s=='SAT')==bool(S) and s!='UNKNOWN'
            if S:assert x in S;nsat+=1
            ncheck+=1
    print('integrated original CNFs',ncheck,'SAT',nsat,'UNSAT',ncheck-nsat)
    # A single long connected original chain; every OR3 is nonaffine, but each
    # private leaf makes its image on the shared dependency space full affine.
    for g in (8,16,32,64):
        n=2*g+1;F=[(i+1,i+2,g+2+i) for i in range(g)]
        N=W.normalize(F,n);assert N is not None
        k,f,R,*_=N;assert k==n and f==0
        assert all(len(S)==7 for B,S in R)
        status,x,stats=original(F,n,0);assert status=='SAT' and len(stats)==1
        assert stats[0]==(g-1,g,0,0,0,0)
        E=[e for B,S in R for e in A.exclusions(B,S)]
        try:D.decision(E,k,0)
        except OverflowError:pass
        else:raise AssertionError('uncontracted rank cap unexpectedly paid')
        print('original chain',n,'raw dependency rank',g-1,'absorbed',g,'residual rank',0,'DP transitions',0)
    # Independent dense signed observation controls (not original CNF extractor).
    for g in (4,8,16):
        d=4*g;V=[((1<<d)-1)^(1<<i) for i in range(d)];R=[]
        for j in range(g):
            a,b,c,e=V[4*j:4*j+4];R.extend([((a,b,c),{0,2,5}),((a,b,e),{0,3,7})])
        s,p,stats=direct(d,R,2);assert s=='SAT' and p==0
    print('dense original observation singleton controls',3)


if __name__=='__main__':main()
