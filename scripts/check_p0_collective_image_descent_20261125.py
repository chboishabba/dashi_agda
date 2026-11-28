"""Section 83: bounded collective image absorption, exact signed choice reopening."""
from itertools import combinations, product
from functools import reduce
from operator import xor
from random import Random
from collections import Counter
import check_p0_syndrome_image_descent_20261125 as S
import check_p0_dependency_phase_20261125 as D
import check_p0_affine_ideal_weld_20261125 as W
import check_p0_intrinsic_hull_20261125 as A
from check_p0_signed_horn_closure_20261125 import sat


def xsum(xs):return reduce(xor,xs,0)


def collective(C,r,cap,arity=3,B=None):
    def pay(tag,n=1):
        if B is not None:B.pay(tag,n)
    pay('collective_input',1+sum(map(len,C)))
    if any(not O for O in C):return 'UNSAT',None,(0,0,0,r,0,0)
    H=();c=0;left=list(range(len(C)));ledger=[];hist=[0,0,0];work=0
    while True:
        chosen=None
        for size in range(1,arity+1):
            for ids in combinations(left,size):
                # Actual projected support, not its affine envelope.
                pay('collective_probe',1+size)
                base=xsum(C[i][0][1] for i in ids)
                V={0}
                for i in ids:
                    pay('collective_project',1+len(C[i])*(1+r))
                    T={S.rem(t^C[i][0][1],H) for p,t in C[i]}
                    pay('collective_product',len(V)*len(T))
                    work+=len(V)*len(T)
                    V={v^t for v in V for t in T}
                pay('collective_rank',1+len(V)*(1+r)+r*r)
                K=D.basis(V)
                if len(V)==1<<len(K):
                    chosen=(ids,base,K);break
            if chosen is not None:break
        if chosen is None:break
        ids,base,K=chosen
        pay('collective_absorb',1+len(left)+(len(H)+len(K))*(1+r)+r*r)
        ledger.append((ids,H,c));hist[len(ids)-1]+=1
        H=D.basis(H+K);c^=base
        left=[i for i in left if i not in ids]
    # Invoke actual Section82 for remaining projected choices plus target offset.
    pay('collective_remaining',1+sum(len(C[i])*(1+r) for i in left))
    E=[[(p,S.rem(t,H)) for p,t in C[i]] for i in left]+[[(0,S.rem(c,H))]]
    status,P,st=S.contract(E,r,cap,B=B)
    stats=(*hist,r-len(H),st[2],work)
    if status!='SAT':return status,None,stats
    result=[None]*len(C);s=0
    for i,p in zip(left,P):
        pay('collective_lookup',1+len(C[i]))
        t=next(t for q,t in C[i] if q==p)
        result[i]=p;s^=t
    for ids,H0,c0 in reversed(ledger):
        for ps in product(*(C[i] for i in ids)):
            pay('collective_reverse',1+len(ids)+r)
            if not S.rem(s^xsum(t for p,t in ps)^c0,H0):opts=ps;break
        else:raise AssertionError('missing saturated preimage')
        for i,(p,t) in zip(ids,opts):result[i]=p;s^=t
    assert s==0
    return 'SAT',result,stats


def original(F,n,cap=8,arity=3):
    N=W.normalize(F,n)
    if N is None:return 'UNSAT',None,[]
    k,f,R,back,forward,*_=N
    blocks=[(B,sorted(T)) for B,T in R];ranges,comps,rank=D.decompose(blocks)
    rows=[];stats=[];unknown=False
    for ids,rels in comps:
        status,P,st=collective(D.choices(blocks,ranges,ids,rels),len(rels),cap,arity)
        stats.append((len(rels),)+st)
        if status=='UNSAT':return status,None,stats
        if status=='UNKNOWN':unknown=True;continue
        for i,p in zip(ids,P):rows.extend((v,p>>j&1) for j,v in enumerate(blocks[i][0]))
    if unknown:return 'UNKNOWN',None,stats
    p=D.lift(rows);assert p is not None and A.accepted(R,p)
    x=back(p);assert sat(F,x) and forward(x)==(p,0)
    return 'SAT',x,stats


def main():
    rng=Random(83);counts=Counter();nchecks=0
    for r in range(1,7):
        for _ in range(70):
            C=[[(p,rng.randrange(1<<r)) for p in range(rng.randrange(0,6))] for _ in range(rng.randrange(0,7))]
            exist=any(xsum(t for p,t in ps)==0 for ps in product(*C))
            for cap in (0,2,r):
                status,P,st=collective(C,r,cap)
                if status=='SAT':assert exist and xsum(C[i][p][1] for i,p in enumerate(P))==0
                elif status=='UNSAT':assert not exist
                if cap==r:assert (status=='SAT')==exist
                counts[status]+=1;counts['pair']+=st[1];counts['triple']+=st[2];nchecks+=1
    print('syndrome comparisons',nchecks,dict(counts))
    # A pair can saturate even though each support is nonlinear.
    C=[[(0,0),(1,1),(2,2)],[(0,0),(1,1),(2,2)]]
    assert S.contract(C,2,0)[0]=='UNKNOWN'
    assert collective(C,2,0)[2][:5]==(0,1,0,0,0)
    # A triple saturation which no single/pair absorption can detect.
    C=[[(p,t) for p,t in enumerate(T)] for T in ([0,1,2],[0,1,4],[0,2,4])]
    assert collective(C,3,0,2)[0]=='UNKNOWN'
    assert collective(C,3,0,3)[2][:5]==(0,0,1,0,0)
    # Actual multiplicities on an affine support need not be uniform.
    M=Counter(a^b for a,b in product((0,1,2),repeat=2));assert M=={0:3,1:2,2:2,3:2}
    # Density lower bound, with all nonempty sets in a 3-dimensional space.
    subsets=[{j for j in range(8) if mask>>j&1} for mask in range(1,256)]
    den=0
    for P,Q in product(subsets,repeat=2):
        if len(P)+len(Q)<=8:continue
        for t in range(8):assert len(P&{t^q for q in Q})>=len(P)+len(Q)-8;den+=1
    print('density checks',den,'pair multiplicity',dict(M))
    counts=Counter()
    for n in range(1,8):
        for _ in range(25):
            F=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(4))) for _ in range(rng.randrange(11))]
            truth=[x for x in range(1<<n) if sat(F,x)]
            s,x,stats=original(F,n,32);assert (s=='SAT')==bool(truth) and s!='UNKNOWN'
            if truth:assert x in truth
            counts[s]+=1
    print('original CNFs',dict(counts))
    # Actual original 3-CNF: all variables occur twice, every local OR3
    # image nonlinear. A pair shares two coordinates and has one connector each.
    for g in (4,8,16,32):
        n=3*g;F=[]
        for i in range(g):
            a,b=2*i+1,2*i+2;z=2*g+i+1;w=2*g+(i+1)%g+1
            F.extend([(a,b,z),(a,b,w)])
        N=W.normalize(F,n);assert N is not None and N[:2]==(n,0)
        k,f,R,*_=N
        assert S.direct(k,R,0)[0]=='UNKNOWN'
        s,x,stats=original(F,n,0,2);assert s=='SAT' and len(stats)==1
        assert stats[0][0]==3*g and stats[0][2]>0 and stats[0][4:6]==(0,0)
        print('original cycle',n,'raw/single/pair/triple/remaining/effective/work',stats[0])


if __name__=='__main__':main()
