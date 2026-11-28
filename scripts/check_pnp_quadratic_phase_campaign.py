"""Restartable independent original-source and quadratic oracle."""
from itertools import product
from fractions import Fraction as Q
from random import Random
from pathlib import Path
from collections import Counter
import argparse,json
from check_pnp_quadratic_phase import gauss,recognize,evaluate,structured_contrast
from check_pnp_dual_syndrome_fourier import Z,OMEGA,add,norm,phase,contrast


def case(i):
    rng=Random(3692821+i);n=i%8;r=i%4;R=tuple(j for j in range(n) if rng.randrange(5));t=tuple(rng.randrange(3) for _ in range(r));o=i%3;w=Q((-1)**i*(1+i%3),3**(i%4))
    groups=[R] if i%2 else [R[j:j+3] for j in range(0,len(R),3)]
    F=tuple(tuple((j+1)*rng.choice((-1,1)) for j in rng.sample(G,rng.randrange(min(4,len(G))+1))) for G in groups for _ in range(i%5))
    cols=tuple(tuple(rng.randrange(3) for _ in range(r+1)) for j in range(n));H=[0]*3
    for b in product(range(2),repeat=len(R)):
        x=dict(zip(R,b))
        if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and tuple(sum(cols[j][a]*x[j] for j in R)%3 for a in range(r))==t:H[(o+sum(cols[j][-1]*x[j] for j in R))%3]+=1
    s=Counter(fixtures=1,points=2**len(R));v=tuple(w*(3*h-sum(H)) for h in H)
    for cap in (1,16,64,1024):
        ans=structured_contrast(F,cols,t,o,R,w,6,cap,100000)
        s['attempts']+=1
        if ans is None:s['refused']+=1;continue
        a,b,st=ans;assert a==b==v,(i,cap,v,ans);s['exact']+=1;s['normal_queries']+=st['normal_queries'];s['structured']+=st['structured'];s['exceptional']+=st['exceptional'];s['branches']+=st['branches'];s['work']+=st['work']
    d=i%7;P={():rng.randrange(3)};P.update({(j,):rng.randrange(3) for j in range(d)});P.update({(j,k):rng.randrange(3) for j in range(d) for k in range(j,d)})
    z=Z
    for x in product(range(3),repeat=d):z=add(z,OMEGA[evaluate(P,x)])
    assert gauss(P,d,lambda _:None)==z;s['gauss']+=1;s['gauss_points']+=3**d
    return s


def chirps(k,opposite):
    F=tuple((-(2*j+1),-(2*j+2)) for j in range(2*k))
    cols=tuple(tuple((1+j%2) if h==(j//2)%k else 0 for h in range(k))+((1 if j<2*k or not opposite else 2),) for j in range(4*k))
    a,b,st=structured_contrast(F,cols,(0,)*k,0,range(4*k),Q(1),2,1,1000000)
    # Independent axis sum: phases x^2 +- (-x)^2; repeated convolution.
    h=[1,0,0];axis=(3,0,0) if opposite else (1,0,2)
    for _ in range(k):h=[sum(h[j]*axis[(i-j)%3] for j in range(3)) for i in range(3)]
    assert a==b==tuple(3*x-sum(h) for x in h)
    return dict(k=k,opposite=opposite,hist=h,stats=st)


def mixed(k):
    # Connected global interaction: sum_{i<j} x_i x_j on F3^k.
    # Each local 6-bit CNF gadget encodes two trits and their product.
    # Affine rows equate every copy to a master trit; phase is read once.
    edges=[(i,j) for i in range(k) for j in range(i+1,k)];r=2*len(edges);F=[];cols=[]
    allowed=set()
    enc=lambda x:(int(x==1),int(x==2))
    for x,y in product(range(3),repeat=2):allowed.add(enc(x)+enc(y)+enc(x*y%3))
    for i in range(k):
        F.append((-(2*i+1),-(2*i+2)))
        for a in (1,2):cols.append(tuple((-a)%3 if v==i else 0 for e in edges for v in e)+(0,))
    for e,(i,j) in enumerate(edges):
        b=len(cols)
        for x in product(range(2),repeat=6):
            if x not in allowed:F.append(tuple((b+v+1)*(1 if not a else -1) for v,a in enumerate(x)))
        for v in range(6):cols.append(tuple(v%2+1 if v<4 and h==2*e+v//2 else 0 for h in range(r))+((v%2+1) if v>=4 else 0,))
    a,b,st=structured_contrast(tuple(F),tuple(cols),(0,)*r,0,range(len(cols)),Q(1),6,1,10000000)
    # Independent DP over accumulated sum and pair-product phase.
    D={(0,0):1}
    for _ in range(k):
        E=Counter()
        for (s,q),v in D.items():
            for x in range(3):E[((s+x)%3,(q+s*x)%3)]+=v
        D=E
    h=[sum(D.get((s,d),0) for s in range(3)) for d in range(3)]
    assert a==b==tuple(3*x-sum(h) for x in h)
    return dict(k=k,variables=len(cols),affine_rows=r,clauses=len(F),hist=h,stats=st)


def controls():
    # Reject a cubic phase and a nonaffine support; accept translated support.
    T={x:OMEGA[x[0]*x[1]*x[2]%3] for x in product(range(3),repeat=3)}
    assert recognize(T,3,lambda _:None) is None
    assert recognize({(0,):OMEGA[0],(1,):OMEGA[1]},1,lambda _:None) is None
    assert recognize({(1,i):OMEGA[i*i%3] for i in range(3)},2,lambda _:None) is not None
    n=32;F=tuple((i+1,i+2) for i in range(n-1));cols=((1,1),)*n
    a,b,st=structured_contrast(F,cols,(1,),0,range(n),Q(1),6,64,200000,1,3)
    D={(1,0):1}
    for _ in range(n):
        E=Counter()
        for (p,t),v in D.items():
            for x in (0,1):
                if p or x:E[x,(t+x)%3]+=v
        D=E
    c=sum(D.get((p,1),0) for p in (0,1));assert a==b==(-c,2*c,-c) and st['normal_queries']==3
    assert structured_contrast(F,cols,(1,),0,range(n),Q(1),6,64,1,1,3) is None
    assert structured_contrast(((1,2),),((1,0),(1,0)),(0,),0,(0,1),Q(1),2,1,10000) is None
    return dict(connected=dict(n=n,count=c,stats=st),chirps=[chirps(k,o) for k in (1,4,16,64) for o in (True,False)],mixed=[mixed(k) for k in (3,5,8,12)])


def main():
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=512);p.add_argument('--batch',type=int,default=64);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args();assert a.batch>0 and a.total>=0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(version=1,total=a.total,next=0,counts={});assert s['version']==1 and s['total']==a.total;c=Counter(s['counts'])
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        c.update(case(i));s.update(next=i+1,counts=dict(c));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    if s['next']==a.total:s['controls']=controls();a.checkpoint.write_text(json.dumps(s))
    print(json.dumps(s))
if __name__=='__main__':main()
