"""Exact algebraic controls; not Lean kernel or PDE acceptance.
Extraction mode uses the actual new phase core with independent graph
and enumerative quadratic donors, disabling old affine/square reductions.
Production mode imports the original full compiler.
"""
from fractions import Fraction as Q
from itertools import product, combinations_with_replacement
from random import Random
from pathlib import Path
from math import prod, factorial
import argparse
import sympy as S
from pnp_phase_separator_exact import choose_separator, restrict_axis, phase_key
if not __debug__:raise SystemExit('refusing optimized execution')
Z=(0,0);ONE=(1,0);OMEGA=((1,0),(0,1),(-1,-1))
def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,b):
    x,y=a;u,v=b;return x*u-y*v,x*v+y*u-y*v
def phase(a,d):return mul(a,OMEGA[d%3])
def value(P,x):return sum(a*prod(x[i] for i in m) for m,a in P.items())%3
def exact(P,n):
    z=Z
    for x in product(range(3),repeat=n):z=add(z,OMEGA[value(P,x)])
    return z
class Refusal(Exception):pass

def reference_pieces(P,n,pay):
    active=set(i for m,a in P.items() if a%3 for i in m);groups=[]
    for m,a in P.items():
        if not m or not a%3:continue
        I=set(m);old=[G for G in groups if I&G]
        for G in old:I|=G;groups.remove(G)
        groups.append(I)
    soft=set();pieces=[]
    for G in groups:
        T={m:a for m,a in P.items() if m and set(m)<=G and a%3}
        if any(len(m)>2 for m in T):pieces.append(G)
        else:soft|=G
    if soft:pieces.append(soft)
    out=[]
    for G in pieces:
        idx={v:i for i,v in enumerate(sorted(G))}
        out.append((len(G),{tuple(idx[i] for i in m):a for m,a in P.items() if m and set(m)<=G and a%3}))
    return out,n-len(active),P.get((),0)%3

def phase_controls(core):
    if core:
        env=dict(globals(),independent_phase_pieces=reference_pieces,affine_axis_reduce=lambda *a:None,
                 quadratic_axis_reduce=lambda *a:None,gauss=lambda P,n,pay:exact(P,n))
        exec(compile(Path(core).read_text(),str(core),'exec'),env);calc=env['conditional_gauss'];refuse=Refusal
    else:
        from check_pnp_quadratic_phase import conditional_gauss as calc,Refusal as refuse
    rng=Random(36914);count=0;pay=lambda _:None
    for n in range(1,7):
        mons=[m for k in range(4) for m in combinations_with_replacement(range(n),k) if all(m.count(i)<=2 for i in set(m))]
        for _ in range(12):
            P={m:rng.randrange(1,3) for m in mons if rng.randrange(4)==0}
            assert calc(P,n,pay,[3**n])==exact(P,n);count+=1
            for j in range(n):
                for v in range(3):
                    R=restrict_axis(P,n,j,v,pay)
                    for x in product(range(3),repeat=n-1):
                        assert value(R,x)==value(P,x[:j]+(v,)+x[j:]);count+=1
    P={(0,1,2):1,(3,4,5):1,(2,6):1,(3,6):2,(6,6):1}
    assert choose_separator(P,7,pay)==6;count+=1
    assert calc(P,7,pay,[3**7])==exact(P,7);count+=1
    memo={};b=[3**7];v=calc(P,7,pay,b,memo);left=b[0]
    for d in range(3):
        assert calc({**P,():d},7,pay,b,memo)==phase(v,d);count+=1
        assert b[0]==left;count+=1
    assert phase_key(P,7,pay)==phase_key({**P,():2},7,pay);count+=1
    assert phase_key(P,7,pay)!=phase_key(P,8,pay);count+=1
    memo={}
    try:calc({(0,0):1},1,pay,[0],memo)
    except refuse:count+=1
    else:raise AssertionError('zero cap escaped')
    assert not memo;count+=1
    for k in (1,2,4,8,16,32):
        P={(3*i,3*i+1,3*i+2):1 for i in range(k)}
        b=[3];assert calc(P,3*k,pay,b)==(15**k,0);count+=1
    return count

def bsd_hodge():
    a,b,u,Y=S.symbols('a b u Y');C=u*(u+a)*(u+b)
    m=(3*u*u+2*(a+b)*u+a*b)/(2*Y);x=m*m-a-b-2*u;y=-Y-m*(x-u)
    r=(a*b-u*u)/(2*Y)*(-(u*u+2*a*u+a*b)/(2*Y))*(-(u*u+2*b*u+a*b)/(2*Y))
    coeff=-8*Y**2+4*a*a*b+8*a*a*u+4*a*b*b+20*a*b*u+28*a*u*u+8*b*b*u+28*b*u*u+28*u**3
    assert S.cancel(8*Y**3*(r+y)-coeff*(Y*Y-C))==0
    count=1
    v=S.symbols('v');xx=v+a/v;D=xx**7-7*a*xx**5+14*a*a*xx**3-7*a**3*xx
    assert S.cancel(v*v-xx*v+a)==0;count+=1
    assert S.cancel(v**14-D*v**7+a**7)==0;count+=1
    assert S.cancel((xx-v)/a-1/v)==0;count+=1
    for e in product((-1,1),repeat=2):
        row=(*e,prod(e));assert prod(row)==1;count+=1
        for f in product((-1,1),repeat=2):
            other=(*f,prod(f));assert prod(x*y for x,y in zip(row,other))==1;count+=1
    return count

def interval_and_joint():
    rng=Random(369);count=0
    for _ in range(400):
        dl=Q(rng.randrange(0,6),10);du=dl+Q(rng.randrange(0,4),10)
        zl=Q(rng.randrange(0,4),20);zu=zl+Q(rng.randrange(0,3),20)
        cu,wu,ddu,dzu=[Q(rng.randrange(0,6),100) for _ in range(4)];H=Q(rng.randrange(0,5),4)
        faces=(dl-cu,1-du,Q(1,4)-zu,zl-ddu-cu*wu);margin=min(faces)-dzu*H
        for j in range(4):assert margin+dzu*H<=faces[j];count+=1
        assert margin+dzu*H==min(faces);count+=1
        for _ in range(4):
            d=dl+(du-dl)*Q(rng.randrange(5),4);z=zl+(zu-zl)*Q(rng.randrange(5),4)
            c=cu*Q(rng.randrange(5),4);w=wu*Q(rng.randrange(5),4)
            h=[Q(rng.randrange(0,10),7) for _ in range(4)];M=sum(h)
            x0sq=H*M*Q(rng.randrange(5),4)
            dens=sum(x*y for x,y in zip((d-c,1-d,Q(1,4)-z,z-ddu-c*w),h))-dzu*x0sq
            assert dens>=margin*M;count+=1
    for n in range(1,30):
        e=[Q(j,3*n*n) for j in range(n)];d=[Q(n-j,7*n*n) for j in range(n)];B=sum(e)+2*sum(d)
        for k in range(n+1):assert sum(e[:k])+2*sum(d[k:])<=B;count+=1
    return count

def ym_series():
    count=0
    for n in range(80):assert factorial(n+2)>=2**(n+1);count+=1
    for j in range(1,65):
        r=Q(j,128);tail=sum(r**(n+1)/factorial(n+2) for n in range(24))
        assert tail<=r/(2-r)<=r;count+=1
        assert 1/(1-r)<=2;count+=1
        assert r/(1-r)<=2*r;count+=1
    x=S.Matrix(S.symbols('x0:3'));h=S.Matrix(S.symbols('h0:3'));z=2*x.cross(h)
    assert S.expand(z.dot(z)-4*(x.dot(x)*h.dot(h)-x.dot(h)**2))==0;count+=1
    return count

def signed_fold():
    rng=Random(36914);count=0;K=list(product(range(-1,2),repeat=3));O=(0,0,0);KS=set(K)
    for _ in range(3):
        U={O:S.zeros(3,1)}
        for k in K:
            if k in U:continue
            p=S.Matrix(k);z=S.Matrix([rng.randrange(-2,3)+S.I*rng.randrange(-2,3) for _ in range(3)])
            v=(z-p*(p.dot(z)/p.dot(p))).expand();U[k]=v;U[tuple(-x for x in k)]=v.conjugate()
        pairs=[]
        for p,q in product(K,repeat=2):
            k=tuple(x+y for x,y in zip(p,q))
            if k not in KS:continue
            c=S.re((-S.I*S.Matrix(q).dot(U[p])*U[q]).dot(U[k].conjugate())).expand()
            pairs.append((p,q,k,c))
        C={(p,q):c for p,q,k,c in pairs}
        for p,q,k,c in pairs:
            assert C[(tuple(-x for x in p),k)]==-c;count+=1
        for _ in range(4):
            w={k:rng.randrange(0,10) for k in K}
            assert 2*sum(w[k]*c for p,q,k,c in pairs)==sum((w[k]-w[q])*c for p,q,k,c in pairs);count+=1
    return count

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--extracted-core');a=p.parse_args()
    counts=dict(pnp=phase_controls(a.extracted_core),bsd_hodge=bsd_hodge(),interval_joint=interval_and_joint(),ym=ym_series(),signed_fold=signed_fold())
    print('SymPy',S.__version__,counts,'TOTAL',sum(counts.values()),'PASS')
