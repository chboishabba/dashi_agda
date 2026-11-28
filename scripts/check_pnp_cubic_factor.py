"""Actual extracted conditional cubic core; enumerative leaves for small controls.
This is not the full production CNF integration or a physical bit-clock test.
"""
import argparse,hashlib,math
from pathlib import Path
from itertools import product,combinations_with_replacement
from random import Random
Z=(0,0);ONE=(1,0);OMEGA=((1,0),(0,1),(-1,-1))
class Refusal(Exception):pass

def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]-a[1]*b[1]
def phase(a,d):return mul(a,OMEGA[d%3])
def put(P,m,a):
    z=(P.get(m,0)+a)%3
    if z:P[m]=z
    else:P.pop(m,None)
def exact(P,n):
    z=Z
    for x in product(range(3),repeat=n):
        e=sum(a*math.prod(x[i] for i in m) for m,a in P.items())%3
        z=add(z,OMEGA[e])
    return z

def gauss(P,n,pay):
    assert all(len(m)<=2 for m in P)
    pay(3**n)
    return exact(P,n)

def main(path):
    raw=path.read_text()
    start=raw.index('def put(');end=raw.find('\ndef recognize(',start)
    core=raw[start:end] if end>=0 else raw[start:]
    print('core bytes',len(core.encode()),'sha256',hashlib.sha256(core.encode()).hexdigest())
    env=dict(globals());exec(compile(core,str(path),'exec'),env)
    actual_gauss=env['gauss'];env['gauss']=gauss
    calc=env['conditional_gauss'];pieces=env['independent_phase_pieces'];noop=lambda _:None
    rng=Random(3699);count=0
    for n in range(1,8):
        mons=[m for k in range(4) for m in combinations_with_replacement(range(n),k) if all(m.count(i)<=2 for i in set(m))]
        for _ in range(24):
            P={m:a for m in mons if rng.randrange(3)==0 and (a:=rng.randrange(1,3))}
            assert calc(P,n,noop,[3**n])==exact(P,n);count+=1
    for k in (1,2,4,8,16,32,64):
        P={(3*j,3*j+1,3*j+2):1 for j in range(k)};b=[3*k]
        assert calc(P,3*k,noop,b)==(15**k,0);count+=1
        assert b[0]==0;count+=1
        assert calc({**P,():2},3*k+2,noop,[3*k])==phase((9*15**k,0),2);count+=1
    env['gauss']=actual_gauss
    for k in (2,3,4,8,16,32,64):
        P={(3*j,3*j+1,3*j+2):1 for j in range(k)}
        for j in range(k-1):
            P[(3*j,3*k+j)]=1;P[(3*(j+1),3*k+j)]=2
        b=[3]
        assert len(pieces(P,4*k-1,noop)[0])==1;count+=1
        assert calc(P,4*k-1,noop,b)==(3**(k-1)*(3**(2*k)+2*3**k),0);count+=1
        assert b[0]==0;count+=1
    P={(0,1,2):1,(3,4,5):1,(2,3):1}
    assert len(pieces(P,6,noop)[0])==1;count+=1
    assert calc(P,6,noop,[729])==exact(P,6);count+=1
    try:calc({(0,1,2):1,(3,4,5):1},6,noop,[5])
    except Refusal:count+=1
    else:raise AssertionError('shared cap escaped')
    print(f'{count}/{count} cubic factor controls PASS')

if __name__=='__main__':
    if not __debug__:raise SystemExit('refusing optimized execution')
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);main(p.parse_args().source)
