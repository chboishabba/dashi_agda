"""Replay exact extracted production phase core, not a substitute CNF pipeline.
Independent enumeration and a 3-state transfer oracle on connected chains.
"""
import argparse, hashlib, math
from pathlib import Path
from itertools import product, combinations_with_replacement
from random import Random
Z=(0,0);ONE=(1,0);OMEGA=((1,0),(0,1),(-1,-1))

def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]-a[1]*b[1]
def phase(a,d):return mul(a,OMEGA[d%3])
class Refusal(Exception):pass

def exact(P,n):
    z=Z
    for x in product(range(3),repeat=n):
        e=sum(a*math.prod(x[i] for i in m) for m,a in P.items())%3
        z=add(z,OMEGA[e])
    return z

def chain(k):
    # Eliminate x locally by direct enumeration; propagate y by 3-state transfer.
    w=[Z]*3
    for y in range(3):
        for x in range(3):w[y]=add(w[y],OMEGA[(x*x+x*y*y)%3])
    v=w[:]
    for _ in range(k-1):
        nxt=[Z]*3
        for y in range(3):
            for z in range(3):nxt[y]=add(nxt[y],mul(w[y],phase(v[z],z*y)))
        v=nxt
    return add(v[0],add(v[1],v[2]))

def main(path):
    raw=path.read_text();start=raw.index('def put(');end=raw.find('\ndef recognize(',start)
    core=raw[start:end] if end>=0 else raw[start:]
    print('core sha256',hashlib.sha256(core.encode()).hexdigest())
    env=dict(globals());exec(compile(core,str(path),'exec'),env)
    calc=env['conditional_gauss'];reduce=env['quadratic_axis_reduce'];pieces=env['independent_phase_pieces'];noop=lambda _:None
    rng=Random(36911);count=0
    for n in range(2,8):
        mons=[m for k in range(4) for m in combinations_with_replacement(range(n),k) if all(m.count(i)<=2 for i in set(m))]
        for _ in range(40):
            P={m:rng.randrange(1,3) for m in mons if rng.randrange(4)==0}
            P[(0,0)]=1
            assert calc(P,n,noop,[3**n])==exact(P,n);count+=1
            r=reduce(P,n,noop)
            if r is not None:
                f,k,Q=r;assert mul(f,exact(Q,k))==exact(P,n);count+=1
    # Genuine quartic escape: square of yz+uv is not a cubic function.
    P={(0,0):1,(0,1,2):1,(0,3,4):1}
    assert reduce(P,5,noop) is None;count+=1
    assert calc(P,5,noop,[243])==exact(P,5);count+=1
    for k in (2,3,4,8,16,32,64,128):
        P={(2*j,2*j):1 for j in range(k)}
        P.update({(2*j,2*j+1,2*j+1):1 for j in range(k)})
        P.update({(2*j+1,2*j+3):1 for j in range(k-1)})
        assert len(pieces(P,2*k,noop)[0])==1;count+=1
        b=[1];v=calc(P,2*k,noop,b)
        assert v==chain(k) and b[0]==0;count+=1
        if k<=4:assert v==exact(P,2*k);count+=1
    print(f'{count}/{count} connected square controls PASS')
if __name__=='__main__':
    if not __debug__:raise SystemExit('refusing optimized execution')
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);main(p.parse_args().source)
