#!/usr/bin/env python3
"""Exact rational finite audit of the user-specified alternating nine-site braid."""
from fractions import Fraction as Q
from itertools import combinations

PATH=((0,0),(0,1),(1,1),(2,1),(2,2),(1,2),
      (0,2),(0,1),(1,1),(2,1),(2,0),(1,0))
SHIFTS=(0,4,8)
PAIRS=tuple(combinations(range(3),2))

def pos(a,t):
    return PATH[(t+SHIFTS[a])%12]

def mix(a,t,u):
    x,y=pos(a,t),pos(a,t+1)
    return tuple(Q(v)+u*(w-v) for v,w in zip(x,y))

def collision():
    for t in range(12):
        for a,b in PAIRS:
            d0=[Q(x-y) for x,y in zip(pos(a,t),pos(b,t))]
            d1=[Q(x-y) for x,y in zip(pos(a,t+1),pos(b,t+1))]
            v=[y-x for x,y in zip(d0,d1)]
            candidates={Q(0),Q(1)}
            for x,dx in zip(d0,v):
                if dx: candidates.add(-x/dx)
            for u in candidates:
                if 0<=u<=1 and all(x+u*dx==0 for x,dx in zip(d0,v)):
                    return t,a,b,u
    return None

def winding(a,b):
    n=0
    for t in range(12):
        p,q=pos(a,t),pos(b,t)
        r,s=pos(a,t+1),pos(b,t+1)
        x0,y0=Q(p[1]-q[1]),Q(p[0]-q[0])
        x1,y1=Q(r[1]-s[1]),Q(r[0]-s[0])
        if (y0<=0<y1) or (y1<=0<y0):
            u=-y0/(y1-y0)
            if x0+u*(x1-x0)>0:
                n+=1 if y1>y0 else -1
    return n

def crossings():
    # A regular projection: horizontal coordinate = col+row/7
    project=lambda p: Q(p[1])+Q(p[0],7)
    result=[]
    for t in range(12):
        start=[pos(k,t) for k in range(3)]
        end=[pos(k,t+1) for k in range(3)]
        order=sorted(range(3),key=lambda k: project(start[k]))
        assert len({project(v) for v in start})==3
        assert len({project(v) for v in end})==3
        for a,b in PAIRS:
            d0=project(start[a])-project(start[b])
            d1=project(end[a])-project(end[b])
            if d0*d1>=0: continue
            u=d0/(d0-d1)
            assert 0<u<1
            pa,pb=mix(a,t,u),mix(b,t,u)
            da=pa[0]-pa[1]/11
            db=pb[0]-pb[1]/11
            assert da!=db
            ia,ib=order.index(a),order.index(b)
            assert abs(ia-ib)==1
            left=a if d0<0 else b
            positive=(da>db)==(left==a)
            result.append((Q(t)+u, min(ia,ib)+1, 1 if positive else -1))
    result.sort()
    assert len({event[0] for event in result})==len(result)
    return [(g,s) for _,g,s in result]

def clearance_squared():
    """Minimum squared pair separation over all concurrent affine segments."""
    best=None
    for t in range(12):
        for a,b in PAIRS:
            d0=[Q(x-y) for x,y in zip(pos(a,t),pos(b,t))]
            d1=[Q(x-y) for x,y in zip(pos(a,t+1),pos(b,t+1))]
            v=[y-x for x,y in zip(d0,d1)]
            denom=sum(x*x for x in v)
            u=max(Q(0),min(Q(1),-sum(x*y for x,y in zip(d0,v))/denom)) if denom else Q(0)
            val=sum((x+u*y)**2 for x,y in zip(d0,v))
            best=val if best is None else min(best,val)
    return best

def main():
    assert len(PATH)==12
    assert all(len({pos(a,t) for a in range(3)})==3 for t in range(12))
    assert collision() is None, collision()
    assert clearance_squared()==Q(1), clearance_squared()
    assert all(pos(a,t+4)==pos((a+1)%3,t)
               for t in range(12) for a in range(3))
    assert [winding(a,b) for a,b in PAIRS]==[0,0,0]
    word=crossings()
    assert word==[(1,-1),(2,1)]*3, word
    print('PASS exact: discrete distinctness; continuous noncollision; C3 phase shift')
    print('PASS exact: min squared pair separation = 1 at all continuous times')
    print('PASS: uniform per-strand perturbation < 1/2 preserves collision avoidance and braid isotopy via straight homotopy')
    print('PASS exact: pairwise winding (0,0,0); projected braid word (s1^-1 s2)^3')
    print('Topological identification of the standard closure: Borromean rings')

if __name__=='__main__':
    main()
