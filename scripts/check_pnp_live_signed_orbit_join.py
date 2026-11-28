"""Live boundary and certified source orbit contraction.
Classical factor DP and group orbit counting; hyperfabric attachment only.
Logical cap, not a physical bit clock. None is transactional refusal.
"""
from itertools import product
from collections import Counter
from random import Random

class Refused(Exception): pass
class Budget:
    def __init__(self, cap):
        if cap < 0: raise ValueError("cap")
        self.cap=cap; self.left=cap
    def pay(self,n):
        if n>self.left: raise Refused()
        self.left-=n
    @property
    def used(self): return self.cap-self.left

def accepts(F,x):
    return all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)

def live_join(F,n,bags,rows,target,B,fixed=None):
    """One owner per clause/variable; forget a boundary only at last use.
    Keep representative original assignments as receipts, not in state key.
    """
    fixed={} if fixed is None else dict(fixed)
    if n<0 or len(rows)!=len(target) or any(len(row)!=n for row in rows):
        raise ValueError("shape")
    if any(not 0<=i<n or b not in (0,1) for i,b in fixed.items()):
        raise ValueError("fixed")
    bags=tuple(tuple(sorted(set(b))) for b in bags)
    B.pay(1+(len(bags)+1)*(n+sum(1+len(c) for c in F)+len(rows)*(n+1)))
    if set().union(*map(set,bags))!=set(range(n)): raise ValueError("cover")
    if any(not 1<=abs(l)<=n for c in F for l in c): raise ValueError("literal")
    if not bags:
        ok=accepts(F,()) and all(t%3==0 for t in target)
        return int(ok),() if ok else None,0
    first=[next(j for j,b in enumerate(bags) if i in b) for i in range(n)]
    last=[max(j for j,b in enumerate(bags) if i in b) for i in range(n)]
    owned=[[] for _ in bags]
    for c in F:
        V={abs(l)-1 for l in c}
        j=next((j for j,b in enumerate(bags) if V<=set(b)),None)
        if j is None: raise ValueError("uncovered clause")
        owned[j].append(c)
    r=len(rows); states={((),(0,)*r):(1,{})}; peak=1
    for j,bag in enumerate(bags):
        H=owned[j]
        B.pay((1<<len(bag))*(1+n+r*n+sum(1+len(c) for c in H)))
        table={}
        for bits in product((0,1),repeat=len(bag)):
            x=dict(zip(bag,bits))
            if any(x[i]!=fixed[i] for i in bag if i in fixed) or not accepts(H,x): continue
            key=tuple((i,x[i]) for i in bag if first[i]<j or last[i]>j)
            y=tuple(sum(row[i]*x[i] for i in bag if first[i]==j)%3 for row in rows)
            rep,k=table.get((key,y),(x,0));table[(key,y)]=(rep,k+1)
        B.pay(len(states)*len(table)*(1+n+r)**2)
        nxt={}
        for (key,y),(k,x) in states.items():
            for (key2,z),(d,m) in table.items():
                a=dict(key);b=dict(key2)
                if any(a[i]!=b[i] for i in a.keys()&b.keys()): continue
                K=(tuple(sorted((i,v) for i,v in (a|b).items() if last[i]>j)),
                   tuple((u+v)%3 for u,v in zip(y,z)))
                old,rep=nxt.get(K,(0,x|d));nxt[K]=(old+k*m,rep)
        states=nxt;peak=max(peak,len(states))
    B.pay(1+n+sum(1+len(c) for c in F)+r*(n+1))
    k,x=states.get(((),tuple(t%3 for t in target)),(0,None))
    if x is None: return 0,None,peak
    w=tuple(x[i] for i in range(n))
    assert accepts(F,w) and all(w[i]==b for i,b in fixed.items())
    assert tuple(sum(a*b for a,b in zip(row,w))%3 for row in rows)==tuple(t%3 for t in target)
    return k,w,peak

def source_group(F,n,rows,exterior,generators,B):
    """Verify actual CNF automorphisms, affine columns, exterior stability.
    Only coordinate permutations; arbitrary ternary value rotations are NOT
    Boolean automorphisms. Close the supplied generators with paid probes.
    """
    E=set(exterior)
    if not E<=set(range(n)): raise ValueError("exterior")
    if any(not 1<=abs(l)<=n for c in F for l in c) or any(len(row)!=n for row in rows):
        raise ValueError("source")
    B.pay(1+sum(1+len(c) for c in F)+n*(len(rows)+1))
    canon=lambda cs: Counter(tuple(sorted(c)) for c in cs)
    original=canon(F)
    G=tuple(tuple(g) for g in generators)
    for g in G:
        B.pay(1+n*(len(rows)+1)+sum(1+len(c) for c in F))
        if sorted(g)!=list(range(n)) or {g[i] for i in E}!=E: raise ValueError("permutation")
        moved=canon(tuple((g[abs(l)-1]+1)*(1 if l>0 else -1) for l in c) for c in F)
        if moved!=original or any(row[i]%3!=row[g[i]]%3 for row in rows for i in range(n)):
            raise ValueError("not source invariant")
    identity=tuple(range(n));seen={identity};todo=[identity]
    while todo:
        h=todo.pop()
        for g in G:
            B.pay(1+n)
            k=tuple(g[h[i]] for i in range(n))
            if k not in seen: seen.add(k);todo.append(k)
    return tuple(sorted(seen))

def orbit_join(F,n,bags,rows,target,exterior,generators,cap):
    """Orbit-weighted exterior coverage, including nonfree stabilizers.
    Every conditional fibre is counted once per exterior assignment.
    """
    B=Budget(cap)
    try:
        E=tuple(sorted(set(exterior)));G=source_group(F,n,rows,E,generators,B)
        B.pay((1<<len(E))*(1+len(E)))
        unseen=set(product((0,1),repeat=len(E)))
        count=0;witness=None;orbits=0;peak=0
        index={i:j for j,i in enumerate(E)}
        while unseen:
            x=min(unseen);B.pay(len(unseen)*(1+len(E))+len(G)*(1+len(E)))
            orbit=set()
            for g in G:
                y=[0]*len(E)
                for j,i in enumerate(E): y[index[g[i]]]=x[j]
                orbit.add(tuple(y))
            assert orbit<=unseen
            unseen.difference_update(orbit)
            k,w,p=live_join(F,n,bags,rows,target,B,dict(zip(E,x)))
            B.pay(1+n+len(E))
            count+=len(orbit)*k;orbits+=1;peak=max(peak,p)
            if w is not None:witness=w
        return count,witness,B.used,orbits,peak
    except Refused: return None

def main():
    rng=Random(36943);C=Counter()
    for n in range(1,8):
        bags=tuple((i,i+1) for i in range(n-1)) or ((0,),)
        for _ in range(16):
            F=tuple(tuple((i+1)*rng.choice((-1,1)) for i in b) for b in bags)
            rows=(tuple(rng.randrange(3) for i in range(n)),)
            for t in range(3):
                want=[x for x in product((0,1),repeat=n) if accepts(F,x) and sum(a*b for a,b in zip(rows[0],x))%3==t]
                out=orbit_join(F,n,bags,rows,(t,),(),(),10**8)
                assert out[0]==len(want) and ((out[1] in want) if want else out[1] is None)
                assert orbit_join(F,n,bags,rows,(t,),(),(),0) is None
                C["live_fibres"]+=1
    # Actual S3 on three Boolean coordinates; four exterior orbits (weights
    # 1,3,3,1), not six states per orbit. Symmetric source and affine rows.
    F=((1,2),(2,3),(1,3));bags=((0,1),(1,2),(0,2));rows=((1,1,1),)
    for t in range(3):
        out=orbit_join(F,3,bags,rows,(t,),(0,1,2),((1,2,0),(0,2,1)),10**7)
        want=[x for x in product((0,1),repeat=3) if accepts(F,x) and sum(x)%3==t]
        assert out[0]==len(want) and out[3]==4
        assert (out[1] in want) if want else out[1] is None
        C["S3_fibres"]+=1
    try:
        orbit_join(((1,),),3,bags,rows,(0,),(0,1,2),((1,2,0),),10**7)
        raise AssertionError("false symmetry")
    except ValueError: C["negative_controls"]+=1
    # Long path: live frontier is small although total shared boundary grows.
    n=24;bags=tuple((i,i+1) for i in range(n-1));F=tuple((i+1,i+2) for i in range(n-1))
    out=orbit_join(F,n,bags,(),(),(),(),10**8)
    a,b=1,2
    for _ in range(n):a,b=b,a+b
    assert out[0]==a and out[4]<=2
    C["long_path"]+=1
    print(dict(C))

if __name__=="__main__":main()
