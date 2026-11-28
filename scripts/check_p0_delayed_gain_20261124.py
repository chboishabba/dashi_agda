"""Finite delay/clock controls for G126 onward; not a halting oracle or Clay proof."""
from itertools import product, combinations
from math import ceil

# Two-register machine: halt is a state, so its arrival time is the step count.
def halted_within(code, budget):
    pc, regs = 0, [0, 0]
    for t in range(budget + 1):
        op, *args = code[pc]
        if op == 'halt': return True
        if t == budget: return False
        if op == 'inc':
            r, target = args; regs[r] += 1; pc = target
        elif op == 'dec':
            r, positive, zero = args
            if regs[r]: regs[r] -= 1; pc = positive
            else: pc = zero
        else: raise ValueError(op)
    raise AssertionError('unreachable')

def delay(t):
    return [('inc', 0, i+1) for i in range(t)] + [('halt',)]

# Canonical labelled CNF representation, including explicit dense variable count.
def enc(n, F):
    return (str(n)+':'+ ';'.join(','.join(map(str,c)) for c in sorted(set(F)))).encode('ascii')

def size(n, F): return len(enc(n,F))
def truth(F,x): return all(any(x[abs(i)-1] == (i>0) for i in c) for c in F)
def default(n,F):
    x = [False]*n
    for c in sorted(F):
        if len(c)==1: x[abs(c[0])-1] = c[0]>0
    return tuple(x)
def exhaustive(n,F):
    return next((x for x in product((False,True),repeat=n) if truth(F,x)),default(n,F))
def anchored(n,F):
    return len({abs(c[0]) for c in F if len(c)==1})==n

def delayed(code,n,F):
    if anchored(n,F):return default(n,F)
    if not halted_within(code,size(n,F)-1):return exhaustive(n,F)
    return default(n,F)
def score(W,n,F):return truth(F,W(n,F))

cs=[(i,) for i in (-2,-1,1,2)]+[(a,b) for a in (-1,1) for b in (-2,2)]
forms=[tuple(c for i,c in enumerate(cs) if mask>>i&1) for mask in range(256)]
delays=(0,1,2,3,4,5,8,12,16,20,24,32,48,64,96,128,256)
checks=short=edges=shortedges=gains=anchors=0
for T in delays:
    code=delay(T)
    if T:assert not halted_within(code,T-1)
    assert halted_within(code,T)
    W=lambda n,F:delayed(code,n,F)
    for F in forms:
        N=size(2,F); S=score(W,2,F); H=truth(F,exhaustive(2,F))
        assert not S or H;checks+=1
        if N<=T:assert S==H;short+=1
        if anchored(2,F):assert S==H;anchors+=1
        for lit in (-2,-1,1,2):
            G=tuple(sorted(set(F+((lit,),))))
            x=W(2,G); gain=not S and truth(G,x)
            edges+=1
            if N<=T:assert not gain;shortedges+=1
            if gain:assert N>T and truth(F,x);gains+=1
    # Explicit witness family: grow until BOTH encodings exceed T.
    m=2
    while True:
        F=((1,2),)+tuple((1,i) for i in range(3,m+1))
        G=F+((1,),)
        if min(size(m,F),size(m,G))>T:break
        m+=1
    assert not anchored(m,F) and not score(W,m,F) and score(W,m,G)
    assert truth(F,W(m,G))
print('delay programs',len(delays),'formula checks',checks,'short correctness',short,
      'unit edges',edges,'short zero-gain edges',shortedges,'actual gains',gains,
      'anchor checks',anchors,'explicit late gains',len(delays))

# Conditional clocked construction, on this finite carrier use exhaustive as
# the stand-in for a hypothetical complete polynomial W*. This is NOT a
# polynomial-time general SAT solver; finite controls only.
loop=[('inc',0,0)]
clocked=lambda code,n,F: (default(n,F) if anchored(n,F) or halted_within(code,size(n,F)-1) else exhaustive(n,F))
finite=0
for F in forms:
    assert score(lambda n,F:clocked(loop,n,F),2,F)==truth(F,exhaustive(2,F));finite+=1
for T in delays:
    for F in forms:
        assert clocked(delay(T),2,F)==delayed(delay(T),2,F);finite+=1
print('conditional clocked finite controls',finite)
