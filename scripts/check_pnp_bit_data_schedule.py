"""Explicit sequential bit-data schedule for F3 elimination and CNF audit.
Data head movement, bit reads/writes and Boolean register gates are charged.
The host address generation, loop control, compilation and other portfolio
kernels are NOT yet implemented on the same tape clock.
"""
from collections import Counter
from itertools import product
from random import Random
from check_pnp_f3_syndrome_boundary import rref

class Refused(Exception):pass
class Clock:
    def __init__(self,cap):
        if cap<0:raise ValueError('cap')
        self.cap=cap;self.left=cap;self.count=Counter()
    def pay(self,name,k=1):
        if k<0:raise ValueError('charge')
        if k>self.left:raise Refused()
        self.left-=k;self.count[name]+=k
    def AND(self,a,b):self.pay('gate');return a&b
    def OR(self,a,b):self.pay('gate');return a|b
    def NOT(self,a):self.pay('gate');return 1-a

class Tape:
    def __init__(self,clock,bits):
        self.clock=clock;self.bits=list(bits);self.head=0
        clock.pay('load',len(self.bits))
    def seek(self,i):
        if not 0<=i<len(self.bits):raise ValueError('address')
        self.clock.pay('head_move',abs(i-self.head));self.head=i
    def read(self,i):self.seek(i);self.clock.pay('read');return self.bits[i]
    def write(self,i,b):self.seek(i);self.clock.pay('write');self.bits[i]=b

def code(a):
    if a not in (0,1,2):raise ValueError('trit')
    return a&1,a>>1

def value(a):return a[0]+2*a[1]

def onehot(c,a):return c.NOT(c.OR(*a)),a[0],a[1]

def add(c,a,b):
    x,y=onehot(c,a),onehot(c,b)
    return (c.OR(c.OR(c.AND(x[0],y[1]),c.AND(x[1],y[0])),c.AND(x[2],y[2])),
            c.OR(c.OR(c.AND(x[0],y[2]),c.AND(x[2],y[0])),c.AND(x[1],y[1])))

def mul(c,a,b):
    return (c.OR(c.AND(a[0],b[0]),c.AND(a[1],b[1])),
            c.OR(c.AND(a[0],b[1]),c.AND(a[1],b[0])))

def nonzero(c,a):return c.OR(*a)

def neg(c,a):c.pay('register_copy',2);return a[1],a[0]

def rref_bits(rows,n,c):
    """Same elimination and pivot order as signed_component_histogram.rref."""
    m=len(rows)
    if any(len(row)!=n+1 for row in rows):raise ValueError('matrix')
    tape=Tape(c,(b for row in rows for a in row for b in code(a)))
    from check_pnp_nat_bit_schedule import NatOps
    ops=NatOps(c)
    def address(i,j):return ops.mul(2,ops.address(i,n+1,j))
    def get(i,j):
        k=address(i,j);return tape.read(k),tape.read(ops.add(k,1))
    def put(i,j,a):
        k=address(i,j);tape.write(k,a[0]);tape.write(ops.add(k,1),a[1])
    p=0;piv=[]
    for j in range(n):
        i=next((i for i in range(p,m) if nonzero(c,get(i,j))),None)
        if i is None:continue
        if i!=p:
            for k in range(n+1):
                a,b=get(p,k),get(i,k);put(p,k,b);put(i,k,a)
        a=get(p,j) # inverse of either nonzero F3 value is itself
        for k in range(n+1):put(p,k,mul(c,a,get(p,k)))
        for i in range(m):
            if i==p:continue
            a=get(i,j)
            if not nonzero(c,a):continue
            a=neg(c,a)
            for k in range(n+1):put(i,k,add(c,get(i,k),mul(c,a,get(p,k))))
        piv.append(j);p+=1
    if any(nonzero(c,get(i,n)) for i in range(p,m)):return None
    return tuple(tuple(value(get(i,j)) for j in range(n+1)) for i in range(p)),tuple(piv)

def span_bits(A,r,c):
    result=rref_bits(tuple(tuple(a)+(0,) for a in A),r,c)
    assert result is not None
    return tuple(row[:-1] for row in result[0])

def chart_bits(A,b,r,c):
    rr=rref_bits(tuple(tuple(a)+(t,) for a,t in zip(A,b)),r,c)
    if rr is None:return None
    rows,piv=rr;free=tuple(i for i in range(r) if i not in piv)
    c.pay('register_copy',2*r*(1+len(free)))
    u=[0]*r
    for i,row in zip(piv,rows):u[i]=row[-1]
    V=[]
    for j in free:
        v=[0]*r;v[j]=1
        for i,row in zip(piv,rows):v[i]=value(neg(c,code(row[j])))
        V.append(tuple(v))
    return tuple(u),tuple(V)

def audit(F,rows,target,x,c):
    """All clause and F3 operations on actual original witness bits."""
    if len(rows)!=len(target) or any(len(r)!=len(x) for r in rows):raise ValueError('shape')
    tape=Tape(c,x);ok=1
    for clause in F:
        sat=0
        for l in clause:
            v=tape.read(abs(l)-1)
            sat=c.OR(sat,v if l>0 else c.NOT(v))
        ok=c.AND(ok,sat)
    for row,t in zip(rows,target):
        a=(0,0)
        for i,r in enumerate(row):
            b=tape.read(i);a=add(c,a,mul(c,code(r),(b,0)))
        want=code(t)
        eq=c.AND(a[0] if want[0] else c.NOT(a[0]),a[1] if want[1] else c.NOT(a[1]))
        ok=c.AND(ok,eq)
    return bool(ok)

def main():
    rng=Random(36943);C=Clock(10**8);counts=Counter()
    for a,b in product(range(3),repeat=2):
        assert value(add(C,code(a),code(b)))==(a+b)%3
        assert value(mul(C,code(a),code(b)))==(a*b)%3
        counts['field']+=2
    for n,m in product(range(6),range(6)):
        for _ in range(12):
            rows=tuple(tuple(rng.randrange(3) for j in range(n+1)) for i in range(m))
            assert rref_bits(rows,n,C)==rref(rows,n)
            counts['rref']+=1
    for n in range(1,7):
        F=tuple(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,n+1))) for _ in range(3))
        rows=(tuple(rng.randrange(3) for _ in range(n)),)
        for x,t in product(product((0,1),repeat=n),range(3)):
            expected=all(any(x[abs(l)-1]==int(l>0) for l in z) for z in F) and sum(a*b for a,b in zip(rows[0],x))%3==t
            assert audit(F,rows,(t,),x,C)==expected
            counts['audit']+=1
    assert sum(C.count.values())+C.left==C.cap
    try:rref_bits(((1,0),),1,Clock(0));raise AssertionError('free computation')
    except Refused:counts['refusal']+=1
    print(dict(counts),dict(C.count),C.cap-C.left)
if __name__=='__main__':main()
