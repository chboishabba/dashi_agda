"""Unsigned bit-register arithmetic, with explicit gates and copies.
Host index/control and integer interchange remain separately unmetered.
"""
from check_pnp_bit_data_schedule import Clock,Refused
from random import Random

class NatOps:
    def __init__(self,c):self.c=c
    def word(self,x):
        if x<0:raise ValueError('unsigned')
        k=max(1,x.bit_length());self.c.pay('nat_load',k)
        return tuple((x>>i)&1 for i in range(k))
    def value(self,w):
        self.c.pay('nat_store',len(w));return sum(b<<i for i,b in enumerate(w))
    def xor(self,a,b):
        c=self.c;return c.AND(c.OR(a,b),c.NOT(c.AND(a,b)))
    def add_words(self,a,b):
        c=self.c;carry=0;z=[]
        for i in range(max(len(a),len(b))):
            x=a[i] if i<len(a) else 0;y=b[i] if i<len(b) else 0
            u=self.xor(x,y);z.append(self.xor(u,carry));carry=c.OR(c.AND(x,y),c.AND(u,carry))
        c.pay('nat_copy',len(z)+1);return tuple(z)+(carry,)
    def add(self,x,y):return self.value(self.add_words(self.word(x),self.word(y)))
    def mul(self,x,y):
        c=self.c;a,b=self.word(x),self.word(y);k=len(a)+len(b);z=(0,)*k
        c.pay('nat_copy',k)
        for i,d in enumerate(b):
            part=(0,)*i+tuple(c.AND(d,u) for u in a)
            c.pay('nat_copy',len(part));z=self.add_words(z,part)[:k]
        return self.value(z)
    def subtract_words(self,a,b):
        c=self.c;borrow=0;z=[]
        for i,x in enumerate(a):
            y=b[i] if i<len(b) else 0;u=self.xor(x,y)
            z.append(self.xor(u,borrow));borrow=c.OR(c.AND(c.NOT(x),y),c.AND(c.NOT(u),borrow))
        c.pay('nat_copy',len(z));return tuple(z),borrow
    def divmod(self,x,y):
        if y<=0:raise ValueError('divisor')
        c=self.c;a,b=self.word(x),self.word(y);r=(0,)*(len(b)+1);q=[]
        c.pay('nat_copy',len(r))
        for bit in reversed(a):
            v=(bit,)+r[:-1];c.pay('nat_copy',len(v))
            d,borrow=self.subtract_words(v,b);r=v if borrow else d
            c.pay('nat_copy',len(r)+1);q.append(c.NOT(borrow))
        return self.value(tuple(reversed(q))),self.value(r)
    def sum(self,values):
        z=0
        for x in values:z=self.add(z,x)
        return z
    def address(self,i,stride,j):return self.add(self.mul(i,stride),j)


def main():
    rng=Random(369);c=Clock(100000000);o=NatOps(c);checks=0
    for k in range(1,65):
        for _ in range(4):
            x=rng.getrandbits(k);y=rng.getrandbits(k)+1
            assert o.add(x,y)==x+y and o.mul(x,y)==x*y and o.divmod(x,y)==divmod(x,y)
            assert o.address(x,y,7)==x*y+7;checks+=4
    assert sum(c.count.values())+c.left==c.cap
    try:NatOps(Clock(0)).add(1,2);raise AssertionError('free arithmetic')
    except Refused:pass
    print(dict(checks=checks,charges=dict(c.count),total=c.cap-c.left))
if __name__=='__main__':main()
