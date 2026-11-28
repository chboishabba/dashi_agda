"""Signed-magnitude arithmetic using original unsigned bit schedules.
Explicit sign copies and magnitude borrow; host branch/control not a tape clock.
"""
from check_pnp_nat_bit_schedule import NatOps
from check_pnp_bit_data_schedule import Clock,Refused

class IntOps:
    def __init__(self,c):self.c=c;self.u=NatOps(c)
    def add(self,x,y):
        c=self.c;u=self.u;c.pay('sign_read',2)
        if (x<0)==(y<0):z=u.add(abs(x),abs(y));sign=x<0
        else:
            a,b=u.word(abs(x)),u.word(abs(y));k=max(len(a),len(b))
            a=a+(0,)*(k-len(a));b=b+(0,)*(k-len(b));c.pay('nat_copy',2*k)
            v,borrow=u.subtract_words(a,b)
            if borrow:v,_=u.subtract_words(b,a)
            z=u.value(v);sign=(y<0) if borrow else (x<0)
        c.pay('sign_write');return -z if sign else z
    def sub(self,x,y):self.c.pay('sign_flip');return self.add(x,-y)
    def mul(self,x,y):
        self.c.pay('sign_read',2);sign=self.u.xor(int(x<0),int(y<0));z=self.u.mul(abs(x),abs(y))
        self.c.pay('sign_write');return -z if sign else z
    def sum(self,xs):
        z=0
        for x in xs:z=self.add(z,x)
        return z

def main():
    from random import Random
    rng=Random(369);c=Clock(10**8);o=IntOps(c);n=0
    for k in range(1,49):
        for sx,sy in ((1,1),(1,-1),(-1,1),(-1,-1)):
            x=sx*rng.getrandbits(k);y=sy*rng.getrandbits(k)
            assert o.add(x,y)==x+y and o.sub(x,y)==x-y and o.mul(x,y)==x*y;n+=3
    for x in (-1,0,1):assert o.sub(x,x)==0;n+=1
    assert sum(c.count.values())+c.left==c.cap
    try:IntOps(Clock(0)).add(1,-1);raise AssertionError('free signed arithmetic')
    except Refused:pass
    print(dict(checks=n,charged=c.cap-c.left))
if __name__=='__main__':main()
