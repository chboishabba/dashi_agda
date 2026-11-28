"""Actual fixed stack compiler with metered binary-exponent operations.
The metered primitive costs are conservative grade-school bit-operation
weights. They are not literal same-target single-tape execution steps.
"""
from check_pnp_stack_fractran import Runner,compile_candidate_bits

class Meter:
    def __init__(self):self.work=0;self.ops=0
    @staticmethod
    def width(x):return max(1,abs(x).bit_length())
    def pay(self,x,y,factor=1):
        self.ops+=1;self.work+=factor*(self.width(x)+self.width(y)+2)
    def add(self,x,y):self.pay(x,y,2);return x+y
    def sub(self,x,y):self.pay(x,y,2);return x-y
    def mul(self,x,c):self.pay(x,c,4*self.width(c));return x*c
    def div(self,x,c):
        assert c>0
        self.pay(x,c,8*self.width(c));return x//c
    def lt(self,x,y):self.pay(x,y);return x<y
    def scan(self,v):self.work+=sum(self.width(x) for x in v)+len(v)

class ChargedRunner(Runner):
    def hit(self,v,D,g,k,m):
        lo,hi=0,m.sub(k,1)
        for a,d,b in zip(v,D,g):
            if d>0:
                q=-m.div(m.sub(a,b),d);lo=q if m.lt(lo,q) else lo
            elif d<0:
                q=m.div(m.sub(a,b),-d);hi=q if m.lt(q,hi) else hi
            elif m.lt(a,b):return False
            if m.lt(hi,lo):return False
        return not m.lt(hi,lo)
    def guarded(self,v,block,k,m):
        need,D,higher=block;m.scan(v)
        if k==0:return tuple(v)
        for a,d,g in zip(v,D,need):
            z=m.mul(m.sub(k,1),d)
            if m.lt(m.add(a,z if m.lt(z,0) else 0),g):return None
        if any(self.hit(v,D,g,k,m) for g in higher):return None
        return tuple(m.add(a,m.mul(k,d)) for a,d in zip(v,D))
    def first_paid(self,v,m):
        for i,(g,d) in enumerate(self.rules):
            if all(not m.lt(a,b) for a,b in zip(v,g)):
                return i,tuple(m.add(a,b) for a,b in zip(v,d))
        return None,None
    def paid_step(self,v):
        # Caller starts at an encoded boundary; internal compiler phases
        # preserve this invariant. No full extent decode at every step.
        m=Meter();S=dict(raw=0,literal=0,jumps=0,checks=0,max_bits=max(v).bit_length(),lane_width=0)
        while True:
            m.scan(v);S['lane_width']+=sum(m.width(a) for a in v)
            active=next(i for i in range(5,len(v)) if v[i]);info=self.M.loops.get(active)
            if self.M.tags[active][0]=='halt':return v,True,dict(S,bit_weight=m.work,arithmetic_ops=m.ops)
            if info:
                _,x,a=info;t=m.div(v[x],a)
                if t:
                    u=self.guarded(v,self.blocks[active],t,m);S['checks']+=1
                    assert u is not None and self.guarded(v,self.blocks[active],m.add(t,1),m) is None;S['checks']+=1
                    v=u;S['raw']+=2*t;S['jumps']+=1;S['max_bits']=max(S['max_bits'],max(v).bit_length());continue
            _,u=self.first_paid(v,m);assert u is not None
            v=u;S['raw']+=1;S['literal']+=1;S['max_bits']=max(S['max_bits'],max(v).bit_length());m.scan(v)
            active=next(i for i in range(5,len(v)) if v[i]);name=self.M.tags[active][0]
            if name in ('q','halt'):return v,name=='halt',dict(S,bit_weight=m.work,arithmetic_ops=m.ops)

def run_exact(M,accept,c,T,probe_terminal=False):
    """Run exactly T source transitions; early halt is distinct from final acceptance.
    Final decode only once. No model or future source trace is supplied.
    The optional extra paid probe tests terminality at the retained endpoint.
    """
    if T<0:raise ValueError('horizon')
    run=ChargedRunner(M);v=M.encode(*c);receipts=[];done=0
    for _ in range(T):
        v,h,s=run.paid_step(v);receipts.append(s)
        if h:break
        done+=1
    q,L,R,h=M.decode(v);terminal=True if h else None;probe=None
    if probe_terminal and not h:
        _,terminal,probe=run.paid_step(v)
    return dict(status='EXACT' if done==T else 'EARLY_HALT',steps=done,configuration=(q,L,R),accepted=q==accept,halted=h,terminal=terminal,probe=probe,bit_weight=sum(a['bit_weight'] for a in receipts)+(probe['bit_weight'] if probe is not None else 0),receipts=receipts)

def candidate_exact(states,symbols,count,bits,left,right,T,probe_terminal=False):
    M,ini,accept=compile_candidate_bits(states,symbols,count,bits)
    return run_exact(M,accept,(ini,tuple(left),tuple(right) or (M.blank,)),T,probe_terminal)
