"""Static finite-window compiler of a standard first-match tape table.
No known execution, SAT oracle or self-quotation is used in compilation.
Each source transition uses two reduced-fraction steps. A window escape
is a distinguished refusal, never an ordinary source halt.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import prod

@dataclass(frozen=True)
class Window:
    states:int
    symbols:int
    width:int
    rules:tuple
    # Each fraction is (numerator prime tags, denominator prime tags).
    program:tuple
    lanes:int
    def control(self,q,i):return q*self.width+i
    def cell(self,i,a):return self.states*self.width+i*self.symbols+a
    @property
    def escape(self):return self.lanes-1
    def encode(self,q,i,tape):
        if not (0<=q<self.states and 0<=i<self.width and len(tape)==self.width and all(0<=a<self.symbols for a in tape)):raise ValueError('configuration')
        return frozenset([self.control(q,i)]+[self.cell(j,a) for j,a in enumerate(tape)])
    def decode(self,v):
        if self.escape in v:return None
        cs=[a for a in v if a<self.states*self.width]
        if len(cs)!=1 or len(v)!=self.width+1:raise ValueError('not a canonical boundary')
        q,i=divmod(cs[0],self.width);t=[]
        for j in range(self.width):
            a=[a for a in range(self.symbols) if self.cell(j,a) in v]
            if len(a)!=1:raise ValueError('cell')
            t.append(a[0])
        return q,i,tuple(t)

def compile_window(states,symbols,width,rules):
    if min(states,symbols,width)<1:raise ValueError('dimensions')
    rules=tuple(tuple(r) for r in rules);used=set();selected=[]
    for q,a,p,b,d in rules:
        if not (0<=q<states and 0<=p<states and 0<=a<symbols and 0<=b<symbols and d in (-1,0,1)):raise ValueError('rule')
        if (q,a) not in used:selected.append((q,a,p,b,d));used.add((q,a))
    base=width*(states+symbols);lanes=base+width*len(selected)+1;P=[]
    W=Window(states,symbols,width,rules,(),lanes)
    for k,(q,a,p,b,d) in enumerate(selected):
        for i in range(width):
            phase=base+k*width+i
            # Consume both the source control and scanned symbol even
            # when the transition would leave either unchanged.
            P.append(((phase,),(W.control(q,i),W.cell(i,a))))
            dest=W.control(p,i+d) if 0<=i+d<width else W.escape
            P.append(((dest,W.cell(i,b)),(phase,)))
    return Window(states,symbols,width,rules,tuple(P),lanes)

def raw_step(W,v):
    for k,(num,den) in enumerate(W.program):
        if all(t in v for t in den):
            rest=v.difference(den)
            assert not rest.intersection(num),'one-hot invariant'
            return rest.union(num),k
    return None,None

def source_step(W,c):
    q,i,t=c
    for a,b,p,z,d in W.rules:
        if (a,b)==(q,t[i]):
            if not 0<=i+d<W.width:return 'escape',None
            u=list(t);u[i]=z;return 'step',(p,i+d,tuple(u))
    return 'halt',c

def replay(W,c,limit):
    if limit<0:raise ValueError('limit')
    v=W.encode(*c);steps=0
    for _ in range(limit):
        u,k=raw_step(W,v)
        if u is None:return 'halt',W.decode(v),steps
        z,j=raw_step(W,u);assert z is not None and j==k+1 and k%2==0
        steps+=2;v=z
        if W.escape in v:return 'escape',None,steps
    return 'limit',W.decode(v),steps

def fractions(W,primes):
    # Caller supplies a certified distinct prime basis. Prime generation,
    # validation, materialization and integer arithmetic are separate.
    if len(primes)!=W.lanes or len(set(primes))!=W.lanes:raise ValueError('basis')
    return tuple(Fraction(prod(primes[t] for t in num),prod(primes[t] for t in den)) for num,den in W.program)

def dense_rules(W):
    return tuple((tuple(int(i in den) for i in range(W.lanes)),tuple(int(i in num)-int(i in den) for i in range(W.lanes))) for num,den in W.program)
