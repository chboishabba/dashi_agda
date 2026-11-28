"""Fixed-program two-stack FRACTRAN compiler, with certified static loop jumps.
Binary exponent-vector model, NOT ordinary materialized integer bit time.
Conway priority semantics; classical two-stack tape encoding.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import prod
from check_pnp_fractran_guarded_block import compile_block,jump
from check_pnp_window_fractran import compile_static_bits

@dataclass
class Machine:
    states:int
    symbols:int
    blank:int
    rules:tuple
    tags:tuple
    sparse:tuple
    loops:dict
    @property
    def base(self):return max(2,self.symbols)
    def digit(self,a):return 0 if a==self.blank else a+1 if a<self.blank else a
    def symbol(self,a):return self.blank if a==0 else a-1 if a<=self.blank else a
    def encode(self,q,left,right):
        def stack(xs):
            v=0
            for a in reversed(xs):
                if not 0<=a<self.symbols:raise ValueError('symbol')
                v=self.base*v+self.digit(a)
            return v
        if not 0<=q<self.states:raise ValueError('state')
        right=tuple(right) or (self.blank,);v=[0]*len(self.tags);v[0]=stack(left);v[1]=stack(right);v[3]=len(left);v[4]=len(right);v[self.tags.index(('q',q))]=1
        return tuple(v)
    def decode(self,v):
        if len(v)!=len(self.tags) or v[2] or not v[4] or any(a<0 for a in v):raise ValueError('boundary')
        active=[i for i in range(5,len(v)) if v[i]]
        if len(active)!=1 or v[active[0]]!=1:raise ValueError('control')
        tag,q=self.tags[active[0]] if len(self.tags[active[0]])==2 else (None,None)
        if tag not in ('q','halt'):raise ValueError('private phase')
        def word(x,n):
            out=[]
            for _ in range(n):
                x,a=divmod(x,self.base)
                if a>=self.symbols:raise ValueError('digit')
                out.append(self.symbol(a))
            if x:raise ValueError('stack length')
            return tuple(out)
        return q,word(v[0],v[3]),word(v[1],v[4]),tag=='halt'
    def dense(self):
        return tuple((tuple(den.get(i,0) for i in range(len(self.tags))),tuple(num.get(i,0)-den.get(i,0) for i in range(len(self.tags)))) for num,den in self.sparse)
    def fractions(self,primes):
        if len(primes)!=len(self.tags) or len(set(primes))!=len(primes):raise ValueError('prime basis')
        return tuple(Fraction(prod(primes[i]**a for i,a in num.items()),prod(primes[i]**a for i,a in den.items())) for num,den in self.sparse)


def compile_stack(states,symbols,blank,rules):
    if min(states,symbols)<1 or not 0<=blank<symbols:raise ValueError('dimensions')
    rules=tuple(tuple(r) for r in rules);table={};B=max(2,symbols)
    for q,a,p,b,d in rules:
        if not (0<=q<states and 0<=p<states and 0<=a<symbols and 0<=b<symbols and d in (-1,0,1)):raise ValueError('rule')
        table.setdefault((q,a),(p,b,d))
    digit=lambda a:0 if a==blank else a+1 if a<blank else a
    tags=[('L',),('R',),('U',),('Llen',),('Rlen',)];index={t:i for i,t in enumerate(tags)};P=[];loops={}
    def tag(t):
        if t not in index:index[t]=len(tags);tags.append(t)
        return index[t]
    def edge(src,dst,consume=None,produce=None):
        den={tag(src):1,**(consume or {})};num={tag(dst):1,**(produce or {})}
        assert not den.keys()&num.keys()
        P.append((num,den))
    def loop(src,x,a,y,b):
        # Alternating private tags prevent cancellation of a control guard.
        mid=('loop',)+src;k=len(P);edge(src,mid,{x:a},{y:b});edge(mid,src)
        loops[tag(src)]=(k,x,a)
    def push(src,stack,b,dst):
        # scratch U=0 at entry; two transfers, then write the digit.
        restore=('restore',)+src;loop(src,stack,1,2,B);edge(src,restore)
        loop(restore,2,1,stack,1);edge(restore,dst,produce={stack:b} if b else {})
    def quotient(src,stack,dst):
        loop(src,2,1,stack,1);edge(src,dst)
    for q in range(states):
        read=('read',q);edge(('q',q),read);loop(read,1,B,2,1)
        # R<B at dispatch; descending guards give exactly its remainder.
        for a in sorted(range(symbols),key=digit,reverse=True):
            edge(read,('quot',q,a),consume={1:digit(a)} if digit(a) else {})
        for a in range(symbols):
            action=('action',q,a);quotient(('quot',q,a),1,action)
            if (q,a) not in table:
                push(action,1,digit(a),('halt',q));continue
            p,b,d=table[q,a]
            if d==1:push(action,0,digit(b),('rightlen',p))
            elif d==0:push(action,1,digit(b),('q',p))
            else:push(action,1,digit(b),('leftshift',p))
        # Shared left move completion for all rules with target q.
        # R already holds B*tail+b; shift it again before popping L.
        pop=('leftpop',q);push(('leftshift',q),1,0,pop);loop(pop,0,B,2,1)
        for a in sorted(range(symbols),key=digit,reverse=True):
            edge(pop,('leftquot',q,a),consume={0:digit(a)} if digit(a) else {},produce={1:digit(a)} if digit(a) else {})
        for a in range(symbols):quotient(('leftquot',q,a),0,('leftlen',q))
        # Retain exact split-list extents, including explicit blank cells.
        # Rlen includes the scanned cell; always >=1. Read guard Rlen>=2
        # cannot be reduced to Rlen>=1: consume two then restore one.
        edge(('rightlen',q),('rightrestore',q),consume={4:2},produce={3:1})
        edge(('rightlen',q),('q',q),produce={3:1})
        edge(('rightrestore',q),('q',q),produce={4:1})
        edge(('leftlen',q),('q',q),consume={3:1},produce={4:1})
        edge(('leftlen',q),('q',q),produce={4:1})
    return Machine(states,symbols,blank,rules,tuple(tags),tuple(P),loops)


def compile_candidate_bits(states,symbols,count,bits):
    # Reuse actual existing static bit-layout parser with a one-cell window.
    W,blank,initial,accept=compile_static_bits(states,symbols,1,count,bits)
    return compile_stack(states,symbols,blank,W.rules),initial,accept


def source_next(M,c):
    q,L,R=c;a=R[0] if R else M.blank;tail=R[1:] if R else ();left=L[0] if L else M.blank
    for p,s,t,b,d in M.rules:
        if (p,s)!=(q,a):continue
        if d==1:return t,(b,)+L,tail or (M.blank,)
        if d==0:return t,L,(b,)+tail
        return t,L[1:],(left,b)+tail
    return None


class Runner:
    def __init__(self,M):
        self.M=M;self.rules=M.dense();self.blocks={tag:compile_block(self.rules,(k,k+1)) for tag,(k,_,_) in M.loops.items()}
    def first(self,v):
        for i,(g,d) in enumerate(self.rules):
            if all(a>=b for a,b in zip(v,g)):return i,tuple(a+b for a,b in zip(v,d))
        return None,None
    def step(self,v,accelerate=True,raw_cap=None):
        """Return canonical next/halt; static loop summaries are verified
        against actual ordered fraction guards. No future source trace.
        raw_cap is a refusal bound for literal controls only."""
        if self.M.decode(v)[3]:return v,True,dict(raw=0,literal=0,jumps=0,checks=0,max_bits=max(v).bit_length())
        S=dict(raw=0,literal=0,jumps=0,checks=0,max_bits=max(v).bit_length())
        while True:
            if raw_cap is not None and S['raw']>=raw_cap:raise RuntimeError('raw cap')
            active=next(i for i in range(5,len(v)) if v[i]);info=self.M.loops.get(active)
            if accelerate and info:
                k,x,a=info;t=v[x]//a
                if t:
                    end=jump(v,self.blocks[active],t);S['checks']+=1
                    assert end is not None and jump(v,self.blocks[active],t+1) is None;S['checks']+=1
                    v=end;S['raw']+=2*t;S['jumps']+=1;S['max_bits']=max(S['max_bits'],max(v).bit_length());continue
            _,u=self.first(v);assert u is not None
            v=u;S['raw']+=1;S['literal']+=1;S['max_bits']=max(S['max_bits'],max(v).bit_length())
            active=next(i for i in range(5,len(v)) if v[i]);name=self.M.tags[active][0]
            if name in ('q','halt'):
                return v,name=='halt',S
