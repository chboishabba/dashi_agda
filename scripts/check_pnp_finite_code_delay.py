"""Finite code hardwires a complete bounded source prefix, then falls back.
This refutes grade-independent/clock-degree-only first-gain cutoffs, not
full-code computable deadlines. Offline code construction is unbounded.
"""
from itertools import product
from check_pnp_fixed_code_gain import Candidate,syntax,scan,verify,valid


def word(F,n):
    # Fixed finite alphabet and prefix-free ordered syntax; unary source
    # arity and variable indices in this explicit test encoding.
    yield from (1,)*n;yield 0
    for c in F:
        yield 2
        for l in c:
            yield 1 if l>0 else 0
            yield from (1,)*abs(l);yield 0
    yield 3


class Trie:
    def __init__(self):self.edges=[{}];self.outputs={};self.reads=0
    def insert(self,w,x):
        j=0
        for t in w:
            if t not in self.edges[j]:
                self.edges[j][t]=len(self.edges);self.edges.append({})
            j=self.edges[j][t]
        assert j not in self.outputs;self.outputs[j]=x
    def run(self,F,n,cap):
        j=0;self.reads=0
        for t in word(F,n):
            self.reads+=1
            j=self.edges[j].get(t,-1)
            if j<0:return dict(witness=None)
        return dict(witness=self.outputs.get(j))


def compile_prefix(N):
    T=Trie();sources=0
    for grade in range(1,N+1):
        for n in range(1,grade+1):
            for F in syntax(n,grade-n):
                x=next((x for x in product((0,1),repeat=n) if valid(F,n,x)),None)
                if x is not None:T.insert(word(F,n),x)
                sources+=1
    # The trie is finite CONTROL data, no exhaustive search at run time.
    # This charge is an explicit encoded-length bound, not a native TM receipt.
    e=Candidate(T.run,lambda F,n:1+len(tuple(word(F,n)))+n)
    return e,T,sources


def main():
    totals=0
    for N in range(2,8):
        e,T,sources=compile_prefix(N)
        for grade in range(1,N+1):
            for n in range(1,grade+1):
                for F in syntax(n,grade-n):
                    x=e.run(F,n);w=any(valid(F,n,z) for z in product((0,1),repeat=n))
                    assert (x is not None)==w
                    if x is not None:assert valid(F,n,x)
                    assert T.reads<=len(tuple(word(F,n)))
                    totals+=1
        q=scan(e,N,10**7);assert q['status']=='NO_GAIN_WITHIN_PREFIX'
        F=((-1,-1),)*N;assert 1+3*N>N and e.run(F,1) is None
        q2=dict(status='GAIN',n=1,parent=F,literal=-1,witness=(0,));assert verify(e,q2)
        print('delay',N,'sources',sources,'states',len(T.edges),'prefix_calls',q['calls'],'later_grade',1+3*N)
    print('bounded source checks',totals)
if __name__=='__main__':main()
