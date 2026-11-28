"""Same-input fixed anchored producer and direct finite gain scan.
No semantic normalization of a candidate's input; no total deadline claim.
"""
from itertools import product
from check_pnp_gain_bisection import valid,bisect_gain
from check_pnp_normal_endpoint_weld import cnf_solver
from check_p0_signed_contrast_20261125 import ContinuationAllowance


def anchor(F,n):
    """Source-defined fully pinned override, regardless of path history."""
    P={}
    for c in F:
        if len(c)==1:
            l=c[0];i=abs(l)-1;b=int(l>0)
            if i in P and P[i]!=b:return None
            P[i]=b
    if len(P)!=n:return None
    x=tuple(P[i] for i in range(n))
    return x if valid(F,n,x) else None


class Candidate:
    def __init__(self,producer,clock):self.producer=producer;self.clock=clock
    def run(self,F,n):
        if n<0 or any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError('source')
        cap=self.clock(F,n)
        if type(cap)!=int or cap<0:raise ValueError('clock')
        x=anchor(F,n)
        if x is None:x=self.producer(F,n,cap).get('witness')
        return tuple(x) if valid(F,n,x) else None


def localize(F,n,w,e,root):
    if not valid(F,n,w):raise ValueError('original witness')
    pins=tuple(((i+1)*(2*b-1),) for i,b in enumerate(w));cache={}
    class Refusal(Exception):pass
    def score(i):
        if i not in cache:
            G=F+pins[:i];cost=1+n+sum(1+len(c) for c in G)+e.clock(G,n)
            if not root.reserve('fixed_gain_call',cost):raise Refusal()
            cache[i]=e.run(G,n)
        return cache[i] is not None
    try:
        if score(0):return dict(status='ROOT_VERIFIED')
        assert n>0 and score(n) # actual anchor, not an external path-dependent answer
        a,b=bisect_gain(n,score)
    except Refusal:return dict(status='UNKNOWN')
    return dict(status='GAIN',n=n,parent=F+pins[:a],literal=pins[a][0],witness=cache[b],queries=len(cache))


def verify(e,q):
    if q['status']!='GAIN':return False
    F,n,l=q['parent'],q['n'],q['literal']
    return (e.run(F,n) is None and e.run(F+((l,),),n)==q['witness'] and valid(F+((l,),),n,q['witness']))


def syntax(n,cost):
    """All ordered CNFs with sum (1 + clause length) == cost.
    Includes repeated clauses/literals and empty clauses; no quotienting.
    """
    if cost==0:yield ();return
    L=tuple(l for i in range(1,n+1) for l in (-i,i))
    for k in range(cost):
        for c in product(L,repeat=k):
            for tail in syntax(n,cost-k-1):yield (c,)+tail


def scan(e,max_grade,max_calls):
    """Finite prefix of direct gain recognizer; no SAT decision oracle."""
    if min(max_grade,max_calls)<0:raise ValueError('bound')
    calls=0
    for grade in range(max_grade+1):
        for n in range(1,grade+1):
            for F in syntax(n,grade-n):
                if calls>=max_calls:return dict(status='REFUSED',calls=calls,grade=grade)
                a=e.run(F,n);calls+=1
                if a is not None:continue
                for i in range(1,n+1):
                    for l in (-i,i):
                        if calls>=max_calls:return dict(status='REFUSED',calls=calls,grade=grade)
                        x=e.run(F+((l,),),n);calls+=1
                        if x is not None:return dict(status='GAIN',n=n,parent=F,literal=l,witness=x,calls=calls,grade=grade)
    return dict(status='NO_GAIN_WITHIN_PREFIX',calls=calls,max_grade=max_grade)


def main():
    from random import Random
    C={};rng=Random(3693103)
    e=Candidate(lambda F,n,c:cnf_solver(F,n,(),(),c),lambda F,n:0)
    for n in range(1,13):
        for _ in range(10):
            w=tuple(rng.randrange(2) for i in range(n));F=tuple(((i+1)*(2*b-1),) for i,b in enumerate(w))
            assert localize(F,n,w,e,ContinuationAllowance(10**6))['status']=='ROOT_VERIFIED'
            # Actual miss: non-unit duplicate literals encode each same pin,
            # but the source-defined override only applies to literal units.
            G=tuple(c+c for c in F);q=localize(G,n,w,e,ContinuationAllowance(10**6));assert verify(e,q)
            C['fixed_localization']=C.get('fixed_localization',0)+1
    q=scan(e,5,100000);assert verify(e,q);print('actual fixed code first scanned gain',q)
    # Complete on this finite prefix only; no universal completeness claim.
    exhaustive=Candidate(lambda F,n,c:dict(witness=next((x for x in product((0,1),repeat=n) if valid(F,n,x)),None)),lambda F,n:1<<n)
    z=scan(exhaustive,5,100000);assert z['status']=='NO_GAIN_WITHIN_PREFIX';print('finite prefix control',z)
    assert scan(e,5,0)['status']=='REFUSED'
    # Arbitrary syntactic padding does not force a miss: an all-zero
    # recognizer solves every source accepting zero, however padded.
    zc=Candidate(lambda F,n,c:dict(witness=(0,)*n),lambda F,n:1+n+sum(map(len,F)))
    for n in (1,2,8,32,128):
        F=tuple((-i,i) for i in range(1,n+1))*8
        assert zc.run(F,n)==(0,)*n
    print(C,'padding controls 5, refusal PASS')
if __name__=='__main__':main()
