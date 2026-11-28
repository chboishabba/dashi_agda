"""Bounded online raw valuation acceleration; no future trace oracle.
Uses already executed rule suffixes and exact original priority interval checks.
Raw step limit is virtual time, not host runtime or self-quotation closure.
"""
from collections import Counter,OrderedDict
from check_pnp_fractran_guarded_block import compile_block,jump


def execute(rules,v,limit,window=16,cache_cap=64):
    if limit<0 or window<0 or cache_cap<0 or any(a<0 for a in v):raise ValueError('input')
    n=len(v);v=tuple(v);rules=tuple((tuple(g),tuple(d)) for g,d in rules)
    if any(len(g)!=n or len(d)!=n or any(a<0 or a+b<0 for a,b in zip(g,d)) for g,d in rules):raise ValueError('rule')
    S=Counter(raw_steps=0,literal_steps=0,jumps=0,compile_lane_upper=0,probe_lane_upper=0,dispatch_lane_upper=0,history_symbols=0,candidate_checks=0,probes=0,cache_hits=0)
    history=();cache=OrderedDict()
    def remember(p,k):
        nonlocal history
        if window:
            h=p*min(k,(window+len(p)-1)//len(p));S['history_symbols']+=len(h)+len(history);history=(history+h)[-window:]
    def probe(block,k):
        S['probes']+=1;S['probe_lane_upper']+=n*(2+len(block[2]));return jump(v,block,k)
    while S['raw_steps']<limit:
        remaining=limit-S['raw_steps'];best=None
        # Only already observed suffixes; no assumed recurring state.
        for l in range(1,min(len(history),remaining//2)+1):
            S['candidate_checks']+=1;p=history[-l:]
            if p in cache:block=cache[p];cache.move_to_end(p);S['cache_hits']+=1
            else:
                S['compile_lane_upper']+=n*(len(rules)+sum(3+i for i in p));block=compile_block(rules,p)
                if cache_cap:
                    cache[p]=block
                    if len(cache)>cache_cap:cache.popitem(last=False)
            if probe(block,2) is None:continue
            # Prefix closure makes k-admissibility monotone. Keep the
            # original period guard list; no exponential guard expansion.
            low,high=2,remaining//l
            while low<high:
                mid=(low+high+1)//2
                if probe(block,mid) is None:high=mid-1
                else:low=mid
            if best is None or l*low>best[0]:best=(l*low,p,low,probe(block,low))
            if best[0]==remaining:break
        if best is not None:
            length,p,k,end=best;assert end is not None
            v=end;S['raw_steps']+=length;S['jumps']+=1;remember(p,k);continue
        i=None
        for j,(g,d) in enumerate(rules):
            S['dispatch_lane_upper']+=n
            if all(a>=b for a,b in zip(v,g)):i=j;break
        if i is None:return v,'halt',dict(S)
        S['dispatch_lane_upper']+=n;v=tuple(a+b for a,b in zip(v,rules[i][1]));S['raw_steps']+=1;S['literal_steps']+=1;remember((i,),1)
    return v,'limit',dict(S)
