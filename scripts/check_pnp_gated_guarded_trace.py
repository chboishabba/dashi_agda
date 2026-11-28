"""Exact consecutive-repeat discovery with bounded failed-probe cache.
Explicit operand-bit tariff, NOT a measured physical machine bit clock.
A savings admission filter pays accumulated modeled discovery where possible;
unsuccessful attempts remain charged, so no universal zero-regression claim.
"""
from collections import Counter,OrderedDict
from check_pnp_fractran_guarded_block import compile_block,jump


def charge(*xs):
    # Declared arithmetic tariff on signed operand sizes. Includes k and
    # current exponents; multiplication/division are not unit-cost.
    return (1+sum(1+abs(x).bit_length() for x in xs))**2


def repeat_suffixes(history,remaining):
    for l in range(1,min(len(history)//2,remaining//2)+1):
        p=history[-l:]
        if history[-2*l:-l]!=p:continue
        if any(l%d==0 and p==p[:d]*(l//d) for d in range(1,l)):continue
        yield p


def relevant_two(block):
    G,D,H=block
    # Every selected and forbidden threshold for j=0,1. Nonpositive
    # thresholds are automatically satisfied by nonnegative exponents.
    return tuple(i for i,(g,d) in enumerate(zip(G,D)) if g-min(0,d)>0 or any(h[i]-min(0,d)>0 for h in H))


def execute_gated(rules,v,limit,window=32,cache_cap=64,admit=True):
    if limit<0 or window<0 or cache_cap<0 or any(a<0 for a in v):raise ValueError('input')
    n=len(v);v=tuple(v);rules=tuple((tuple(g),tuple(d)) for g,d in rules)
    if any(len(g)!=n or len(d)!=n or any(a<0 or a+b<0 for a,b in zip(g,d)) for g,d in rules):raise ValueError('rule')
    S=Counter(raw_steps=0,literal_steps=0,jumps=0,probes=0,cache_hits=0,cooldown_skips=0,candidate_checks=0,repeat_triggers=0,admission_refusals=0,preflight_skips=0,discovery_disabled=0,compile_charge=0,probe_charge=0,bookkeeping_charge=0,literal_charge=0,admitted_literal_lower=0)
    history=();cache=OrderedDict();m=max((abs(x) for g,d in rules for x in g+d),default=0)
    S['bookkeeping_charge']+=1+sum(1+abs(x).bit_length() for g,d in rules for x in g+d)
    disabled=False
    def overhead():return S['compile_charge']+S['probe_charge']+S['bookkeeping_charge']
    def remember(p,k):
        nonlocal history
        if window:
            h=p*min(k,(window+len(p)-1)//len(p));S['bookkeeping_charge']+=len(h)+len(history)+1;history=(history+h)[-window:]
    def probe_cost(block,k):
        G,D,H=block
        return 1+sum(12*charge(a,d,g,k) for a,d,g in zip(v,D,G))+sum(12*charge(a,d,g,k) for h in H for a,d,g in zip(v,D,h))
    def probe(block,k):
        S['probes']+=1;S['probe_charge']+=probe_cost(block,k);return jump(v,block,k)
    while S['raw_steps']<limit:
        remaining=limit-S['raw_steps'];best=None
        # Charge exact suffix and primitive-word comparisons even when
        # there is no repeat. Zero guard probes is not zero overhead.
        ceiling=S['admitted_literal_lower']+remaining*(1+2*n)
        if admit and not disabled and overhead()>=ceiling:
            disabled=True;S['discovery_disabled']+=1
        lmax=0 if disabled else min(len(history)//2,remaining//2)
        S['candidate_checks']+=lmax;S['bookkeeping_charge']+=1+sum(2*l+l*l for l in range(1,lmax+1))
        for p in (() if disabled else repeat_suffixes(history,remaining)):
            l=len(p);S['repeat_triggers']+=1
            if p in cache:
                block,I,failed=cache[p];cache.move_to_end(p);S['cache_hits']+=1
            else:
                # Charge declared lane-operation allowance using an operand
                # bound for all prefix displacements and shifted guards.
                width=(l+1)*m+1;cost=1+n*(len(rules)+sum(3+i for i in p))*12*charge(width,width)
                if admit and overhead()+cost>=ceiling:
                    S['preflight_skips']+=1;continue
                S['compile_charge']+=cost
                block=compile_block(rules,p);I=relevant_two(block);failed=None
            sig=tuple(v[i] for i in I);S['bookkeeping_charge']+=1+sum(1+abs(a).bit_length() for a in sig)
            if failed==sig:
                S['cooldown_skips']+=1;continue
            if admit and overhead()+probe_cost(block,2)>=ceiling:
                S['preflight_skips']+=1;continue
            end=probe(block,2)
            if cache_cap:
                cache[p]=(block,I,sig if end is None else None);cache.move_to_end(p)
                if len(cache)>cache_cap:cache.popitem(last=False)
            if end is None:continue
            low,high=2,remaining//l
            while low<high:
                mid=(low+high+1)//2
                if admit and overhead()+probe_cost(block,mid)>=ceiling:break
                e=probe(block,mid)
                if e is None:high=mid-1
                else:low=mid;end=e
            if best is None or l*low>best[0]:best=(l*low,p,low,end)
            if best[0]==remaining:break
        if best is not None:
            length,p,k,end=best
            # Each literal transition pays at least one dispatch charge,
            # n guard comparisons and n valuation updates in this tariff.
            lower=length*(1+2*n);record=2*window+len(p)+1
            if not admit or overhead()+record<S['admitted_literal_lower']+lower:
                S['admitted_literal_lower']+=lower;v=end;S['raw_steps']+=length;S['jumps']+=1;remember(p,k);continue
            S['admission_refusals']+=1
        i=None;S['literal_charge']+=1
        for j,(g,d) in enumerate(rules):
            ok=True
            for a,b in zip(v,g):
                S['literal_charge']+=charge(a,b)
                if a<b:ok=False;break
            if ok:i=j;break
        if i is None:return v,'halt',dict(S)
        S['literal_charge']+=sum(charge(a,d) for a,d in zip(v,rules[i][1]));v=tuple(a+b for a,b in zip(v,rules[i][1]));S['raw_steps']+=1;S['literal_steps']+=1;remember((i,),1)
    return v,'limit',dict(S)


def valuation_adapter(program,initial,primes,limit,**kw):
    """Actual reduced fraction program and known finite prime basis.
    Return exponent endpoint (no uncharged giant integer materialization).
    Basis validation and integer factor readout are separately charged.
    """
    from fractions import Fraction
    from sympy import isprime
    P=tuple(primes);n=len(P)
    if len(set(P))!=n or not all(isprime(p) for p in P):raise ValueError('prime basis')
    work=0
    def val(x):
        nonlocal work
        if x<1:raise ValueError('positive integer')
        out=[]
        for p in P:
            a=0
            while True:
                work+=charge(x,p)
                q,r=divmod(x,p)
                if r:break
                x=q;a+=1
            out.append(a)
        if x!=1:raise ValueError('unknown prime factor')
        return tuple(out)
    rules=[]
    for f in program:
        f=Fraction(f);g=val(f.denominator);u=val(f.numerator);rules.append((g,tuple(a-b for a,b in zip(u,g))))
    v,why,S=execute_gated(rules,val(initial),limit,**kw)
    return v,why,dict(S,factor_readout_charge=work,basis_validation_input_bits=sum(p.bit_length() for p in P))
