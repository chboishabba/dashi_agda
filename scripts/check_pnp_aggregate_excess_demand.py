"""Exact excess ceiling via the existing shared Tseitin gate/CNF owner."""
from check_pnp_affine_normal_components import bits,canon,chart,satisfies,Exhausted
from check_pnp_demand_strata import Allowance,ProbeLimit
from check_openai_shared_tseitin_parsimonious import optimized_clauses

def compile_excess_demand(n,R,H,caps,ceiling,B,flats=()):
    """Parsimonious extension of original hard-feasible carrier.
    All gate indices remain creation-order, as in donor.
    Returns lifted arity, original H, lifted hard flats, gates, output.
    """
    R,H,caps,flats=tuple(R),tuple(H),tuple(caps),tuple(flats)
    if n<0 or len(R)!=len(caps) or any(r<0 or r>>n for r in R) or any(c<0 for c in caps):raise ValueError('invalid source')
    if any(a<0 or a>>n or b not in (0,1) for a,b in H) or any(a<0 or a>>n or b not in (0,1) for F in flats for a,b in F):raise ValueError('invalid demand')
    B.pay('aggregate_compile_input',1+n+len(R)+sum(r.bit_count() for r in R)+len(H)+sum(map(len,flats)))
    gates=[];cache={}
    def gate(op,*args):
        B.pay('aggregate_gate_attempt')
        key=(op,args)
        if key not in cache:cache[key]=('g',len(gates));gates.append(key)
        return cache[key]
    zero=gate('const',False);one=gate('const',True)
    def binary(op,a,b):
        B.pay('aggregate_boolean')
        if a==b:return a
        if op=='and':
            if zero in (a,b):return zero
            if one in (a,b):return b if a==one else a
        else:
            if one in (a,b):return one
            if zero in (a,b):return b if a==zero else a
        return gate(op,*sorted((a,b)))
    def thresholds(W,k):
        # S[j] iff at least j bits have been seen; retain old row.
        S=[one]+[zero]*k
        for t,w in enumerate(W,1):
            B.pay('aggregate_threshold_row',1+k)
            T=list(S)
            for j in range(1,min(k,t)+1):T[j]=binary('or',S[j],binary('and',w,S[j-1]))
            S=T
        return S
    E=sum(max(0,r.bit_count()-c) for r,c in zip(R,caps))
    if ceiling<0:output=zero
    elif ceiling>=E:output=one
    else:
        excess=[]
        for r,c in zip(R,caps):
            d=r.bit_count()
            if c>=d:continue
            S=thresholds(tuple(('i',j) for j in bits(r)),d)
            excess.extend(S[c+1:])
        output=gate('not',thresholds(excess,ceiling+1)[ceiling+1])
    B.pay('aggregate_gate_cnf',1+3*len(gates))
    clauses=optimized_clauses(n,gates,output)
    G=[]
    for C in clauses:
        B.pay('aggregate_clause',1+len(C))
        F=canon((1<<j,int(not sign)) for j,sign in C)
        if F is not None:G.append(F)
    return n+len(gates),H,flats+tuple(G),tuple(gates),output

def pair_or_aggregate_trace(n,R,H,caps,x,B,flats=(),atomic_basis_block=False,lower=0,aggregate_cap=8192):
    """Bounded rank-two bypass, then exact aggregate query via existing producers."""
    from itertools import combinations
    from check_pnp_fractran_trace import trace
    from check_pnp_partial_quotient import solve as partial
    from check_pnp_collective_fibre_escape import solve as collective
    phi=lambda z:sum(max(0,(r&z).bit_count()-c) for r,c in zip(R,caps))
    start=phi(x)
    try:
        A=Allowance(B,max(0,B.left//3));A.pay('productive_pair_chart',1+n*(1+len(H)))
        _,V=chart(n,H)
        for a,b in combinations(V,2):
            A.pay('productive_pair_probe',1+n*(1+len(R)+sum(map(len,flats))))
            y=x^a^b
            if satisfies(y,H,flats) and phi(y)<start:
                t=trace(n,R,H,caps,x,y,A,flats,atomic_basis_block)
                if t is not None:return 'IMPROVED',t,lower
    except (ProbeLimit,Exhausted,RecursionError):pass
    try:
        A=Allowance(B,min(aggregate_cap,max(0,B.left//2)))
        N,Q,F,gates,output=compile_excess_demand(n,R,H,caps,start-1,A,flats)
        for k,producer in enumerate((partial,collective)):
            try:
                S=Allowance(A,max(0,A.left//(2-k)));y,_,done=producer(N,Q,F,S.left,budget=S)
                if y is None:
                    if done:return 'MINIMUM',None,start
                    continue
                B.pay('aggregate_original_verify',1+N+sum(map(len,F)))
                if not done or not satisfies(y,Q,F):raise AssertionError('invalid lifted witness')
                z=y&((1<<n)-1)
                if not satisfies(z,H,flats) or phi(z)>=start:raise AssertionError('invalid original endpoint')
                t=trace(n,R,H,caps,x,z,B,flats,atomic_basis_block)
                if t is not None:return 'IMPROVED',t,lower
            except (ProbeLimit,Exhausted,RecursionError):continue
    except (ProbeLimit,Exhausted,RecursionError):pass
    return 'UNKNOWN',None,lower
