"""Witness-to-trace adapter; no endpoint search or unrestricted contraction claim."""
from check_pnp_affine_normal_components import bits, canon, chart, satisfies

def trace(n,R,H,caps,x,y,B,flats=(),atomic_basis_block=False):
    """Return signed macro receipt, or None on nonimprovement/prefix refusal.
    Budget exceptions propagate; caller must retain original state.
    Hard nonlinear flats are checked at macro boundaries, not microstates.
    """
    R,H,caps,flats=tuple(R),tuple(H),tuple(caps),tuple(flats)
    B.pay('trace_input',1+n*(1+len(H)+len(R)+sum(map(len,flats))))
    if len(R)!=len(caps) or any(r<0 or r>>n for r in R) or any(c<0 for c in caps):
        raise ValueError('invalid capacity source')
    if any(a<0 or a>>n or b not in (0,1) for a,b in H) or any(a<0 or a>>n or b not in (0,1) for F in flats for a,b in F):
        raise ValueError('invalid demand')
    if any(z<0 or z>>n for z in (x,y)) or not all(satisfies(z,H,flats) for z in (x,y)):
        raise ValueError('endpoint outside demand')
    Q=canon(H)
    if Q is None: raise ValueError('inconsistent demand')
    u,V=chart(n,Q)
    piv={a.bit_length()-1 for a,b in Q}
    free=[i for i in range(n) if i not in piv]
    residual=lambda z: tuple((r&z).bit_count()-c for r,c in zip(R,caps))
    potential=lambda r:sum(max(0,a) for a in r)
    initial=residual(x);target=residual(y)
    if potential(target)>=potential(initial):return None
    state=x;rr=initial;out=[]
    active=tuple(v for j,v in zip(free,V) if ((x^y)>>j&1))
    if atomic_basis_block:
        # Only caller-authorized endpoint semantics: internal units remain
        # visible but are not required to be source-admissible checkpoints.
        block=0
        for v in active:block^=v
        active=(block,) if block else ()
    for v in active:
        B.pay('trace_macro',1+n*(1+len(H)+len(R)+sum(map(len,flats))))
        nxt=state^v
        if not satisfies(nxt,H,flats):return None
        signed=tuple((i,1-2*((state>>i)&1)) for i in bits(v))
        micro=state;cur=list(rr);units=[]
        for i,d in signed:
            B.pay('trace_unit',1+n+len(R))
            # One-hot Boolean prime tags (coordinate, sign): symbolic
            # numerator/denominator, not expanded integers or runtime claims.
            before=(micro>>i)&1
            if d!=1-2*before:raise AssertionError('orientation')
            micro^=1<<i
            dr=tuple(d*((r>>i)&1) for r in R)
            cur=[a+b for a,b in zip(cur,dr)]
            if tuple(cur)!=residual(micro):raise AssertionError('residual')
            units.append(dict(coord=i,delta=d,denominator=(i,before),
                              numerator=(i,1-before),state=micro,
                              delta_residual=dr,residual=tuple(cur)))
        if micro!=nxt or tuple(cur)!=residual(nxt):raise AssertionError('decode')
        out.append(dict(before=state,after=nxt,basis=v,units=units,
                        residual=tuple(cur),potential=potential(cur)))
        state=nxt;rr=tuple(cur)
    if state!=y or rr!=target:raise AssertionError('endpoint')
    return dict(start=x,end=y,demand=H,hard_flats=flats,rows=R,caps=caps,
                initial=initial,final=target,macros=out,
                decrease=potential(initial)-potential(target),
                atomic_basis_block=atomic_basis_block)

def recover_trace(n,R,H,caps,x,B,signed_screen=False,flats=()):
    """Existing consumer owns discovery; receipt is optional and transactional."""
    from check_pnp_capacity_partition import recover_cell
    from check_pnp_demand_strata import ProbeLimit
    from check_pnp_affine_normal_components import Exhausted
    R,H,caps,flats=tuple(R),tuple(H),tuple(caps),tuple(flats)
    Q=canon(H)
    if Q is None or not satisfies(x,H,flats):raise ValueError('invalid start')
    # Existing capacity recovery is specialized to odd row weights.
    if canon(Q+tuple((r,1) for r in R))!=Q:return None
    from check_pnp_demand_strata import Allowance
    try:
        v=recover_cell(n,R,Q,caps,Allowance(B,max(0,B.left//2)),signed_screen=signed_screen)
        if v.witness is None:return None
        if not satisfies(v.witness,H,flats):return None
        return trace(n,R,H,caps,x,v.witness,B,flats)
    except (ProbeLimit,Exhausted,RecursionError):return None


def improve_trace(n,R,H,caps,x,B,flats=(),leaf_cap=8,seam_cap=8,atomic_basis_block=False):
    """Find a strict aggregate improvement by the existing separator fold.
    Return (status, receipt, lower). A lower bound is for the hard-feasible carrier,
    not a claim that hard nonlinear prefixes are reachable.
    """
    from check_pnp_separator_row_strata import build, minimum_excess
    from check_pnp_demand_strata import Allowance, ProbeLimit
    from check_pnp_affine_normal_components import Exhausted
    R,H,caps,flats=tuple(R),tuple(H),tuple(caps),tuple(flats)
    if n<0 or x<0 or x>>n or len(R)!=len(caps) or any(r<0 or r>>n for r in R) or any(c<0 for c in caps):
        raise ValueError('invalid source')
    Q=canon(H)
    if Q is None or not satisfies(x,H,flats):raise ValueError('invalid start')
    phi=sum(max(0,(r&x).bit_count()-c) for r,c in zip(R,caps))
    if phi==0:return 'SAT',None,0
    if not R or canon(Q+tuple((r,1) for r in R))!=Q:return 'UNKNOWN',None,0
    lower=0
    try:
        A=Allowance(B,max(0,B.left//2))
        G=build(n,R,Q,A,leaf_cap,seam_cap,hard_flats=flats)
        if G is None:return 'UNKNOWN',None,0
        lower,y=minimum_excess(n,R,Q,caps,G,A,hard_flats=flats)
        if lower is None:raise AssertionError('incumbent is a hard-feasible point')
        if lower>=phi:return 'MINIMUM',None,lower
        if not satisfies(y,H,flats):return 'UNKNOWN',None,lower
        receipt=trace(n,R,H,caps,x,y,B,flats,atomic_basis_block=atomic_basis_block)
        if receipt is None:return 'UNKNOWN',None,lower
        return 'IMPROVED',receipt,lower
    except (ProbeLimit,Exhausted,RecursionError):return 'UNKNOWN',None,lower


def productive_trace(n,R,H,caps,x,B,flats=(),leaf_cap=8,seam_cap=8,
                     atomic_basis_block=False,aggregate_cap=8192):
    """Shared-clock sufficient-observation portfolio. No width or progress oracle.
    Return status, receipt, certified lower bound on the original hard carrier.
    A verified zero endpoint is useful even if its trace refuses; use
    productive_trace only when the caller actually requires a trace.
    """
    from check_pnp_demand_strata import Allowance, ProbeLimit
    from check_pnp_affine_normal_components import Exhausted
    from check_pnp_capacity_geometry import violation_flats
    from check_pnp_partial_quotient import solve as partial
    from check_pnp_collective_fibre_escape import solve as collective
    R,H,caps,flats=tuple(R),tuple(H),tuple(caps),tuple(flats)
    if n<0 or x<0 or x>>n or len(R)!=len(caps) or any(r<0 or r>>n for r in R) or any(c<0 for c in caps):
        raise ValueError('invalid source')
    Q=canon(H)
    if Q is None or not satisfies(x,H,flats):raise ValueError('invalid incumbent')
    w=tuple((r&x).bit_count() for r in R)
    phi=sum(max(0,a-c) for a,c in zip(w,caps))
    if phi==0:return 'SAT',None,0
    lower=0
    try:
        status,t,lower=improve_trace(n,R,Q,caps,x,Allowance(B,max(0,B.left//3)),
                                     flats,leaf_cap,seam_cap,atomic_basis_block)
        if status!='UNKNOWN':return status,t,lower
        # Cheap source-derived legal chart moves; retain all residual components.
        A=Allowance(B,max(0,B.left//4))
        try:
            A.pay('productive_chart',1+n*(1+len(Q)))
            _,V=chart(n,Q)
            for v in V:
                A.pay('productive_basis_probe',1+n*(1+len(R)+sum(map(len,flats))))
                y=x^v
                if satisfies(y,Q,flats) and sum(max(0,(r&y).bit_count()-c) for r,c in zip(R,caps))<phi:
                    t=trace(n,R,Q,caps,x,y,A,flats,atomic_basis_block)
                    if t is not None:return 'IMPROVED',t,lower
        except (ProbeLimit,Exhausted):pass
        if canon(Q+tuple((r,1) for r in R))!=Q:
            from check_pnp_aggregate_excess_demand import pair_or_aggregate_trace
            return pair_or_aggregate_trace(n,R,Q,caps,x,B,flats,atomic_basis_block,lower,aggregate_cap)
        # Zero target permits arbitrary compensating changes. Additional
        # demands enforce rowwise nonincreasing excess with one strict repair.
        ceiling=tuple(max(a,c) for a,c in zip(w,caps))
        demands=[caps]
        for i,(a,c) in enumerate(zip(w,caps)):
            if a>c:
                q=list(ceiling);q[i]=a-1
                demands.append(tuple(q))
        demands=tuple(dict.fromkeys(demands))
        for j,C in enumerate(demands):
            try:
                A=Allowance(B,max(0,B.left//(2*(len(demands)-j))))
                A.pay('productive_demand',1+len(R))
                F=violation_flats(n,R,Q,C,A)+flats
                for k,producer in enumerate((partial,collective)):
                    try:
                        S=Allowance(A,max(0,A.left//(2-k)))
                        y,_,done=producer(n,Q,F,S.left,budget=S)
                        if y is None:
                            if done and j==0:lower=max(lower,1)
                            continue
                        if not done or not satisfies(y,Q,F) or any((r&y).bit_count()>c for r,c in zip(R,C)):
                            raise AssertionError('invalid producer witness')
                        t=trace(n,R,Q,caps,x,y,B,flats,atomic_basis_block)
                        if t is not None:return 'IMPROVED',t,lower
                    except (ProbeLimit,Exhausted,RecursionError):continue
            except (ProbeLimit,Exhausted,RecursionError):continue
    except (ProbeLimit,Exhausted,RecursionError):pass
    from check_pnp_aggregate_excess_demand import pair_or_aggregate_trace
    return pair_or_aggregate_trace(n,R,Q,caps,x,B,flats,atomic_basis_block,lower,aggregate_cap)


def realize_ordered_trace(n,receipt,bridge,primes,B):
    """Use FRACDASH bridge_macro_common (caller supplies actual module).
    One extra control prime per program position forces ordered execution,
    including repeated coordinate swaps; this is a trace-specific program,
    not a uniform SAT solver. Prime generation is external, validation paid.
    """
    from fractions import Fraction
    from sympy import isprime
    units=tuple(u for m in receipt['macros'] for u in m['units'])
    L=len(units)
    primes=tuple(primes)
    if len(primes)!=3*n+L+1:raise ValueError('prime basis size')
    B.pay('prime_basis_validation',1+sum(p.bit_length()**2 for p in primes))
    if len(set(primes))!=len(primes) or not all(isprime(p) for p in primes):
        raise ValueError('non-distinct or nonprime basis')
    registers=tuple(str(i) for i in range(n))
    lane={r:dict(zip(('negative','zero','positive'),primes[3*i:3*i+3]))
          for i,r in enumerate(registers)}
    phase=primes[3*n:]
    def state(z):
        return {r:('positive' if z>>i&1 else 'zero') for i,r in enumerate(registers)}
    x=receipt['start'];z=x
    initial=bridge.encode_state_integer(state(x),registers,lane)*phase[0]
    program=[]
    R,caps=receipt['rows'],receipt['caps']
    for t,u in enumerate(units):
        B.pay('prime_compile_unit',1+n+len(R))
        i,d=u['coord'],u['delta']
        if not 0<=i<n or d!=1-2*((z>>i)&1):raise ValueError('invalid unit')
        vector=[0]*n;vector[i]=d
        nxt,f=bridge.apply_unit_step(state(z),vector,registers,lane)
        z^=1<<i
        if nxt!=state(z) or u['state']!=z or u['residual']!=tuple((r&z).bit_count()-c for r,c in zip(R,caps)):
            raise ValueError('invalid receipt')
        program.append(f*Fraction(phase[t+1],phase[t]))
    if z!=receipt['end']:raise ValueError('invalid endpoint')
    # Unique active phase makes at most L rules fire. Charge the full scan
    # count and a conservative explicit integer-size proxy before execution.
    width=sum(max(p.bit_length() for p in lane[r].values()) for r in registers)+max(p.bit_length() for p in phase)
    B.pay('prime_ordered_replay',1+(L+1)*(L+1)*(1+width**2))
    final,indices,integers=bridge.fractran_execute(initial,program)
    if indices!=list(range(L)) or len(integers)!=L+1 or integers[-1]!=final:
        raise AssertionError('priority or halt mismatch')
    for t,a in enumerate(integers):
        if a%phase[t]:raise AssertionError('phase mismatch')
        decoded=bridge.decode_integer_state(a//phase[t],registers,lane)
        if decoded!=state(x if t==0 else units[t-1]['state']):
            raise AssertionError('decode mismatch')
    return dict(program=tuple(map(str,program)),indices=tuple(indices),
                integers=tuple(integers),final=final,prime_basis=primes)
