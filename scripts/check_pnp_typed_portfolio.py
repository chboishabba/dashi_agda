"""Typed common dispatcher using the original threshold and trace owners.
Declared ContinuationAllowance, not a physical tape clock. Hard GF2 rows
are not silently reinterpreted as F3 syndrome rows.
"""
from collections import Counter
from check_p0_signed_contrast_20261125 import ContinuationAllowance
from check_pnp_affine_normal_components import Exhausted, bits, satisfies
from check_pnp_aggregate_excess_demand import compile_excess_demand
from check_openai_shared_tseitin_parsimonious import optimized_clauses
from check_pnp_source_derived_cover import source_solve
from check_pnp_fractran_trace import trace

class Work:
    def __init__(self,cap):
        self.left=cap;self.stats=Counter()
    def pay(self,tag,n=1):
        if n<0:raise ValueError("negative work")
        if n>self.left:raise Exhausted()
        self.left-=n;self.stats[tag]+=n

def reserve(root,name,cap):
    return Work(cap) if root.reserve(name,cap) else None

def cnf_dispatch(F,n,rows,target,root,cap):
    if reserve(root,"original_cnf",cap) is None:return dict(status="UNKNOWN")
    q=source_solve(F,n,rows,target,cap)
    assert q["reserved"]<=cap
    return q

def parity_cnf(N,H,flats,B):
    """Exact Boolean parity-gate bridge into the existing placed CNF.
    H: required equations. flats: forbidden conjunctions of equations.
    Existing auxiliary coordinates retain their absolute indices.
    """
    B.pay("parity_input",1+N+sum(1+a.bit_length() for a,b in H)+sum(1+a.bit_length() for F in flats for a,b in F))
    gates=[];memo={};parities={};C=[]
    def gate(op,*args):
        B.pay("parity_gate",1)
        k=(op,args)
        if k not in memo:
            memo[k]=("g",len(gates));gates.append(k)
        return memo[k]
    def parity(mask):
        if mask in parities:return parities[mask]
        B.pay("parity_mask",1+N)
        I=tuple(bits(mask))
        if not I:w=gate("const",False)
        else:
            w=("i",I[0])
            for i in I[1:]:
                v=("i",i)
                w=gate("or",gate("and",w,gate("not",v)),gate("and",gate("not",w),v))
        parities[mask]=w;return w
    def lit(a,b):
        w=parity(a);return (w[1]+1+(N if w[0]=="g" else 0))*(1 if b else -1)
    for a,b in H:C.append((lit(a,b),))
    for F in flats:C.append(tuple(lit(a,1-b) for a,b in F))
    output=gate("const",True)
    B.pay("parity_cnf_emit",1+3*len(gates)+sum(1+len(c) for c in C))
    C.extend(tuple((i+1)*(1 if b else -1) for i,b in c) for c in optimized_clauses(N,gates,output))
    return N+len(gates),tuple(C)

def hard_dispatch(n,R,H,caps,x,flats,root,cap,atomic_basis_block=False):
    """Strict actual potential improvement or a certified minimum.
    Trace-specific microsteps are only admissible at the declared macro
    boundaries. Refused trace never erases a valid improved endpoint.
    """
    if not root.reserve("hard_affine",cap):return dict(status="UNKNOWN")
    B=Work(cap)
    try:
        if n<0 or x<0 or x>>n or len(R)!=len(caps) or any(r<0 or r>>n for r in R) or any(c<0 for c in caps):raise ValueError("source")
        if any(a<0 or a>>n or b not in (0,1) for a,b in H) or any(a<0 or a>>n or b not in (0,1) for F in flats for a,b in F):raise ValueError("hard constraints")
        B.pay("hard_source",1+n*(1+len(H)+len(R)+sum(map(len,flats))))
        if not satisfies(x,H,flats):raise ValueError("hard incumbent")
        phi=lambda z:sum(max(0,(r&z).bit_count()-c) for r,c in zip(R,caps))
        start=phi(x)
        if start==0:return dict(status="SAT",witness=x,potential=0)
        N,Q,F,_,_=compile_excess_demand(n,R,H,caps,start-1,B,flats)
        N,C=parity_cnf(N,Q,F,B)
        # Same executed C1a dispatcher, now on the actual strict-demand
        # CNF. Reserve a trace portion, rather than spending it twice.
        query=B.left*3//4;B.pay("strict_demand_solve",query)
        q=source_solve(C,N,(),(),query)
        if q["status"]=="EMPTY":return dict(status="MINIMUM",witness=x,potential=start)
        if q["status"]!="WITNESS":return dict(status="UNKNOWN",query=q["status"])
        y=sum(int(b)<<i for i,b in enumerate(q["witness"][:n]))
        B.pay("hard_original_audit",1+n*(1+len(H)+len(R)+sum(map(len,flats))))
        assert satisfies(y,H,flats) and phi(y)<start
        try:
            t=trace(n,R,H,caps,x,y,B,flats,atomic_basis_block)
        except Exhausted:t=None
        return dict(status="IMPROVED" if t is not None else "IMPROVED_ENDPOINT_NO_TRACE",
                    witness=y,potential=phi(y),trace=t)
    except Exhausted:return dict(status="UNKNOWN")
