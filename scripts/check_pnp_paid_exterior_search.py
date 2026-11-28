"""Bounded source-derived exterior search with conservative trial reservations.
No universal separator, physical bit clock or polynomial SAT claim.
"""
from itertools import combinations, product
from check_pnp_source_cluster_planner import planned_cluster_join


def paid_exterior_search(F, n, rows, target, cap, trial_cap, max_exterior, width=4):
    """Return (status, original witness, charged work, attempts).
    A refusal is never an EMPTY certificate. Every attempted planner call
    is debited its entire declared reservation, including failed calls.
    Input materialization/validation is outside this scoped logical ledger.
    """
    if min(n, cap, max_exterior, width) < 0 or trial_cap <= 0:
        raise ValueError('bounds')
    F=tuple(tuple(c) for c in F); rows=tuple(tuple(r) for r in rows); target=tuple(target)
    if len(rows)!=len(target) or any(len(r)!=n for r in rows) or any(not 1<=abs(l)<=n for c in F for l in c):
        raise ValueError('source')
    left=cap; attempts=0
    setup=1+n+sum(1+len(c) for c in F)+len(rows)*(n+1)
    if setup>left: return 'UNKNOWN',None,0,0
    left-=setup
    for size in range(min(max_exterior,n)+1):
        for E in combinations(range(n),size):
            overhead=1+n+size
            if overhead>left: return 'UNKNOWN',None,cap-left,attempts
            left-=overhead
            complete=True
            for bits in product((0,1),repeat=size):
                debit=trial_cap+overhead
                if debit>left: return 'UNKNOWN',None,cap-left,attempts
                left-=debit; attempts+=1
                x=[0]*n
                for i,b in zip(E,bits): x[i]=b
                out=planned_cluster_join(F,n,E,x,rows,target,trial_cap,width)
                if out is None:
                    complete=False
                    break
                count,witness,used=out
                if not 0<=used<=trial_cap: raise RuntimeError('invalid planner receipt')
                if count:
                    if witness is None: raise RuntimeError('missing witness')
                    return 'WITNESS',witness,cap-left,attempts
                if witness is not None: raise RuntimeError('invalid empty fibre')
            if complete:
                # All exterior assignments covered by exact zero-count fibres.
                return 'EMPTY',None,cap-left,attempts
    return 'UNKNOWN',None,cap-left,attempts
