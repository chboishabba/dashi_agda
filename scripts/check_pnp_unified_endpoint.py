"""One endpoint scheduler for the original Boolean source.
Full reservation of each attempted route; declared units, NOT physical time.
Legacy exact EMPTY is distinct from witness-only completion.
"""
from check_pnp_binary_support_endpoint import direct,identity_isolation
from check_pnp_constructive_descent import search
from check_p0_signed_contrast_20261125 import accepts,ContinuationAllowance

def solve(F,n,cap,*,legacy=True,shares=None,direct_options=None):
    if min(n,cap)<0:raise ValueError('budget/source')
    F=tuple(tuple(c) for c in F)
    if any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError('literal')
    shares=(cap//2,cap//4,cap-cap//2-cap//4) if shares is None else tuple(shares)
    if len(shares)!=3 or min(shares)<0 or sum(shares)>cap:raise ValueError('shares')
    receipts=[];remaining=cap
    def reserve(name,k):
        nonlocal remaining
        assert 0<=k<=remaining
        remaining-=k
        d=dict(route=name,allocated=k);receipts.append(d);return d
    def finish(status,x):
        if status=='WITNESS':assert len(x)==n and all(v in (0,1) for v in x) and accepts(F,x)
        else:assert x is None
        assert sum(r['allocated'] for r in receipts)+remaining==cap
        return status,x,dict(total=cap,left=remaining,attempts=receipts)
    d=reserve('binary',shares[0]);ledger=ContinuationAllowance(shares[0])
    status,x,rec=direct(F,n,ledger,**(direct_options or {}))
    d.update(status=status,actual_reserved=ledger.total-ledger.left,queries=rec,baseline_cells=ledger.baseline_cells,boundary_attempts=ledger.boundary_attempts)
    if status!='UNKNOWN':return finish(status,x)
    if legacy:
        d=reserve('normal-quotient-portfolio',shares[1])
        from check_p0_correlated_marginal_20261126 import portfolio
        try:y,done,route=portfolio(n,(),F,shares[1])
        except RecursionError:y,done,route=None,False,'recursion-refusal'
        status='WITNESS' if y is not None else 'EMPTY' if done else 'UNKNOWN'
        d.update(status=status,inner_route=route)
        if status!='UNKNOWN':return finish(status,tuple((y>>i)&1 for i in range(n)) if y is not None else None)
    d=reserve('signed-seed',shares[2]);per=shares[2]//(n+1)
    x,rec=search(F,n,per)
    assert sum(a['reserved'] for a in rec)<=shares[2]
    d.update(status='WITNESS' if x is not None else 'UNKNOWN',per_scale=per,scales=rec)
    return finish(d['status'],x)

def classify(F,n,cap,known=None,**options):
    F=tuple(tuple(c) for c in F)
    if n<0 or cap<0 or any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError('source')
    # One outer reservation; anchor callers can give the entire cap to the puncture.
    if 'shares' in options:raise ValueError('classification allocates its own shares')
    if known is None:
        first=cap//2;status,x,rec=solve(F,n,first,**options)
        if status!='WITNESS':return status,(),(rec,)
    else:
        first=0;x=tuple(known);rec=None
        if len(x)!=n or any(v not in (0,1) for v in x) or not accepts(F,x):raise ValueError('anchor')
    block=tuple(-i-1 if a else i+1 for i,a in enumerate(x))
    status,y,tail=solve(F+(block,),n,cap-first,**options)
    if status=='EMPTY':return 'SINGLETON',(x,),(rec,tail)
    if status=='WITNESS':
        assert x!=y;return 'MULTIPLE',(x,y),(rec,tail)
    return 'UNKNOWN',(x,),(rec,tail)
