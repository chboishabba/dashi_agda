"""Original Boolean support from the existing signed ternary observer.
No isolation or model-count oracle. A zero upper mass is an EMPTY receipt;
noncompletion remains UNKNOWN. Capped logical ledger, not physical bit time.
"""
from fractions import Fraction as Q
from math import ceil,floor
from check_p0_signed_contrast_20261125 import cell,refine,canon,accepts,ContinuationAllowance


def child_bounds(lo,hi,parent_lower=0,parent_upper=None):
    # Delta2=-m, Delta0=3*c0-m, Delta1=3*c1-m.
    mlo=max(0,parent_lower,ceil(-hi[2]));mhi=floor(-lo[2])
    if parent_upper is not None:mhi=min(mhi,parent_upper)
    L=[max(0,ceil(Q(lo[d]+mlo)/3)) for d in (0,1)]
    U=[min(mhi,floor(Q(hi[d]+mhi)/3)) for d in (0,1)]
    a,b=L;u,v=U
    L=(max(a,mlo-v),max(b,mlo-u));U=(min(u,mhi-b),min(v,mhi-a))
    assert mlo<=mhi and all(0<=a<=b for a,b in zip(L,U))
    return L,U,mlo,mhi


def direct(F,n,ledger,rows=(),target=(),split_budget=4,exact_probe_budget=0,cell_options=None):
    """Return (WITNESS/EMPTY/UNKNOWN, original bits or None, receipts).
    All prefixes are original unit clauses. One observer query per bit,
    with optional refinement only when the existing bounds cannot progress.
    """
    F=tuple(tuple(c) for c in F);rows=tuple(tuple(r) for r in rows);target=tuple(target)
    if n<0 or len(rows)!=len(target) or any(len(r)!=n for r in rows) or any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError('source')
    F=canon(F)
    opt={} if cell_options is None else dict(cell_options)
    if 'ledger' in opt:raise ValueError('ledger')
    valid=lambda x:accepts(F,x) and tuple(sum(a*b for a,b in zip(r,x))%3 for r in rows)==target
    if n==0:return ('WITNESS',(),[]) if valid(()) else ('EMPTY',None,[])
    G=F;x=[];receipts=[];lower=0;upper=1<<n
    for i in range(n):
        cols=tuple(tuple(r[j]%3 for r in rows)+(int(j==i),) for j in range(n))
        root=cell(G,cols,target,0,tuple(range(n)),Q(1),ledger=ledger,**opt)
        lo,hi=((Q(0),)*3,(Q(0),)*3) if root is None else (root[-2],root[-1])
        L,U,mlo,mhi=child_bounds(lo,hi,lower,upper);splits=0
        if mhi and not max(L) and root is not None and (split_budget or exact_probe_budget):
            lo,hi,_,splits=refine([root],-Q(1),split_budget,exact_probe_budget=exact_probe_budget,ledger=ledger,cell_options=opt)
            L,U,mlo,mhi=child_bounds(lo,hi,lower,upper)
        d=max(range(2),key=lambda j:(L[j],-j)) if max(L)>0 else None
        receipts.append(dict(i=i,lo=L,hi=U,parent=(mlo,mhi),chosen=d,splits=splits,reserved=ledger.total-ledger.left))
        if mhi==0:
            assert i==0,'certified inhabited prefix became empty'
            return 'EMPTY',None,receipts
        if d is None:return 'UNKNOWN',None,receipts
        x.append(d);lower,upper=L[d],U[d];G=canon(G+((i+1 if d else -i-1,),))
    x=tuple(x);assert valid(x)
    return 'WITNESS',x,receipts


def classify(F,n,ledger,known=None,**kw):
    """Clipped support: EMPTY, SINGLETON, MULTIPLE, UNKNOWN.
    A verified original anchor is enough to start. A blocker deletes
    exactly that witness. No noncompletion is interpreted as singleton.
    """
    F=tuple(tuple(c) for c in F);rows=kw.get('rows',());target=tuple(kw.get('target',()))
    if known is None:
        status,x,first=direct(F,n,ledger,**kw)
        if status!='WITNESS':return status,(),(first,[])
    else:
        x=tuple(known);first=[]
        if len(x)!=n or any(a not in (0,1) for a in x) or not accepts(F,x) or tuple(sum(a*b for a,b in zip(r,x))%3 for r in rows)!=target:raise ValueError('anchor')
    blocker=tuple(-i-1 if a else i+1 for i,a in enumerate(x))
    status,y,second=direct(F+(blocker,),n,ledger,**kw)
    if status=='EMPTY':return 'SINGLETON',(x,),(first,second)
    if status=='WITNESS':
        assert x!=y
        return 'MULTIPLE',(x,y),(first,second)
    return 'UNKNOWN',(x,),(first,second)


def identity_isolation(x):
    """Existing Toeplitz indexing A[i,j]=p[n-1+i-j], target b=A*x."""
    n=len(x)
    if not n:return (),()
    if any(a not in (0,1) for a in x):raise ValueError('bits')
    return (0,)*(n-1)+(1,)+(0,)*(n-1),tuple(x)


def guarded(F,n):
    """Actual known-anchor construction; no aux bits needed for CNF.
    selector is variable n+1. Residual selector 1 preserves F.
    """
    s=n+1
    return canon(tuple((s,-i-1) for i in range(n))+tuple((-s,)+tuple(c) for c in F))
