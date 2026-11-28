"""Actual signed continuation positive-witness consumer, without a model oracle.
UNKNOWN is not UNSAT. Each k attempt gets one shared reservation across
all coefficient, translation and original-bit recovery queries.
"""
from fractions import Fraction as Q
from check_p0_signed_contrast_20261125 import canon,accepts,matrix,coefficient,translation,sector,refine,ContinuationAllowance

def search(F,n,allowance_per_k=1048576,split_budget=4,exact_probe_budget=0):
    if min(n,allowance_per_k,split_budget,exact_probe_budget)<0:raise ValueError('bounds')
    F=tuple(tuple(c) for c in F)
    if any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError('literal')
    F=canon(F);attempts=[]
    if n==0:return (() if accepts(F,()) else None),attempts
    for k in range(1,n+2):
        ledger=ContinuationAllowance(allowance_per_k);P=();B=();bits=[];steps=[];why='continuation refusal';L=n+2*k-1
        def query(roots,eps):
            lo,hi,ds,done=refine(roots,eps,split_budget,exact_probe_budget=exact_probe_budget,ledger=ledger)
            d=max(ds,key=lambda d:(lo[d],-d)) if ds else None
            steps.append(dict(direction=d,lo=tuple(map(str,lo)),hi=tuple(map(str,hi)),splits=done,spent=ledger.total-ledger.left))
            return d
        for _ in range(L):
            roots=coefficient(F,n,k,P,ledger=ledger) if len(P)<n+k-1 else translation(F,n,k,P,B,ledger=ledger)
            d=query(roots,Q(1,8*L))
            if d is None:break
            if len(P)<n+k-1:P+=(d,)
            else:B+=(d,)
        else:
            # Terminal positive singleton => exactly one Boolean label has
            # contrast +2. Require a certified STRICTLY positive direction,
            # never infer a witness from a zero/common-mode character.
            A=matrix(n,k,P);why='bit recovery refusal'
            for i in range(n):
                d=query([sector(F,n,A,B,tuple(int(i==j) for j in range(n)),Q(1),ledger=ledger)],-Q(1))
                if d not in (0,1):break
                bits.append(d)
            else:
                x=tuple(bits)
                if accepts(F,x) and tuple(sum(a*b for a,b in zip(row,x))%3 for row in A)==B:why='witness'
                else:why='original verification refusal'
        attempts.append(dict(k=k,seed=P,target=B,bits=tuple(bits),status=why,steps=steps,charges=dict(ledger.charges),reserved=ledger.total-ledger.left,baseline_cells=ledger.baseline_cells,boundary_attempts=ledger.boundary_attempts))
        assert sum(ledger.charges.values())+ledger.left==allowance_per_k
        if why=='witness':return tuple(bits),attempts
    return None,attempts
