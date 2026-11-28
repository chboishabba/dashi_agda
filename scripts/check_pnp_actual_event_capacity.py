"""Actual event capacity on a restricted original unit-CNF SAT consumer.
A read-only input observation is not an internal observation of closed state.
This restricted family is an exact control, not a general SAT lower bound.
"""
from collections import Counter
from itertools import product

def sat(x):
    return not any(x[i] and x[i+1] for i in range(0,len(x),2))

def step(k,state,bit):
    bad,p=state
    if k%2==0:return bad,bit
    return bad or (p and bit),0

def trace(x):
    s=[(0,0)]
    for k,b in enumerate(x):s.append(step(k,s[-1],b))
    assert bool(not s[-1][0])==sat(x)
    return tuple(s)

def events(anchor,domain,cuts):
    X=trace(anchor);T=len(anchor)
    receipts=[];loads=Counter();windows=Counter()
    for y in domain:
        if sat(y)==sat(anchor):continue
        Y=trace(y)
        for a,b in cuts:
            if not 0<=a<b<=T:raise ValueError("window")
            if X[a]!=Y[a] or X[b]==Y[b]:continue
            j=next(j for j in range(a,b) if X[j+1]!=Y[j+1])
            assert X[j]==Y[j] and anchor[j]!=y[j]
            receipts.append((y,a,b,j))
            loads[j]+=1
            for k in range(a,b):windows[k]+=1
    C=max(loads.values(),default=0)
    assert len(receipts)<=T*C
    assert all(loads[k]<=windows[k] for k in range(T))
    assert len(loads)<=T
    # The original complete state also contains the read-only input.
    # Equal complete states imply equal input and same future.
    for y,a,b,j in receipts:
        assert (anchor,X[a])!=(y,trace(y)[a])
    return len(receipts),len(loads),C,max(windows.values(),default=0)

def main():
    result=[]
    for n in range(1,7):
        T=2*n;D=tuple(product((0,1),repeat=T));x=(0,)*T
        cuts=tuple((a,b) for a in range(T) for b in range(a+1,T+1))
        count,paid,C,W=events(x,D,cuts)
        assert count>0 and paid<=T and C<=W
        result.append((n,len(D)-3**n,count,paid,C,W))
    print(dict(unit_cnf_controls=result))
if __name__=="__main__":main()
