"""Actual unit-head tape crossing sequences on separated equality inputs.
Classical crossing-sequence control, not an unrestricted DAG lower bound.
"""
from itertools import product
from collections import Counter

def run(x,y,g):
    n=len(x);assert len(y)==n and g>=1
    # A unit-head deterministic machine on promised equal-length words.
    tape=dict(enumerate(('^',)+tuple(x)+('#',)*g+tuple(y)+('$',)))
    cuts=tuple(range(n,n+g+1));words={c:[] for c in cuts};q='scan';i=1;steps=0
    def move(p,d,write=None):
        nonlocal q,i,steps
        if write is not None:tape[i]=write
        j=i+d;cut=min(i,j);q=p;steps+=1
        if d and cut in words:words[cut].append((q,d))
        i=j
    while True:
        a=tape[i]
        if q=='scan':
            if a=='X':move(q,1)
            elif a=='#':ok=True;break
            else:assert a in (0,1);move(('gap',a),1,'X')
        elif isinstance(q,tuple) and q[0]=='gap':
            b=q[1]
            if a=='#':move(('right',b),1)
            else:move(q,1)
        elif isinstance(q,tuple) and q[0]=='right':
            b=q[1]
            if a in ('#','Y'):move(q,1)
            elif a==b:move('return',-1,'Y')
            else:ok=False;break
        elif q=='return':
            if a=='^':move('scan',1)
            else:move(q,-1)
        else:raise AssertionError(q)
    crossing=sum(map(len,words.values()));assert crossing<=steps
    # Only final halt side/output, no timestamps.
    out=tuple(tuple(words[c])+((('halt',ok),int(i>c)),) for c in cuts)
    return ok,steps,crossing,out

def main():
    C=Counter()
    for n in range(1,8):
        A=list(product(range(2),repeat=n));g=n;diag=[run(x,x,g) for x in A]
        for j in range(g+1):
            W=[r[3][j] for r in diag];assert len(set(W))==len(A);C['cut_injectivity']+=len(A)
        for x,y in product(A,repeat=2):
            ok,T,K,W=run(x,y,g);assert ok==(x==y) and K<=T;C['pairs']+=1;C['crossings']+=K
        for ok,T,K,W in diag:
            assert ok and K>=2*n*g;C['diagonal']+=1
    # Abstract finite short-word counting: when g*(m+1)^K < |A|,
    # at least one input must have all words long, even when short inputs
    # differ across cuts. Use rotated variable-length injective codebooks.
    for k in range(1,7):
        A=list(range(2**(k+4)));g=3;m=2;K=k//2
        if g*(m+1)**K>=len(A):continue
        pool=[p for j in range(k+5) for p in product(range(m),repeat=j)];assert len(pool)>=len(A)
        words=lambda c,x:pool[(x+c*(K+1))%len(A)]
        assert all(len({words(c,x) for x in A})==len(A) for c in range(g))
        assert any(all(len(words(c,x))>K for c in range(g)) for x in A);C['simultaneous_controls']+=1
    print(dict(C))
if __name__=='__main__':main()
