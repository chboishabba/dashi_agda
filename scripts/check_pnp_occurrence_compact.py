"""Cook AST constructor-level occurrence compaction and reopening controls.
The native owner uses Karp's original occurrence list and first label.
This Python campaign is a reference specialization, not kernel parity.
"""
from itertools import product
from random import Random


def occurrences(f):
    if f[0]=='var':return (f[1],)
    if f[0]=='const':return ()
    return sum((occurrences(t) for t in f[1:]),())


def ev(f,x):
    op=f[0]
    if op=='var':return x(f[1])
    if op=='const':return f[1]
    if op=='not':return not ev(f[1],x)
    if op=='and':return ev(f[1],x) and ev(f[2],x)
    if op=='or':return ev(f[1],x) or ev(f[2],x)
    raise ValueError('constructor')


def compact(f):
    L=occurrences(f);first={}
    for k,i in enumerate(L):first.setdefault(i,k)
    def go(t):
        if t[0]=='var':return ('var',first[t[1]])
        if t[0]=='const':return t
        return (t[0],)+tuple(go(s) for s in t[1:])
    return L,first,go(f)


def restrict(f,b):
    if f[0]=='var':return ('const',b) if f[1]==0 else ('var',f[1]-1)
    if f[0]=='const':return f
    return (f[0],)+tuple(restrict(t,b) for t in f[1:])


def search(f,n,decide):
    x=[];Q=[]
    for _ in range(n):
        g=restrict(f,False);a=bool(decide(g));Q.append((g,a));b=not a
        x.append(b);f=g if not b else restrict(f,True)
    return tuple(x),tuple(Q)


def main():
    rng=Random(3693204);fw=bw=queries=miss=0
    def tree(k,ids):
        if k==0:return ('var',rng.choice(ids)) if rng.randrange(4) else ('const',bool(rng.randrange(2)))
        op=rng.choice(('not','and','or'))
        return (op,tree(k-1,ids)) if op=='not' else (op,tree(k-1,ids),tree(k-1,ids))
    for j in range(320):
        ids=(0,1,7,1<<256,(1<<8192)+17);f=tree(rng.randrange(4),ids);L,M,g=compact(f);n=len(L)
        for y in product((False,True),repeat=len(M)):
            a=dict(zip(M,y));x=tuple(a[i] for i in L)
            assert ev(g,x.__getitem__)==ev(f,a.__getitem__);fw+=1
        for x in product((False,True),repeat=n):
            assert ev(g,x.__getitem__)==ev(f,lambda i:x[M[i]]);bw+=1
        def sat(t):
            P=tuple(dict.fromkeys(occurrences(t)))
            return any(ev(t,dict(zip(P,y)).__getitem__) for y in product((False,True),repeat=len(P)))
        if sat(f):
            x,Q=search(g,n,sat);assert len(Q)==n and ev(f,lambda i:x[M[i]]);queries+=len(Q)
            x,Q=search(g,n,lambda _:False)
            if not ev(f,lambda i:x[M[i]]):assert any(sat(t)!=a for t,a in Q);miss+=1
    # Actual repeated huge source label: never split into distinct bits.
    v=('var',(1<<8192)+17);f=('and',v,('not',v));L,M,g=compact(f)
    assert len(L)==2 and len(M)==1 and not any(ev(g,x.__getitem__) for x in product((False,True),repeat=2))
    print(dict(formulas=320,forward=fw,backward=bw,exact_queries=queries,missed_source_controls=miss,huge_repeated_label=1))
if __name__=='__main__':main()
