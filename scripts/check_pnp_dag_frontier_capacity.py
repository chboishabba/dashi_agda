"""Actual output cone: fan-in expansion charges distinct original gates.
This proves only an essential-input lower bound, not unrestricted SAT work.
"""
from check_pnp_dag_cutset import refs,read
from check_openai_shared_tseitin_parsimonious import eval_circuit
from check_pnp_sparse_dag_cut import sparse_cut
from random import Random
from itertools import product


def cone(G,out):
    need={out};binary=0;trace=[]
    for j in range(len(G)-1,-1,-1):
        w=('g',j)
        if w not in need:continue
        operands=set(refs(G[j]));before=len(need)
        need.remove(w);need.update(operands)
        charge=max(0,len(operands)-1);binary+=charge
        assert len(need)<=before+charge
        trace.append((j,before,len(need),charge))
    assert all(w[0]=='i' for w in need) and len(need)<=1+binary
    return need,binary,trace


def main():
    rng=Random(3693004);cases=points=essential=0
    for n in range(1,7):
        for _ in range(64):
            G=[];W=[('i',i) for i in range(n)]
            for j in range(14):
                op=rng.choice(('const','not','and','or'));args=(bool(rng.randrange(2)),) if op=='const' else tuple(rng.choice(W) for _ in range(1 if op=='not' else 2))
                G.append((op,args));W.append(('g',j))
            out=rng.choice(W);G=tuple(G);need,binary,tr=cone(G,out)
            assert need==set(sparse_cut(G,out,0)[0]);truth={x:read(x,eval_circuit(n,G,x),out) for x in product((False,True),repeat=n)};E=set()
            for x,v in truth.items():
                for i in range(n):
                    if truth[x[:i]+(not x[i],)+x[i+1:]]!=v:E.add(('i',i))
                    points+=1
            assert E<=need and len(E)<=1+binary;essential+=len(E);cases+=1
    # Sharp bound on original AND family; each input essential.
    for n in (2,4,8,16,32,64,128):
        G=tuple(('and',( ('i',0) if j==0 else ('g',j-1),('i',j+1))) for j in range(n-1));out=('g',n-2)
        need,b,tr=cone(G,out);assert b==n-1 and len(need)==n
        x=(True,)*n;assert read(x,eval_circuit(n,G,x),out)
        for i in range(n):
            y=x[:i]+(False,)+x[i+1:];assert not read(y,eval_circuit(n,G,y),out)
    print(dict(cases=cases,sensitivity_comparisons=points,essential=essential,sharp_AND=7))
if __name__=='__main__':main()
