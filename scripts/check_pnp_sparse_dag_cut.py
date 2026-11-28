"""Output-backward live cut on the actual shared DAG, retaining bypasses."""
from check_pnp_dag_cutset import refs,read,cut,restrict
from check_openai_shared_tseitin_parsimonious import eval_circuit
from itertools import product
from random import Random


def sparse_cut(gates,out,k):
    if not 0<=k<=len(gates):raise ValueError('cut')
    need={out};keep=[]
    for j in range(len(gates)-1,k-1,-1):
        w=('g',j)
        if w in need:
            need.remove(w);need.update(refs(gates[j]));keep.append(j)
    live=tuple(sorted(need));keep=tuple(reversed(keep))
    assert all(w[0]=='i' or w[1]<k for w in live)
    slot={w:('i',i) for i,w in enumerate(live)}
    slot.update({('g',j):('g',i) for i,j in enumerate(keep)})
    suffix=tuple((op,args if op=='const' else tuple(slot[w] for w in args)) for op,args in (gates[j] for j in keep))
    return live,suffix,slot[out]


def main():
    rng=Random(36927);cuts=points=smaller=pruned=restrictions=0
    for n in range(1,6):
        for _ in range(32):
            W=[('i',i) for i in range(n)];G=[]
            for j in range(10):
                op=rng.choice(('const','not','and','or'));a=(bool(rng.randrange(2)),) if op=='const' else tuple(rng.choice(W) for _ in range(1 if op=='not' else 2))
                G.append((op,a));W.append(('g',j))
            G=tuple(G);out=rng.choice(W)
            for k in range(len(G)+1):
                live,S,o=sparse_cut(G,out,k);old,_,_=cut(n,G,out,k)
                assert set(live)<=set(old) and len(S)<=len(G)-k
                smaller+=len(live)<len(old);pruned+=len(G)-k-len(S);cuts+=1
                for x in product((False,True),repeat=n):
                    v=eval_circuit(n,G[:k],x);y=tuple(read(x,v,w) for w in live)
                    assert read(y,eval_circuit(len(y),S,y),o)==read(x,eval_circuit(n,G,x),out);points+=1
            # Actual restriction, then output-backward cut, not an oracle.
            for b in (False,True):
                C,o=restrict(n,G,out,{0:b});live,S,p=sparse_cut(C,o,len(C)//2)
                for x in product((False,True),repeat=n):
                    y=tuple(read(x,eval_circuit(n,C[:len(C)//2],x),w) for w in live)
                    assert read(y,eval_circuit(len(y),S,y),p)==read((b,)+x[1:],eval_circuit(n,G,(b,)+x[1:]),out)
                    restrictions+=1
    print(dict(cuts=cuts,pointwise=points,strict_live_reduction=smaller,pruned_gate_occurrences=pruned,restricted_pointwise=restrictions))
if __name__=='__main__':main()
