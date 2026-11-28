"""Explicit indexed mask on actual creation-order DAG; no recursive demand.
Linear number of array accesses and gate visits, not single-tape bit time.
"""
from check_pnp_dag_cutset import refs,read,restrict
from check_pnp_sparse_dag_cut import sparse_cut
from check_openai_shared_tseitin_parsimonious import eval_circuit


def scan(n,G,out,k=0):
    m=len(G)
    if n<0 or not 0<=k<=m:raise ValueError('bounds')
    inp=bytearray(n);gate=bytearray(m);live=bytearray(m);writes=visits=0
    def mark(w,bound):
        nonlocal writes
        t,i=w
        if t=='i' and 0<=i<n:inp[i]=1
        elif t=='g' and 0<=i<bound:gate[i]=1
        else:raise ValueError('wire')
        writes+=1
    mark(out,m)
    for j in range(m-1,k-1,-1):
        visits+=1
        if gate[j]:
            live[j]=1;gate[j]=0
            for w in refs(G[j]):mark(w,j)
    # Same deterministic interface ordering as sparse_cut: gate then input.
    I=tuple(('g',j) for j in range(k) if gate[j])+tuple(('i',i) for i in range(n) if inp[i])
    assert writes<=1+2*visits
    return I,live,dict(visits=visits,marks=writes)


def compile_live(n,G,out,k=0):
    I,live,stats=scan(n,G,out,k);M=[None]*len(G);X=[None]*n;S=[]
    for i,(t,j) in enumerate(I):(M if t=='g' else X)[j]=('i',i)
    def rename(w):
        t,j=w;z=(M if t=='g' else X)[j];assert z is not None;return z
    for j in range(k,len(G)):
        if not live[j]:continue
        op,args=G[j];M[j]=('g',len(S));S.append((op,args if op=='const' else tuple(map(rename,args))))
    return I,tuple(S),rename(out),stats


def main():
    from itertools import product
    from random import Random
    r=Random(3693102);cuts=points=visits=marks=0
    for n in range(1,7):
        for _ in range(32):
            W=[('i',i) for i in range(n)];G=[]
            for j in range(12):
                op=r.choice(('const','not','and','or'));a=(bool(r.randrange(2)),) if op=='const' else tuple(r.choice(W) for _ in range(1 if op=='not' else 2));G.append((op,a));W.append(('g',j))
            G=tuple(G);o=r.choice(W)
            for k in range(len(G)+1):
                I,S,p,t=compile_live(n,G,o,k);assert (I,S,p)==sparse_cut(G,o,k)
                for x in product((False,True),repeat=n):
                    y=tuple(read(x,eval_circuit(n,G[:k],x),w) for w in I)
                    assert read(y,eval_circuit(len(y),S,y),p)==read(x,eval_circuit(n,G,x),o);points+=1
                cuts+=1;visits+=t['visits'];marks+=t['marks']
    # Large shared DAG, no unrolling; linear number of original gate visits.
    for m in (1024,4096,16384,65536):
        G=(('not',(('i',0),)),)+tuple(('and',(('g',j-1),('g',j-1))) for j in range(1,m))
        I,S,p,t=compile_live(1,G,('g',m-1));assert len(S)==m and I==( ('i',0), ) and t==dict(visits=m,marks=2*m)
        print('shared',m,t)
    print(dict(cuts=cuts,pointwise=points,visits=visits,marks=marks))
if __name__=='__main__':main()
