"""Actual shared-gate DAG cut and restriction, on the donor creation-order ABI."""
from itertools import product
from random import Random
from check_openai_shared_tseitin_parsimonious import eval_circuit


def refs(g):
    op,args=g
    return () if op=='const' else args


def cut(n,gates,out,k):
    assert 0<=k<=len(gates)
    live=tuple(sorted({w for w in (out,)+tuple(w for g in gates[k:] for w in refs(g))
                       if w[0]=='i' or w[1]<k}))
    slot={w:('i',i) for i,w in enumerate(live)}
    def rename(w):return slot[w] if w in slot else ('g',w[1]-k)
    suffix=tuple((op,args if op=='const' else tuple(map(rename,args))) for op,args in gates[k:])
    return live,suffix,rename(out)


def read(x,v,w):return (x if w[0]=='i' else v)[w[1]]


def restrict(n,gates,out,pin):
    """Simplify once per original gate; preserve all shared references.
    Constants are explicit in the output cost, not free new gates.
    """
    C=[];mapping={('i',i):pin.get(i,('i',i)) for i in range(n)}
    def const(v):return isinstance(v,bool)
    def emit(op,args):
        w=('g',len(C));C.append((op,args));return w
    for j,(op,args) in enumerate(gates):
        a=tuple(mapping[w] for w in args) if op!='const' else args
        if op=='const':v=bool(a[0])
        elif op=='not':v=not a[0] if const(a[0]) else emit(op,a)
        elif a[0]==a[1]:v=a[0]
        elif any(const(w) for w in a):
            b,w=a if const(a[0]) else a[::-1]
            v=(w if b else False) if op=='and' else (True if b else w)
        else:v=emit(op,a)
        mapping['g',j]=v
    w=mapping[out]
    if const(w):w=emit('const',(w,))
    # Remove all dead gates, including gates disconnected by restriction.
    needed=set();todo=[w]
    while todo:
        a=todo.pop()
        if a[0]=='g' and a[1] not in needed:
            needed.add(a[1]);todo.extend(refs(C[a[1]]))
    ix={j:i for i,j in enumerate(sorted(needed))}
    move=lambda w:('g',ix[w[1]]) if w[0]=='g' else w
    return tuple((op,args if op=='const' else tuple(map(move,args))) for j,(op,args) in enumerate(C) if j in needed),move(w)


def main():
    rng=Random(369);cuts=checks=restrictions=eliminated=0
    for n in range(1,6):
        for _ in range(24):
            gates=[];W=[('i',i) for i in range(n)]
            for j in range(8):
                op=rng.choice(('const','not','and','or'))
                args=(bool(rng.randrange(2)),) if op=='const' else tuple(rng.choice(W) for _ in range(1 if op=='not' else 2))
                gates.append((op,args));W.append(('g',j))
            gates=tuple(gates);out=rng.choice(W)
            for k in range(len(gates)+1):
                live,suffix,o=cut(n,gates,out,k);cuts+=1
                for x in product((False,True),repeat=n):
                    full=eval_circuit(n,gates,x);pre=eval_circuit(n,gates[:k],x)
                    y=tuple(read(x,pre,w) for w in live)
                    assert read(y,eval_circuit(len(y),suffix,y),o)==read(x,full,out)
                    checks+=1
            for i,b in product(range(n),(False,True)):
                C,o=restrict(n,gates,out,{i:b});assert len(C)<=len(gates)+1
                restrictions+=1;eliminated+=len(C)<len(gates)
                for x in product((False,True),repeat=n):
                    z=x[:i]+(b,)+x[i+1:]
                    assert read(x,eval_circuit(n,C,x),o)==read(z,eval_circuit(n,gates,z),out)
    # A gate-only cut loses an input that bypasses the prefix.
    G=(('not',(('i',0),)),('and',(('g',0),('i',1))))
    live,_,_=cut(2,G,('g',1),1);assert live==(('g',0),('i',1))
    print(dict(cuts=cuts,pointwise=checks,restrictions=restrictions,strict_eliminations=eliminated,bypass=1))
if __name__=='__main__':main()
