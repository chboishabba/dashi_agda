"""Replay composed first-enabled block summaries against literal execution."""
from random import Random
from collections import Counter
from check_pnp_fractran_guarded_block import compile_block,compile_reduced,compose,jump

def literal(v,rules,chosen,k):
    for i in chosen*k:
        j=next((j for j,(g,d) in enumerate(rules) if all(a>=b for a,b in zip(v,g))),None)
        if i!=j:return None
        v=tuple(a+b for a,b in zip(v,rules[i][1]))
    return v

def main():
    s=Counter()
    for i in range(8192):
        r=Random(3692817+i);n=r.randrange(1,5);D=[tuple(r.randrange(-3,5) for _ in range(n)) for _ in range(r.randrange(1,7))]
        rules=[(tuple(max(0,-d)+(r.randrange(3) if i%2 else 0) for d in V),V) for V in D]
        a,b=[tuple(r.randrange(len(rules)) for _ in range(r.randrange(1,5))) for j in range(2)]
        v=tuple(r.randrange(12) for _ in range(n));k=r.randrange(8)
        A=compile_block(rules,a);B=compile_block(rules,b);C=compose(A,B);assert C is not None
        ref=compile_block(rules,a+b);assert C[:2]==ref[:2]
        assert jump(v,C,k)==jump(v,ref,k)==literal(v,rules,a+b,k)
        if not i%2:assert compile_reduced(D,a)==A
        s['comparisons']+=1;s['legal']+=jump(v,C,k) is not None;s['removed_higher_guards']+=len(ref[2])-len(C[2])
        if ref[2]:assert compose(A,B,0) is None
    print(dict(s))
if __name__=='__main__':main()
