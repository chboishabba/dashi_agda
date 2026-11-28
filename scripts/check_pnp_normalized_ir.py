"""Flat Nat ABI for original parsed candidate -> normalized compiler.
Finite Python parity, not cross-kernel proof or a universal parser.
"""
from itertools import product
from random import Random
from check_pnp_candidate_literal_endpoint import candidate_bits
from check_pnp_stack_fractran import compile_candidate_bits,compile_stack
from check_pnp_stack_priority_transport import AuditedRunner


def export(M,initial,accept):
    return (M.states,M.symbols,initial,accept,len(M.rules))+tuple(
        x for q,a,p,b,d in M.rules for x in (q,M.digit(a),p,M.digit(b),d+1))


def parse(xs):
    if len(xs)<5 or any(type(x)!=int or x<0 for x in xs):raise ValueError('nat ABI')
    Q,A,q,p,k=xs[:5]
    if min(Q,A)<1 or q>=Q or p>=Q or len(xs)!=5+5*k:raise ValueError('header')
    rows=tuple(tuple(xs[i:i+5]) for i in range(5,len(xs),5))
    if any(a>=Q or b>=A or c>=Q or d>=A or e>=3 for a,b,c,d,e in rows):raise ValueError('rule')
    return Q,A,q,p,rows


def main():
    rng=Random(369);cases=steps=0
    for Q,A in product(range(1,4),repeat=2):
        for blank in range(A):
            for _ in range(4):
                rules=tuple((rng.randrange(Q),rng.randrange(A),rng.randrange(Q),rng.randrange(A),rng.randrange(-1,2)) for _ in range(4))
                rules=(rules[0],(rules[0][0],rules[0][1],0,blank,-rules[0][4]))+rules[1:]
                M,q,p=compile_candidate_bits(Q,A,len(rules),candidate_bits(Q,A,blank,0,Q-1,rules))
                wire=export(M,q,p);Q1,A1,q1,p1,rows=parse(wire)
                assert (Q1,A1,q1,p1)==(Q,A,q,p)
                N=compile_stack(Q,A,0,tuple((a,b,c,d,e-1) for a,b,c,d,e in rows))
                assert export(N,q,p)==wire and N.base==M.base
                R,S=AuditedRunner(M),AuditedRunner(N)
                for s,L,V in product(range(Q),((),(blank,),(0,blank)),((blank,),(0,),(blank,0))):
                    x=M.encode(s,L,V);y=N.encode(s,tuple(map(M.digit,L)),tuple(map(M.digit,V)))
                    u,h,c=R.exact(x,True);v,j,d=S.exact(y,True)
                    assert (u[:5],h,c['raw'])==(v[:5],j,d['raw'])
                    a,b,e,g=M.decode(u)
                    assert N.decode(v)==(a,tuple(map(M.digit,b)),tuple(map(M.digit,e)),g)
                    steps+=1
                cases+=1
    for bad in ((1,1,0,0,1),(1,1,0,0,0,0),(1,1,0,0,1,0,1,0,0,1)):
        try:parse(bad);raise AssertionError('malformed accepted')
        except ValueError:pass
    print(dict(ir_tables=cases,emitted_endpoints=steps,malformed=3))
if __name__=='__main__':main()
