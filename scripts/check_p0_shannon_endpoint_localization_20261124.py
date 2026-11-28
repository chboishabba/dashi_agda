from itertools import product
from math import ceil, log2
from sympy import symbols, expand

def locate(n, observe):
    assert n>=1
    l,r=0,n; calls=0
    while r-l>1:
        m=(l+r)//2; v=observe(m); calls+=1
        if v==0:l=m
        else:r=m
    return l,calls

seqs=0; maxcalls=0
for n in range(1,17):
    for middle in product((0,1),repeat=n-1):
        a=(0,)+middle+(1,)
        j,k=locate(n,a.__getitem__)
        assert a[j:j+2]==(0,1) and k<=ceil(log2(n))
        seqs+=1;maxcalls=max(maxcalls,k)
print('endpoint sequences',seqs,'maximum midpoint calls',maxcalls)

n=3
nodes=[p for k in range(n) for p in product((0,1),repeat=k)]
leaves=list(product((0,1),repeat=n)); ix={p:i for i,p in enumerate(nodes)}
li={p:i for i,p in enumerate(leaves)}
def route(P,p):
    while len(p)<n:p+=((P>>ix[p])&1,)
    return p
cases=0; audits=0; hidden=0
for P in range(1<<len(nodes)):
    routes={p:route(P,p) for p in nodes+leaves}
    for mask in range(1<<len(leaves)):
        f=lambda x:(mask>>li[x])&1
        S={p:f(x) for p,x in routes.items()}
        B={p:(1-S[p])*(S[p+(0,)]|S[p+(1,)]) for p in nodes}
        for p in nodes:
            for x in leaves:
                if x[:len(p)]!=p or not f(x) or S[p]:continue
                j,k=locate(n-len(p),lambda i:S[x[:len(p)+i]])
                q=x[:len(p)+j]; child=x[:len(q)+1]
                assert B[q]==1 and S[child]==1 and routes[q][:len(child)]!=child
                assert f(routes[child]) and k<=ceil(log2(n-len(p)))
                cases+=1
        # Audit equivalence on full tree, and exact hidden-neutral distinction.
        for p in nodes+leaves:
            inhabited=any(f(x) for x in leaves if x[:len(p)]==p)
            descendant=any(B[q] for q in nodes if q[:len(p)]==p)
            assert inhabited==bool(S[p] or descendant)
            audits+=1
            if p in B and not B[p] and not S[p] and inhabited:hidden+=1
print('witness-guided localizations',cases,'descendant audit identities',audits,'hidden neutral states',hidden)
# Always-zero audit gadget G(s,x)=s AND F(x). For any F, all-zero routing
# produces zero at root. A wrong-turn exists iff F is inhabited.
gadgets=0
for m in range(256):
    L=list(product((0,1),repeat=4)); N=[p for k in range(4) for p in product((0,1),repeat=k)]
    def g(x):return x[0] & ((m>>li[x[1:]])&1)
    def s(p):return g(p+(0,)*(4-len(p)))
    D=[p for p in N if not s(p) and (s(p+(0,)) or s(p+(1,)))]
    assert bool(D)==bool(m)
    for p in D:
        w=p+(1,)+(0,)*(3-len(p)); assert g(w)==1
    gadgets+=1
print('fixed-policy audit gadgets',gadgets)
a,b=symbols('a b'); assert expand(a+(1-a)*b-(a+b-a*b))==0
print('symbolic OR residual 1/1')
