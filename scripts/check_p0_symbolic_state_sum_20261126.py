"""Parsimonious graph state-sum CNF bridge and Boolean-ideal firewall.
Local checks only; no external lower-bound proof execution.
"""
from itertools import product
from random import Random
from collections import Counter
import sympy as sp

class CNF:
    def __init__(self,n): self.n=n; self.clauses=[]; self.gates=[]
    def gate(self,op,*ins):
        self.n+=1; j=self.n; self.gates.append((op,ins))
        if op=='and':
            a,b=ins; self.clauses.extend([(-j,a),(-j,b),(j,-a,-b)])
        elif op=='or':
            a,b=ins; self.clauses.extend([(j,-a),(j,-b),(-j,a,b)])
        elif op=='true': self.clauses.append((j,))
        else: raise ValueError(op)
        return j
    def fold(self,ls):
        ls=list(ls)
        if not ls:return self.gate('true')
        a=ls[0]
        for b in ls[1:]: a=self.gate('and',a,b)
        return a
    def extend(self,bits):
        out=list(bits)
        def val(l):return out[abs(l)-1]^int(l<0)
        for op,ins in self.gates:
            out.append(1 if op=='true' else (val(ins[0])&val(ins[1]) if op=='and' else val(ins[0])|val(ins[1])))
        return tuple(out)
    def accepts(self,x):return len(x)==self.n and all(any(x[abs(l)-1]==int(l>0) for l in c) for c in self.clauses)

def compile_graph(v,edges,q):
    # Distinct edge identities, including parallel edges; no loops.
    b=(q-1).bit_length(); assert q>=2
    C=CNF(b*len(edges)); marks={}; incidence=[[] for _ in range(v)]
    def code(e,a):return [(e*b+i+1)*(1 if a>>i&1 else -1) for i in range(b)]
    for e,(i,j) in enumerate(edges):
        assert i!=j;incidence[i].append(e);incidence[j].append(e)
        for a in range(q,1<<b):C.clauses.append((-C.fold(code(e,a)),))
    for i,es in enumerate(incidence):
        for labels in product(range(q),repeat=len(es)):
            # Fresh output even for unary selector, so weights have independent indices.
            a=C.fold(l for e,t in zip(es,labels) for l in code(e,t))
            j=C.gate('and',a,a);marks[i,labels]=j
    return C,marks,incidence,b

def main():
    rng=Random(90); counts=Counter()
    graphs=[(1,[]),(2,[(0,1)]),(2,[(0,1),(0,1)]),(3,[(0,1),(1,2)]),(3,[(0,1),(1,2),(2,0)]),(4,[(0,1),(1,3),(3,2),(2,0)])]
    for v,edges in graphs:
        for q in (2,3):
            C,M,I,b=compile_graph(v,edges,q);n=b*len(edges)
            assert all(len(c)<=3 for c in C.clauses)
            monomials=Counter(); direct=Counter()
            for a in product(range(q),repeat=len(edges)):
                direct[tuple((i,tuple(a[e] for e in es)) for i,es in enumerate(I))]+=1
            for x in product((0,1),repeat=n):
                z=C.extend(x); a=tuple(sum(x[e*b+i]<<i for i in range(b)) for e in range(len(edges)))
                assert C.accepts(z)==all(t<q for t in a)
                counts['source_lifts']+=1
                if C.accepts(z):
                    selected=tuple(k for k,j in M.items() if z[j-1]);assert len(selected)==v
                    monomials[selected]+=1
            assert direct==monomials;counts['graph_polynomials']+=1
            for p in (2,3,5,7):
                for _ in range(10):
                    weights={k:rng.randrange(p) for k in M}
                    def val(terms):return sum(c*sp.prod(weights[k] for k in keys) for keys,c in terms.items())%p
                    assert val(direct)==val(monomials);counts['field_evaluations']+=1
            if C.n<=16:
                assert sum(C.accepts(x) for x in product((0,1),repeat=C.n))==q**len(edges);counts['full_cnf_enumerations']+=1
    # Boolean-equivalent representatives can differ on the exact slot component.
    x,y,z=sp.symbols('x y z');f=x*y*z;g=f+(x*x-x)*y*z
    assert all(f.subs(dict(zip((x,y,z),a)))==g.subs(dict(zip((x,y,z),a))) for a in product((0,1),repeat=3))
    assert sp.Poly(f,x,y,z).coeff_monomial(x*y*z)==1
    assert sp.Poly(g,x,y,z).coeff_monomial(x*y*z)==0
    # Full symbolic polynomial is multi-affine; Boolean evaluations determine it,
    # but a general Boolean-equivalent representative is not the polynomial itself.
    for n in range(1,9):
        a=[rng.randrange(2) for _ in range(1<<n)];b=a.copy()
        for i in range(n):
            for j in range(1<<n):
                if j>>i&1:b[j]^=b[j^(1<<i)]
        for i in range(n):
            for j in range(1<<n):
                if j>>i&1:b[j]^=b[j^(1<<i)]
        assert a==b;counts['mobius_roundtrips']+=1
    print(dict(counts))
if __name__=='__main__':main()
