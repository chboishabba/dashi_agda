"""BR300 literal original BR229 Coulomb and one-body carrier attachment.
Run the original integrals and original symmetry tests before comparison.
"""
import inspect
import sympy as s
import check_hopf369_br225_229_endpoint_welds as original
import check_hopf369_br275_atomic_marked as inverse

def capture(fn,tail):
    source=inspect.getsource(fn)
    ns=dict(fn.__globals__)
    exec(source+'\n    '+tail+'\n',ns)
    return ns[fn.__name__]()

def run():
    H,V,W,H2,modes,pairs=capture(original.atomic,'return H,V,W,H2,modes,pairs')
    D,P,V2=capture(inverse.run,'return D,P,V')
    assert modes==inverse.modes and pairs==inverse.pairs
    assert (W*V*W.H-V2).applyfunc(s.simplify)==s.zeros(28)
    a,c,es,ep,ls,scale=P
    assert (s.Matrix(list(H2))-D*s.Matrix([a,c,es,ep,ls,1])).applyfunc(s.simplify)==s.zeros(784,1)
    G=D.H*D
    assert s.simplify(G.det())!=0
    print('BR300 literal BR229 original matrix equals BR275 design at unit Coulomb scale; signed inverse attachment PASS',flush=True)
if __name__=='__main__':run()
