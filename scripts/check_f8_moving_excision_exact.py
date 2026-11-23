"""Exact finite symbolic controls; not native-order or continuum acceptance."""
import sympy as s


def check():
    I=s.eye(3)
    L=s.Matrix(3,3,s.symbols('l:9'))
    x=s.Matrix(s.symbols('x:3'))
    r=s.Matrix(s.symbols('r:3'))
    p=s.Matrix(s.symbols('p:3'))
    Q=s.diag(1,1,0)
    T=s.diag(0,1,1)
    K=T*L-L*Q
    zero=lambda a: all(s.expand(v)==0 for v in a)
    assert zero(K-(Q*L-L*Q)-(T-Q)*L)
    assert zero(T*(L*x+r)-L*Q*x-T*r-K*x)
    assert zero((I-T)*(L*x+r)-L*(I-Q)*x-(I-T)*r+K*x)
    assert zero(K-(T*L*(I-Q)-(I-T)*L*Q))
    # Keep the two directed interface contributions separately.
    incoming=(p.T*T*L*(I-Q)*x)[0]
    outgoing=(p.T*(I-T)*L*Q*x)[0]
    assert s.expand((p.T*K*x)[0]-incoming+outgoing)==0
    q=s.Matrix(s.symbols('q:3'))
    pn=q+L.T*p
    assert s.expand((q.T*Q*x+p.T*T*(L*x+r)-pn.T*Q*x-p.T*T*r-p.T*K*x)[0])==0
    assert s.expand((q.T*(I-Q)*x+p.T*(I-T)*(L*x+r)-pn.T*(I-Q)*x-p.T*(I-T)*r+p.T*K*x)[0])==0
    # Moving support alone can cause nonzero attribution even for identity transport.
    assert K.subs(dict(zip(L,I))) != s.zeros(3)
    print('8/8 exact moving excision controls PASS; SymPy',s.__version__)


if __name__=='__main__':
    check()
