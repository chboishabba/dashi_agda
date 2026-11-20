"""CMP109 section 2 linear delta elimination: exact determinant and mixed jets.
Applies to ordinary Lebesgue delta(Qx); not a proof that all physical source
normalizations/pivots have been identified. Credit Balaban CMP109 (1987).
"""
import sympy as S
s,t=S.symbols('s t', real=True)
P=S.Matrix([[2+s+t,1+s*t],[s-t,1+2*t]])
R=S.Matrix([[1+t,2+s],[s*t,1-s]])
A=S.Matrix([[6+s,1+t,s*t,2],[1+t,5+s*t,1,s],[s*t,1,4+t,1+t],[2,s,1+t,7+s]])
T=S.Matrix([[1+s+t,t],[0,1+s*t]])
base={s:0,t:0}
def jet(B):return tuple(e.subs(base) for e in (B,B.diff(s),B.diff(t),B.diff(s,t)))
def mul(B,C):
    b,bs,bt,bst=B;c,cs,ct,cst=C
    return (b*c,bs*c+b*cs,bt*c+b*ct,bst*c+bs*ct+bt*cs+b*cst)
def inv(B):
    b,bs,bt,bst=B;g=b.inv()
    return (g,-g*bs*g,-g*bt*g,g*bt*g*bs*g+g*bs*g*bt*g-g*bst*g)
def adj(B):return tuple(b.T for b in B)
def neg(B):return tuple(-b for b in B)
def const(B):return (B,)+(S.zeros(*B.shape),)*3
def vcat(B,C):return tuple(b.col_join(c) for b,c in zip(B,C))
def hcat(B,C):return tuple(b.row_join(c) for b,c in zip(B,C))
def trjet(B):
    b,bs,bt,bst=B;g=b.inv()
    return S.trace(g*bst-g*bt*g*bs)
def verify(base):
    p,r,a,Tj=map(jet,(P,R,A,T));q=hcat(p,r)
    c=vcat(neg(mul(inv(p),r)),const(S.eye(2)))
    h=mul(mul(adj(c),a),c)
    k=vcat(hcat(a,adj(q)),hcat(q,const(S.zeros(2))))
    m=mul(q,adj(q));gram=mul(adj(c),c)
    assert all(x==S.zeros(2) for x in mul(q,c))
    assert k[0].det()==p[0].det()**2*h[0].det()
    assert m[0].det()==p[0].det()**2*gram[0].det()
    assert trjet(k)==2*trjet(p)+trjet(h)
    assert trjet(k)-trjet(m)==trjet(h)-trjet(gram)
    assert trjet(m)==2*trjet(p)+trjet(gram)
    assert trjet(mul(mul(adj(Tj),h),Tj))-2*trjet(Tj)==trjet(h)
    assert trjet(p)!=0
    return trjet(k),trjet(k)-trjet(m),2*trjet(p)
if __name__=='__main__':
    for u,v in [(0,0),(S.Rational(1,5),S.Rational(1,7)),(-S.Rational(1,9),S.Rational(1,11))]:
        base={s:u,t:v}; result=verify(base)
        print('PASS',base,'2 Gamma_st delta, induced, pivot correction:',result)
