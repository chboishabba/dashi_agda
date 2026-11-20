"""Exact finite nonlinear seam and receiver duality; no PDE promotion."""
import sympy as s

def check():
    # Arbitrary quadratic maps, rectangular transfer, moving time fibres.
    x=s.Matrix(s.symbols('x:2')); e=s.Matrix(s.symbols('e:3'))
    I=s.Matrix([[1,0],[1,2],[0,1]]); J=s.Matrix([[2,1],[1,0],[0,2]])
    A=s.Matrix([[1,2],[-1,3]]); B=s.Matrix([[1,2,0],[0,1,3],[2,0,1]])
    Q=lambda a,b:s.Matrix([a[0]*b[1],a[1]*b[0]])
    R=lambda a,b:s.Matrix([a[1]*b[2],a[2]*b[0],a[0]*b[1]])
    g=s.Matrix([2,-1]); f=s.Matrix([1,0,3])
    Fc=lambda a:A*a+Q(a,a)+g
    Ff=lambda a:B*a+R(a,a)+f
    y=I*x; z=y-e
    seam=J*Fc(x)-Ff(y)
    split=(J*A-B*I)*x+J*Q(x,x)-R(y,y)+J*g-f
    assert s.expand(seam-split)==s.zeros(3,1)
    # Exact secant, not a frozen tangent for nonlinear error propagation.
    L=B+s.Matrix.hstack(*[R(y,v)+R(v,z) for v in s.eye(3).columnspace()])
    assert s.expand(Ff(y)-Ff(z)-L*e)==s.zeros(3,1)
    assert s.expand(J*Fc(x)-Ff(z)-L*e-seam)==s.zeros(3,1)
    # Weighted dual transport between genuinely different time metrics.
    W=s.diag(2,3,5); V=s.diag(7,11,13); lam=s.Matrix(s.symbols('l:3'))
    adj=W.inv()*L.T*V*lam
    assert s.expand((lam.T*V*L*e-adj.T*W*e)[0])==0
    assert s.expand((lam.T*V*(L*e+seam)-adj.T*W*e-lam.T*V*seam)[0])==0
    # Orientation reversal: same codomain, exchange paths, not inverse time.
    assert s.expand(Ff(y)-J*Fc(x)+seam)==s.zeros(3,1)
    # R156 finite Gram identity: signed pairing squared plus wedge squares.
    a=s.Matrix(s.symbols('a:3')); b=s.Matrix(s.symbols('b:3'))
    assert s.expand(a.dot(a)*b.dot(b)-a.dot(b)**2-sum((a[i]*b[j]-a[j]*b[i])**2 for i in range(3) for j in range(i+1,3)))==0
    # Nonlinear sign quotient is not additive, even in one coordinate.
    assert s.sign(2)+s.sign(-1)!=s.sign(2-1)
    print('8/8 exact finite seam, secant, weighted dual, orientation and Gram checks PASS')
if __name__=='__main__':check()
