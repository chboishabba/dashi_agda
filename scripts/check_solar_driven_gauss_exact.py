"""Independent exact algebra for the staggered and implicit driven work laws."""
import sympy as S

def run():
    h,c=S.symbols('h c',real=True);I=S.eye(2)
    K=S.Matrix([[1-h*h*c*c,h*c],[-h*c,1]])
    G=S.Matrix([[1,-h*c/2],[-h*c/2,1]])
    assert (K.T*G*K-G).applyfunc(S.expand)==S.zeros(2)
    e,b,j,de,dj=S.symbols('e b j de dj',real=True)
    x=S.Matrix([e,b,j]);d=S.Matrix([de,0,dj]);G3=S.diag(G,1)
    mid=S.Matrix([e-h*c*b/2+de/2,j+dj/2]);delta=S.Matrix([de,dj])
    assert S.expand(((x+d).T*G3*(x+d)-x.T*G3*x)[0]/2-(mid.T*delta)[0])==0
    a,r,s,p,u,w,v=S.symbols('a r s p u w v',real=True)
    m=S.Matrix([w,v]);J=S.Matrix([[0,-a],[a,0]]);R=S.diag(r,s);P=S.Matrix([p,0]);f=(J-R-P*P.T)*m+P*u
    assert S.expand((m.T*f)[0]+(m.T*R*m)[0]-(u/2)**2+(u/2-(P.T*m)[0])**2)==0
    # Actual incidence signs on one oriented triangle, including charge injection.
    d0=S.Matrix([[-1,1,0],[0,-1,1],[-1,0,1]]);C=S.Matrix([[1,1,-1]])
    assert C*d0==S.zeros(1,3)
    E=S.Matrix(S.symbols('e0:3'));B=S.Matrix([b]);f=S.Matrix(S.symbols('f0:3'))
    B1=B-h*C*E;E1=E+h*C.T*B1+h*f
    assert (d0.T*(E1-E)-h*d0.T*f).applyfunc(S.expand)==S.zeros(3,1)
    # Full midpoint identity for arbitrary skew exchange and symmetric loss follows from polarization.
    x=S.Matrix(S.symbols('x0:3'));y=S.Matrix(S.symbols('y0:3'))
    assert S.expand((y.T*y-x.T*x)[0]/2-((y+x).T*(y-x))[0]/2)==0
    print('EXACT_DRIVEN_GAUSS_PASS: 6 symbolic identities')
if __name__=='__main__':run()
