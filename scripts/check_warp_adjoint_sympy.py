import sympy as s

def check():
    a,c,z,h,l,r,d,e=s.symbols('a c z h l r d e', real=True)
    A=s.Matrix([[0,a/2,c/2],[r,a*d-z-h,z],[r,-z+l,-c*d+z-e]])
    u,p,m=s.symbols('u p m'); U,P,M=s.symbols('U P M')
    x=s.Matrix([u,p,m]); y=s.Matrix([U,P,M])
    adj=s.Matrix([r*(P+M),a*U/2+(a*d-z-h)*P+(-z+l)*M,c*U/2+z*P+(-c*d+z-e)*M])
    assert s.expand((y.T*A*x-adj.T*x)[0])==0
    B,C,D=s.symbols('B C D',commutative=False)
    J,K,L=s.symbols('J K L',commutative=False)
    q,f,g,k=s.symbols('q f g k',commutative=False)
    R=s.Rational
    q1=B*q+J*f; q2=R(3,4)*q+R(1,4)*(C*q1+K*g)
    out=q/3+R(2,3)*(D*q2+L*k)
    assert s.expand(out-(q/3+D*q/2+D*C*B*q/6+D*C*J*f/6+D*K*g/6+R(2,3)*L*k))==0
    v,b,dt=s.symbols('v b dt', real=True, nonzero=True)
    weight=-dt/(v*b**3)
    assert s.simplify(weight.subs(v,-1/s.sqrt(1+h*h)).subs(b,1/h)-dt*h**3*s.sqrt(1+h*h))==0
    w1,w2=s.symbols('w1 w2',positive=True); k1,k2,F1,F2=s.symbols('k1 k2 F1 F2',real=True)
    W=s.diag(w1,w2); K=s.Matrix([k1,k2]); F=s.Matrix([F1,F2]); C=(K.T*W.inv()*K)[0]
    assert s.factor(C*(F.T*W*F)[0]-(K.T*F)[0]**2-(k1*w2*F2-k2*w1*F1)**2/(w1*w2))==0
    print('PASS stage transpose, noncommuting SSPRK3 source map, Israel weight, weighted compliance certificate')
if __name__=='__main__':check()
