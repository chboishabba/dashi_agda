"""Independent exact P0AH same-source Israel checks; not a bulk solve."""
import sympy as s

def audit():
    I=s.eye(4); h=s.diag(-1,1,1,1); k=s.symbols('k',positive=True)
    def tensor(prefix):
        a=s.zeros(4)
        for i in range(4):
            for j in range(i,4): a[i,j]=a[j,i]=s.Symbol(f'{prefix}{i}{j}',real=True)
        return h*a
    S,M=tensor('S'),tensor('M'); J=-k*(S-s.trace(S)*I/3)
    f=lambda A:s.trace(A)**2-s.trace(A*A)
    assert (-(J-s.trace(J)*I)-k*S).applyfunc(s.expand)==s.zeros(4)
    assert s.expand(f(M+J/2)-f(M-J/2)-2*k*s.trace(M*S))==0
    assert s.expand((f(M+J/2)+f(M-J/2))/2-f(M)-k*k*(s.trace(S)**2/3-s.trace(S*S))/4)==0
    # KSW668 original rational slice t=4/3 (master 7b77912).
    S0=s.diag(-s.Rational(5,4),*([-s.Rational(11,10)]*3))
    K0=s.diag(-s.Rational(4,5),*([-s.Rational(5,4)]*3))
    assert -3*(S0-s.trace(S0)*I/3)==K0
    assert -12+f(K0)==s.Rational(27,8)
    E=s.Matrix(s.symbols('E:3',real=True)); B=s.Matrix(s.symbols('B:3',real=True))
    u=(E.dot(E)+B.dot(B))/2; P=E.cross(B)
    EM=h*(s.Matrix([[u]]).row_join(-P.T)).col_join((-P).row_join(u*I[:3,:3]-E*E.T-B*B.T))
    invariant=(E.dot(E)-B.dot(B))**2+4*E.dot(B)**2
    assert s.expand(s.trace(EM))==0
    assert s.expand(s.trace(EM*EM)-invariant)==0
    T=s.symbols('T',positive=True)
    assert s.expand(k*k*(s.trace(-T*I+EM)**2/3-s.trace((-T*I+EM)**2))/4-k*k*T*T/3+k*k*invariant/4)==0
    null=EM.subs(dict(zip(list(E)+list(B),[1,0,0,0,1,0])))
    assert null!=s.zeros(4) and s.trace(null*null)==0 and -k*null!=s.zeros(4)
    t,t0,V,n,c,mu=s.symbols('t t0 V n c mu',positive=True)
    F=mu*n+t*n*(s.log(n/V)-1); F2=F+(t-t0)*c*n
    assert s.simplify((F2-F).subs(t,t0))==0
    assert s.simplify(s.diff(F2-F,V))==0
    assert s.simplify(((F2-t*s.diff(F2,t))-(F-t*s.diff(F,t))).subs(t,t0))==-c*n*t0
    assert -s.diff(F,V)==t*n/V
    q,A,C=s.symbols('q A C',positive=True)
    H=q*q/(2*C*A); assert -s.diff(H,A)==H/A
    print('PASS: generic jump and both normal constraints; KSW668 rational slice; EM invariant and null control; thermodynamic nonidentifiability and surface pressure')

if __name__=='__main__': audit()
