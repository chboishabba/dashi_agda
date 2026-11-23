"""Exact SSPRK3 moving-support ledger; no native PDE claim."""
import sympy as s

R=s.Rational
I=s.eye(2)
A=s.Matrix([[2,1],[3,1]])
B=s.Matrix([[1,4],[2,3]])
C=s.Matrix([[3,2],[1,1]])
def vec(name):
    return s.Matrix(s.symbols(name+'0:2'))
x,a,b,c,p=map(vec,('x','a','b','c','p'))
Q0=s.diag(1,0); QA=s.diag(0,1); QB=I; Q1=s.diag(1,0)

def check(A,B,C,Q0,QA,QB,Q1):
    u=A*x+a
    v=R(3,4)*x+(B*u+b)/4
    y=x/3+R(2,3)*(C*v+c)
    def ledger(Q0,QA,QB,Q1):
        z=A*Q0*x+QA*a
        w=R(3,4)*Q0*x+(B*z+QB*b)/4
        base=Q0*x/3+R(2,3)*(C*w+Q1*c)
        KA=QA*A-A*Q0; KB=QB*B-B*QA; KC=Q1*C-C*QB
        terms=[C*B*KA*x/6,C*KB*u/6,R(2,3)*KC*v,C*(QB-Q0)*x/2,(Q1-Q0)*x/3]
        defect=sum(terms,s.zeros(2,1))
        assert (Q1*y-base-defect).applyfunc(s.expand)==s.zeros(2,1)
        assert s.expand((p.T*(Q1*y-base))[0]-sum((p.T*t)[0] for t in terms))==0
        return base,terms
    base,terms=ledger(Q0,QA,QB,Q1)
    comp,other=ledger(I-Q0,I-QA,I-QB,I-Q1)
    assert (base+comp-y).applyfunc(s.expand)==s.zeros(2,1)
    assert all((t+o).applyfunc(s.expand)==s.zeros(2,1) for t,o in zip(terms,other))
    return terms

if __name__=='__main__':
    check(A,B,C,Q0,QA,QB,Q1)
    check(A,B,C,Q0,Q0,Q0,Q0)
    terms=check(I,I,I,Q0,QA,QB,Q1)
    assert any(t!=s.zeros(2,1) for t in terms[3:])
    assert sum(terms,s.zeros(2,1)).applyfunc(s.expand)!=s.zeros(2,1)
    print('PASS moving, stationary, identity-transport fixtures; five-term vector and dual closure, complementary base and termwise cancellation; carry negative control')
