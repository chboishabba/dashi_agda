from itertools import product
from sympy import symbols, Poly, QQ, divisor_sigma, Matrix, eye
from time import perf_counter

def main():
    start=perf_counter()
    q=symbols('q'); N=12
    E4=Poly(1+sum(240*divisor_sigma(n,3)*q**n for n in range(1,N+2)),q,domain=QQ)
    E6=Poly(1-sum(504*divisor_sigma(n,5)*q**n for n in range(1,N+2)),q,domain=QQ)
    numerator=E4**3; delta=(numerator-E6**2).mul_ground(QQ(1,1728))
    eta=Poly(1,q,domain=QQ)
    for n in range(1,N+1):
        z=eta*Poly((1-q**n)**24,q,domain=QQ)
        eta=Poly.from_dict({m:c for m,c in z.terms() if m[0]<=N},q,domain=QQ)
    assert all(delta.nth(n)==eta.nth(n-1) for n in range(1,N+2))
    j=[]
    for n in range(N+1):
        j.append(numerator.nth(n)-sum(delta.nth(k+1)*j[n-k] for k in range(1,n+1)))
    assert j[:5]==[1,744,196884,21493760,864299970]
    # Original NineSheet global inversion; fixed point and four pairs.
    X=list(product((-1,0,1),repeat=2))
    neg=lambda x:tuple(-v for v in x)
    orb=lambda x:min(x,neg(x))
    O=sorted(set(map(orb,X)))
    assert sorted(sum(orb(x)==o for x in X) for o in O)==[1,2,2,2,2]
    P=Matrix(9,9,lambda i,k:int(X[i]==neg(X[k])))
    A=(eye(9)+P)/2; B=(eye(9)-P)/2
    assert A*A==A and B*B==B and A*B==Matrix.zeros(9) and A+B==eye(9)
    assert A.rank()==5 and B.rank()==4
    # D4 quarter turn and reflection commute with inversion.
    for f in (lambda x:(-x[1],x[0]),lambda x:(x[0],-x[1])):
        T=Matrix(9,9,lambda i,k:int(X[i]==f(X[k])))
        assert T*A==A*T and T*B==B*T
    # Exact count-level weld, NOT an actual Monster representation identification.
    F=3**9; H=3**6; C=6*9
    assert F==27*H and C==54
    assert j[2]==2*len(O)*F+C==C*(1+len(O)*H)
    # C3 regular trace cancels; 54 trivial dimensions give trace 54.
    assert (j[2]-C)%3==0
    multiplicity=(j[2]-C)//3
    assert multiplicity==65610
    print('PASS: 13 Delta coefficients; j prefix', j[:5])
    print('PASS: five orbit sizes, complementary projectors ranks 5/4, D4 commutation')
    print('PASS: 54*(1+5*729)=196884; regular C3 multiplicity',multiplicity)
    print('wall_seconds',perf_counter()-start)
if __name__=='__main__': main()
