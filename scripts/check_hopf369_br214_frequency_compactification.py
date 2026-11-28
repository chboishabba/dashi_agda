import sympy as s
from itertools import combinations
from sympy.polys.matrices import DomainMatrix

def run(X,G,J,F,B,Rwall):
    P=list(combinations(range(5),2)); left=G.inv()*X.T
    u=s.symbols('u',real=True); d=1+u*u
    for sig in (-1,1):
        t=sig*s.I*(1-u*u); l=2*u
        xi=s.Matrix([t,s.I*d,0,0,-l]); vs=[s.Matrix([l,0,0,0,-t]),d*s.eye(5)[:,2],d*s.eye(5)[:,3]]
        U=s.Matrix.hstack(*(s.Matrix([xi[a]*v[b]-xi[b]*v[a] for a,b in P]) for v in vs))
        pol=[s.diag(1,1,0),s.diag(1,0,1)]+[s.eye(3)[:,i]*s.eye(3)[:,j].T+s.eye(3)[:,j]*s.eye(3)[:,i].T for i,j in combinations(range(3),2)]
        N=(left*s.Matrix.hstack(*(s.Matrix(list(U*p*U.T)) for p in pol))).applyfunc(s.expand)
        I=s.eye(35); top=((I-F)*N).row_join((I+F)*N).row_join(s.Rational(6,5)*J*d**4)
        h=s.symbols('h',real=True)
        bot=s.zeros(9,5).row_join(h*Rwall*N).row_join((t*s.eye(9)-s.I*d*B)*d**3)
        M=top.col_join(bot).applyfunc(s.expand)
        T0=M.subs(u,0); T1=M.diff(u).subs(u,0)
        rank0=DomainMatrix.from_Matrix(T0).to_field().rank()
        assert rank0==15
        ids=list(T0.subs(h,1).T.rref()[1]); cols=list(T0.subs(h,1).rref()[1])
        det0=s.factor(T0.extract(ids,cols).det(method='domain-ge'))
        assert det0==-s.Rational(26873856,390625)*h**2
        A=T0.row_join(s.zeros(44,19)).col_join(T1.row_join(T0))
        rank1=DomainMatrix.from_Matrix(A).to_field().rank()
        assert rank1==34
        ids=list(A.subs(h,1).T.rref()[1]); cols=list(A.subs(h,1).rref()[1])
        det1=s.factor(A.extract(ids,cols).det(method='domain-ge'))
        assert det1==sig*s.Rational(277326388342554624,762939453125)*h**5
        print(sig,'generic ranks',rank0,rank1,'minors',det0,det1,flush=True)
        for v in (0,s.Rational(1,10),s.Rational(1,2),1):
            T=M.subs(h,v); cs=[T.applyfunc(lambda z:s.expand(z).coeff(u,i)) for i in range(3)]
            vals=[]
            for m in range(1,4):
                Z=s.zeros(44,19)
                D=s.BlockMatrix([[cs[i-j] if i>=j else Z for j in range(m)] for i in range(m)]).as_explicit()
                vals.append(19*m-DomainMatrix.from_Matrix(D).convert_to(s.QQ_I).rank())
            assert vals==([6,7,7] if v==0 else [4,4,4])
            print(sig,v,'joint nullities',vals,flush=True)
    print('PASS BR214 high-frequency compactification; not uniform first-order inverse')

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,P,Q
    _,V,X,G,Y,H,J,A,B,R,_,_=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])*V)[0]
    run(X,G,J,F,B[0],R)
