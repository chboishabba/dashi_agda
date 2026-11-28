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
        E=s.Matrix.hstack(*(B-sig*s.eye(9)).nullspace())
        assert E.cols==1
        P0=s.eye(9)
        for lam in (0,s.Rational(1,2),-s.Rational(1,2),-sig):
            P0=P0*(B-lam*s.eye(9))/(sig-lam)
        assert P0*P0==P0 and P0*B==sig*P0
        Q0=s.eye(9)-P0
        a=s.symbols('a', nonzero=True)
        # h=u²/a. Normalize nonresonant rows only; resonant forcing retained.
        bot=s.zeros(9,5).row_join((P0+u*u/a*Q0)*Rwall*N).row_join((-2*sig*s.I*a*P0+Q0*(t*s.eye(9)-s.I*d*B))*d**3)
        M=top.col_join(bot).applyfunc(s.expand)
        T0=M.subs(u,0); T1=M.diff(u).subs(u,0)
        for av in (s.I/2,-s.I/2,s.I,-s.I,1):
            C0=T0.subs(a,av); C1=T1.subs(a,av)
            K=s.Matrix.hstack(*C0.nullspace())
            rank=DomainMatrix.from_Matrix(C0.row_join(C1*K)).convert_to(s.QQ_I).rank()
            print(sig,av,'rank0',19-K.cols,'rank lift',rank,'remaining',K.cols-(rank-(19-K.cols)),flush=True)
            assert K.cols==5 and rank==19
        rank0=DomainMatrix.from_Matrix(T0).to_field().rank()
        D=T0.row_join(s.zeros(44,19)).col_join(T1.row_join(T0))
        rank1=DomainMatrix.from_Matrix(D).to_field().rank()
        assert (rank0,rank1)==(14,33)
        for M0,expected in ((T0,214990848*s.I*a/390625),(D,sig*47330370277129322496*s.I*a**2/152587890625)):
            ids=list(M0.subs(a,1).T.rref()[1]); cols=list(M0.subs(a,1).rref()[1])
            det=s.factor(M0.extract(ids,cols).det(method='domain-ge'))
            print('minor',len(ids),det,flush=True)
            assert s.cancel(det-expected)==0
    print('PASS BR216 selective wall weighting and symbolic first-order filtration')

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,P,Q
    _,V,X,G,Y,H,J,A,B,R,_,_=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])*V)[0]
    run(X,G,J,F,B[0],R)
