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
        for k in (1,2,10):
            bot=s.zeros(9,5).row_join(Rwall*N).row_join(k*(t*s.eye(9)-s.I*d*B)*d**3)
            M=top.col_join(bot).applyfunc(s.expand)
            for name,T in [('jump',top),('joint',M)]:
                cs=[T.applyfunc(lambda z:s.expand(z).coeff(u,i)) for i in range(5)]
                vals=[]; diffs=[]
                for m in range(1,6):
                    Z=s.zeros(T.rows,19)
                    A=s.BlockMatrix([[cs[i-j] if i>=j else Z for j in range(m)] for i in range(m)]).as_explicit()
                    rank=DomainMatrix.from_Matrix(A).convert_to(s.QQ_I).rank(); nu=19*m-rank
                    diffs.append(nu-(vals[-1] if vals else 0)); vals.append(nu)
                    if diffs[-1]==0:break
                print(sig,k,name,'nullities',vals,'increments',diffs,flush=True)
                assert diffs[-1]==0
                assert all(a>=b for a,b in zip(diffs,diffs[1:]))
                assert vals==([6,7,7] if name=='jump' else [4,4])
                print('orders',{i:diffs[i-1]-diffs[i] for i in range(1,len(diffs))},flush=True)

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,P,Q
    _,V,X,G,Y,H,J,A,B,R,_,_=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])*V)[0]
    run(X,G,J,F,B[0],R)
