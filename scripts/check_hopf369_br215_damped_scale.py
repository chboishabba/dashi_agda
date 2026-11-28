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
        T0=M.subs({u:0,h:0}); T1=M.diff(u).subs({u:0,h:0})
        K=s.Matrix.hstack(*T0.nullspace()); assert K.cols==6
        Z=s.Matrix.hstack(*(T0.row_join(T1*K)).nullspace())
        v=K*Z[19:,:]; ids=v.rref()[1]; assert len(ids)==1
        v=v[:,ids[0]]; w=T0.gauss_jordan_solve(-T1*v)[0]; w=w.subs(dict.fromkeys(w.free_symbols,0))
        assert v!=s.zeros(19,1) and T0*v==s.zeros(44,1) and T0*w+T1*v==s.zeros(44,1)
        c=s.symbols('c'); out=(M.subs(h,c*u*u)*(v+u*w)).applyfunc(s.expand)
        assert out.subs(u,0)==s.zeros(44,1) and out.diff(u).subs(u,0)==s.zeros(44,1)
        print(sig,'nonzero amplitude',list(v),'order2 source rank',out.diff(u,2).subs(u,0).jacobian([c]).rank(),flush=True)
        print("v1",list(w),"quadratic residual",[(i,x) for i,x in enumerate(out.diff(u,2).subs(u,0)/2) if x],flush=True)
        print("wall residual quadratic",list(out[35:,:].diff(u,2).subs(u,0)/2),flush=True)
        assert out.diff(u,2).subs(u,0).diff(c)==s.zeros(44,1)
        assert out.diff(u,2).subs(u,0)!=s.zeros(44,1)
        print('PASS damped-scale polynomial witness',flush=True)

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,P,Q
    _,V,X,G,Y,H,J,A,B,R,_,_=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])*V)[0]
    run(X,G,J,F,B[0],R)
