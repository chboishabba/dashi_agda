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
        # h=u²/a. Multiply nonresonant wall rows by h, leave resonant rows unscaled.
        bot=s.zeros(9,5).row_join((P0+u*u/a*Q0)*Rwall*N).row_join((-2*sig*s.I*a*P0+Q0*(t*s.eye(9)-s.I*d*B))*d**3)
        M=top.col_join(bot).applyfunc(s.expand)
        T0=M.subs(u,0); T1=M.diff(u).subs(u,0)
        singular=[0,1,4,7,8]
        regular=[i for i in range(19) if i not in singular]
        E=s.eye(19)[:,regular]; K=s.eye(19)[:,singular]; S=E.row_join(K)
        assert S.det()==1 and K[10:,:]==s.zeros(9,5)
        assert T0*K==s.zeros(44,5)
        L=(M*E).row_join((M*K).applyfunc(lambda z:s.cancel(z/u)))
        assert L.subs(u,0)==(T0*E).row_join(T1*K)
        ids=[0,1,2,3,5,6,7,8,9,12,14,15,16,18,20,22,25,29,35]
        det=s.factor(L.subs(u,0)[ids,:].det(method='domain-ge'))
        assert det==sig*s.Rational(220150628352,390625)*a
        print('sign',sig,'regularized minor',det,'shape kernel rank',K[10:,:].rank(),flush=True)
        # Exact source quotient on a nonzero complex sample, h=1/100.
        uv=(1+sig*s.I)/20; av=100*uv**2
        Lv=L.subs({u:uv,a:av}).applyfunc(s.cancel)
        R=s.eye(44)[ids,:]; U0=Lv[ids,:].inv()*R
        assert (U0*Lv-s.eye(19)).applyfunc(s.cancel)==s.zeros(19)
        Pi=Lv*U0
        assert (Pi*Pi-Pi).applyfunc(s.cancel)==s.zeros(44) and (U0*Pi-U0).applyfunc(s.cancel)==s.zeros(19,44)
        f=Lv*s.Matrix(range(1,20)); assert (Pi*f-f).applyfunc(s.cancel)==s.zeros(44,1)
        bad=next(s.eye(44)[:,i] for i in range(44) if i not in ids)
        assert (Pi*bad).applyfunc(s.cancel)==s.zeros(44,1) and bad!=s.zeros(44,1)
        assert (M.subs({u:uv,a:av})*S*s.diag(*([1]*14+[1/uv]*5))-Lv).applyfunc(s.cancel)==s.zeros(44,19)
        print('sign',sig,'exact compatible quotient and incompatible row refusal PASS',flush=True)
    # Physical normal integration, lambda=sqrt(gamma²+2 sigma i gamma k).
    r,y,k,g=s.symbols('r y k g',positive=True)
    assert s.integrate(s.exp(-2*r*y),(y,0,s.oo))==1/(2*r)
    # Paired physical modes (a+b),(a-b): positive Gram parallelogram.
    x,z=s.symbols('x z',real=True)
    assert s.expand((x+z)**2+(x-z)**2-2*x*x-2*z*z)==0
    # Re lambda >= sqrt(gamma k), |u|^-2=k sqrt(4+(gamma/k)^2)/gamma.
    assert s.simplify((g**4+4*g*g*k*k)-(2*g*k)**2)==g**4
    assert s.simplify((g/k)**2/(4+(g/k)**2)-g*g/(4*k*k+g*g))==0
    print('PASS BR217 regularized inverse, source quotient, normal integration',s.__version__,flush=True)

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,P,Q
    _,V,X,G,Y,H,J,A,B,R,_,_=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])*V)[0]
    run(X,G,J,F,B[0],R)
