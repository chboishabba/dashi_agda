import sympy as s
from itertools import combinations

def run(X,G,J,F,A,B,R):
    P=list(combinations(range(5),2)); I=s.eye(35); j=-s.Rational(6,5)
    def ext(xi):
        return s.Matrix.vstack(*(xi[a]*X[10*P.index((b,c))+q,:]-xi[b]*X[10*P.index((a,c))+q,:]+xi[c]*X[10*P.index((a,b))+q,:] for a,b,c in combinations(range(5),3) for q in range(10)))
    Cn=ext([0,0,0,0,1])
    for sig in (-1,1):
        u=(1+sig*s.I)/20; d=1+u*u; k=s.Integer(100)
        tau=s.cancel(k*sig*s.I*(1-u*u)/d); lam=s.cancel(2*k*u/d)
        assert s.re(tau)>0 and s.re(lam)>0 and s.cancel(lam**2-tau**2-k*k)==0
        N=s.Matrix.hstack(*ext([tau,s.I*k,0,0,-lam]).nullspace())
        assert N.cols==5
        assert ((tau*I-s.I*k*A[0]+lam*A[3])*N).applyfunc(s.cancel)==s.zeros(35,5)
        p=s.Matrix([s.Rational((i*i+3*i)%17-8,7) for i in range(35)]); q=p[::-1,0]
        D=ext([tau,s.I*k,0,0,-1]); fp=D*p; fm=D*q
        assert fp!=s.zeros(100,1) and fm!=s.zeros(100,1)
        wall=tau*s.eye(9)-s.I*k*B
        T=((I-F)*N).row_join((I+F)*N).row_join(-j*J).col_join(s.zeros(9,5).row_join(R*N).row_join(wall))
        v=s.Matrix([s.Rational(i+1,19) for i in range(19)])
        particular=(p-F*q).col_join(R*(p+F*q)/2)
        forcing=T*v+particular
        corrected=forcing-particular
        ids=list(T.T.rref()[1]); assert len(ids)==19
        recovered=T[ids,:].inv()*corrected[ids,:]
        assert (recovered-v).applyfunc(s.cancel)==s.zeros(19,1)
        assert (T*recovered+particular-forcing).applyfunc(s.cancel)==s.zeros(44,1)
        a=v[:5,:]; b=v[5:10,:]; wp=N*(a+b); wm=N*(a-b)
        assert (ext([tau,s.I*k,0,0,-lam])*wp).applyfunc(s.cancel)==s.zeros(100,1)
        assert (ext([tau,s.I*k,0,0,-lam])*wm).applyfunc(s.cancel)==s.zeros(100,1)
        assert (R*(wp+F*wm)/2-R*N*b).applyfunc(s.cancel)==s.zeros(9,1)
        assert (fp-(ext([tau,s.I*k,0,0,0])*p-Cn*p)).applyfunc(s.cancel)==s.zeros(100,1)
        print('sign',sig,'compatible forced lift, full exterior and 44 boundary rows PASS',flush=True)
    print('PASS BR218 manufactured particular plus homogeneous correction',s.__version__,flush=True)

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,P,Q
    _,V,X,G,Y,H,J,A,B,R,_,_=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])*V)[0]
    run(X,G,J,F,A,B[0],R)
