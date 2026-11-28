"""BR222: invariant normal DAE split and bounded intrinsic particular lift."""
import sympy as s
import numpy as np
from check_hopf369_br220_normal_constraint_propagation import symbols

def run(X,G):
    C,K=symbols(X,G); I=s.eye(35); L=K[4]; Q=s.eye(100)-C[4]*L
    assert L*C[4]==I
    # Verify universal axial polynomial using interpolation: homogeneous degree five.
    # Five powers in A plus lambda^2 and lambda^4 terms have degree five.
    for k in range(6):
        b=C[0]+s.I*k*C[1]; A=-L*b; q=1+k*k
        assert A*(A*A-q*I)*(4*A*A-q*I)==s.zeros(35)
        Pnum=4*A**4-q*A*A
        assert Q*b*Pnum==s.zeros(100,35)
        assert s.trace(Pnum)==30*q*q
    print('PASS universal axial normal polynomial: six exact degree-five coefficients by interpolation',flush=True)
    for sig in (-1,1):
        t=1+sig*s.I;k=2;b=t*C[0]+s.I*k*C[1]; A=-L*b; q=t*t+k*k; D=Q*b
        P=(4*A**4-q*A*A)/(3*q*q); P=P.applyfunc(s.cancel)
        eq=lambda a,b: (a-b).applyfunc(s.cancel)==s.zeros(*a.shape)
        assert eq(P*P,P) and eq(A*P,P*A) and eq(A*A*P,q*P)
        assert P.rank()==10 and D.rank()==25 and eq(D*P,s.zeros(100,35))
        E=I-P; rows=list(D.T.rref()[1]); cols=list(D.rref()[1]); S=I[:,cols]; V=E*S*D.extract(rows,cols).inv()*s.eye(100)[rows,:]
        assert eq(V*D,E) and eq(D*V*D,D) and eq(P*V,s.zeros(35,100))
        Kt=t*K[0]+s.I*k*K[1]
        Vpoly=-(4*A*A+3*q*I)*Kt/(3*q*q)
        assert eq(Vpoly*D,E)
        print('sign',sig,'rank10 physical/rank25 algebraic; exact inverse and commutation PASS',flush=True)
    # Numerical stable particular lift for nonconstant compatible f.
    arr=lambda a:np.asarray(a.tolist(),complex)
    C=list(map(arr,C)); K=list(map(arr,K)); L=K[4]; Q=np.eye(100)-C[4]@L; G=arr(G)
    length=2*np.log(2); rng=np.random.default_rng(369)
    worst=0.; worstode=0.; cases=0
    for sig in (-1,1):
      for gamma in (.5,2.):
       for k in (2.,100.,10000.):
        t=gamma+sig*1j*k; q=t*t+k*k; lam=np.sqrt(q); b=t*C[0]+1j*k*C[1]; A=-L@b; D=Q@b
        # Numerical spectral projections via polynomial can cancel badly at large k.
        P=(4*np.linalg.matrix_power(A,4)-q*A@A)/(3*q*q); E=np.eye(35)-P
        Pp=(P+A@P/lam)/2; Pm=(P-A@P/lam)/2
        w0=rng.normal(size=35)+1j*rng.normal(size=35); w1=rng.normal(size=35)+1j*rng.normal(size=35)
        f0=C[4]@w1+b@w0; f1=b@w1
        # For manufactured affine w, stable Green integrals equal the
        # affine physical projection minus homogeneous endpoint terms.
        for y in (0.,length/3,2*length/3,length):
            w=w0+y*w1; minus=np.exp(-lam*y)*(Pm@w0); plus=np.exp(-lam*(length-y))*(Pp@(w0+length*w1))
            v=E@w+P@w-minus-plus; dv=w1+lam*minus-lam*plus
            f=f0+y*f1
            err=np.linalg.norm(C[4]@dv+b@v-f)/max(1,np.linalg.norm(f)); ode=np.linalg.norm(dv-A@v-L@f)/max(1,np.linalg.norm(L@f)); worst=max(worst,err);worstode=max(worstode,ode)
        cases+=1
    assert worst<1e-5 and worstode<1e-5
    print('diagnostic',cases,'max full exterior relative residual',worst,'max normal ODE relative residual',worstode,flush=True)
    print('PASS BR222 exact split',s.__version__,flush=True)
if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier
    _,_,X,G,_,_,_,_,_,_,_,_=carrier()
    run(X,G)
