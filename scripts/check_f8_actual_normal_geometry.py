"""Actual F8 GN background and frozen optical principal DtN.
The finite collar Dirichlet model is not the full exterior coupled IBVP.
"""
import sympy as s
import mpmath as mp


def exact():
    t,n=s.symbols('t n',positive=True); beta=s.sqrt(1+t**-2)
    A=s.cosh(n)-beta*s.sinh(n); a=t*A
    N=s.cosh(n)-s.sinh(n)/beta
    eq=lambda x:s.simplify(s.expand_trig(x))==0
    assert eq(a.diff(t)-N)
    assert eq(a.diff(n,2)-a) and eq(N.diff(n,2)-N)
    assert eq(a.diff(n)**2-a*a-1)
    assert eq(N.diff(n)*a.diff(n)-N*a)
    assert eq((N.diff(n)*A-N*A.diff(n))-(beta-1/beta))
    assert eq((N*N/A**2).diff(n).subs(n,0)-2*(beta-1/beta))
    assert eq(a.diff(n).subs(n,0)/t+beta) and eq(N.diff(n).subs(n,0)+1/beta)
    # Frame connection checks: metric compatibility and torsion for the frame.
    h,k0,k=s.symbols('h k0 k',real=True); g=s.diag(-1,1,1,1,1)
    C=[s.zeros(5) for _ in range(5)] # columns = differentiated vector
    C[0][4,0]=C[0][0,4]=k0
    for i in range(1,4):
        C[i][0,i]=C[i][i,0]=h; C[i][4,i]=-k; C[i][i,4]=k
    assert all(c.T*g+g*c==s.zeros(5) for c in C)
    # [e0,ei]=-h ei, [en,e0]=-k0 e0, [en,ei]=-k ei
    eye=s.eye(5)
    assert all(C[0][:,i]-C[i][:,0]==-h*eye[:,i] for i in range(1,4))
    assert C[4][:,0]-C[0][:,4]==-k0*eye[:,0]
    assert all(C[4][:,i]-C[i][:,4]==-k*eye[:,i] for i in range(1,4))
    assert sum((g[i,i]*C[i][:,i] for i in range(5)),s.zeros(5,1))==3*h*eye[:,0]-(k0+3*k)*eye[:,4]
    # Airy model normal equation under x=k^-2/3 X, w=k^4/3 W.
    X,W,d=s.symbols('X W d',positive=True); f=s.airyai(d**s.Rational(1,3)*X+W/d**s.Rational(2,3))
    assert s.simplify(f.diff(X,2)-(W+d*X)*f)==0
    # Clock block determinant with arbitrary scalar DtN M (not sqrt(w)).
    z,k,M,K,w=s.symbols('z k M K w',nonzero=True)
    u=s.Matrix([[-z/2,s.I*k,-3*z/2]]); c=K*s.Matrix([10*z,6*s.I*k,2*z])/w
    assert s.expand((u*c)[0]*w+K*(8*z*z+6*k*k))==0
    assert s.cancel((M-(u*c)[0]).subs(z*z,w-k*k)-(M+8*K-2*K*k*k/w))==0
    return 15


def airy_m(W,d):
    a=d**(mp.mpf(1)/3); x=W/a**2
    return -a*mp.airyai(x,1)/mp.airyai(x)


def root(f,lo,hi):
    for _ in range(150):
        m=(lo+hi)/2
        if f(m)>0:hi=m
        else:lo=m
    return (lo+hi)/2


def diagnostic():
    mp.mp.dps=60
    for t in map(mp.mpf,(1,3,12)):
        B=mp.sqrt(1+t**-2); d=2*(B-1/B); K=t**-2/(3*B)-t**-4/12
        # Limiting surface dispersion W*m_A(W)=2K.
        W=root(lambda W:W*airy_m(W,d)-2*K,mp.mpf(0),(2*K)**(mp.mpf(2)/3))
        flat=(2*K)**(mp.mpf(2)/3)
        assert 0<W<flat and abs(W*airy_m(W,d)-2*K)<mp.mpf('1e-40')
        print('t',t,'Airy root / flat root',mp.nstr(W/flat,14))
        for re,im in [(1,1),(0,1),(-1,2),(1,-1)]:
            Z=mp.mpc(re,im); M=airy_m(Z,d)
            assert mp.im(M)*im>0
            assert mp.im(M+8*K-2*K/Z)*im>0
    print('12 complex-sign diagnostics and 3 limiting surface roots PASS')


if __name__=='__main__':
    print(s.__version__, exact(),'grouped exact checks PASS'); diagnostic()
