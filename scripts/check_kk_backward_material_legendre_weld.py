"""Backward weld of existing Cube27 response and fixed-flux inverse.
Local Legendre jet; no identification of prescribed q with physical CY modulus.
"""
import sympy as s

def check():
    E,q,P=s.symbols('E q P', real=True)
    chi=s.symbols('chi', positive=True)
    m,k=s.symbols('m k', real=True)
    F=-chi*E**2/2+m*E*q+k*q*q/2
    e=s.solve(P+s.diff(F,E),E)[0]
    W=s.expand((F+E*P).subs(E,e))
    assert s.simplify(W-(P+m*q)**2/(2*chi)-k*q*q/2)==0
    C=s.diff(W,P,2); L=s.diff(W,P,q); Z=s.diff(W,q,2)
    assert s.simplify(Z-L**2/C-k)==0
    F0=s.symbols('F0',real=True)
    p=s.solve(s.diff(W,P)-F0,P)[0]
    assert s.simplify((W-F0*P).subs(P,p)-F.subs(E,F0))==0
    X,t,D,B,g,A,b,Lam,beta=s.symbols('X t Delta B gamma fluxshift biasflux Lambda beta', real=True)
    ell=m/chi
    U=(D-A)*X**2/2+g*X**4/4-(B+b)*X+P**2/(2*chi)+beta*P**4/4+ell*X*P+Lam*X*P**2/2-F0*P
    inv=s.solve(s.diff(U,X).subs(X,t),D)[0]
    assert s.simplify(t*inv-(A*t+B+b-g*t**3-ell*P-Lam*P**2/2))==0
    C=s.diff(U,P,2).subs(X,t); L=s.diff(U,X,P).subs(X,t)
    Z=s.diff(U,X,2).subs({X:t,D:inv},simultaneous=True)
    assert s.simplify(Z-L**2/C-((B+b-ell*P-Lam*P**2/2)/t+2*g*t*t-L**2/C))==0
    print('PASS Legendre sign, both Hessian terms, fixed-field force, nonlinear inverse and relaxed curvature')

def native_receipt():
    from kk_cube27_nonlinear_weld import weld
    for N in (2,3):
        for U in (1,4):
            for flux in (0,1.5):
                chi,beta,m=weld(N,U,flux)
                assert chi>0
                print('native Legendre jet',N,U,flux,'C',1/chi,'L',m/chi,'direct shift',m*m/chi,'Schur debit',m*m/chi,'beta',beta)

if __name__=='__main__':
    import sys
    check()
    if '--native' in sys.argv:
        native_receipt()
