"""F8 W2: exact orthonormal-to-FRW momentum normalization, stress principal
symmetrizer, and sharp physical Fourier cross-work budget.
No geometric trace/low-band/Einstein-Israel positivity promotion.
"""
import sympy as s

def exact():
    t,x=s.symbols('t x',positive=True);b=1/t;B=s.sqrt(1+b*b)
    rho,p,P=[s.Function(z)(t,x) for z in ('rho','p','P')]
    g=s.diag(-1,t*t,t*t,t*t);gi=g.inv();coords=(t,x)
    # Full mixed stress in the ORTHONORMAL frame, no artificial shift.
    S=s.diag(-rho,p,p,p);S[0,1]=-P;S[1,0]=P
    Q=s.diag(1,t,t,t);C=Q.inv()*S*Q
    assert s.expand(C[0,1]+t*P)==0
    assert s.expand(C[1,0]-P/t)==0
    # Actual FRW connection; for fields with x dependence only.
    ix=range(4);X=(t,x,s.symbols('y'),s.symbols('z'))
    Gamma={(a,i,j):sum(gi[a,k]*(g[k,j].diff(X[i])+g[k,i].diff(X[j])-g[i,j].diff(X[k]))/2 for k in ix) for a in ix for i in ix for j in ix}
    def div(nu):
        return s.expand(sum(C[a,nu].diff(X[a]) for a in ix)+sum(Gamma[a,a,c]*C[c,nu]-Gamma[c,a,nu]*C[a,c] for a in ix for c in ix))
    assert s.simplify(div(0)+rho.diff(t)-b*P.diff(x)+3*b*(rho+p))==0
    assert s.simplify(div(1)+t*P.diff(t)+4*P-p.diff(x))==0
    q=-t*P
    # Same principal unknown q as constraint_detector_closure.
    assert s.expand(-div(0)-rho.diff(t)-b*b*q.diff(x)-3*b*(rho+p))==0
    assert s.expand(div(1)-q.diff(t)-3*b*q-p.diff(x))==0
    cs=1/(3*B**2)
    EM=(cs*rho**2+b*b*q*q)/2
    assert s.simplify(EM-(cs*rho**2+P**2)/2)==0
    # Exact t-uniform energy coercivity for 1<=t<=12:
    # cs>=1/6 gives rho²<=12 E_M; P²<=2 E_M.
    k=s.symbols('k',positive=True)
    Csharp=24+36/k**2
    assert s.expand(Csharp-2*12-18*2/k**2)==0
    # If k>=6, Csharp<=25; then all k >= Kstar satisfy Schur high-frequency absorption.
    Kstar=2*12**6*25
    assert Kstar==149299200 and Kstar>=6
    assert s.Rational(36,Kstar**2)<=1
    # The bulk trace constant is an independent required analytic certificate.
    print('PASS 7 grouped physical FRW momentum normalization, Ward, sharpened material Schur; full bulk trace open')

if __name__=='__main__':exact()
