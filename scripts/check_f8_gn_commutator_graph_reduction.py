"""F8 W2: use original wave equation to eliminate the normal second jet.
The remaining k-weighted source demands a spatial graph-energy level.
"""
import sympy as s

def exact():
    A,B,C,At,Bt,Ct,Att,Btn,Bn,F=s.symbols(
        'A B C At Bt Ct Att Btn Bn F',nonzero=True,real=True)
    u,p,q,pt,qn=s.symbols('u p q pt qn',real=True)
    # Physical original wave L u = F, with u_t=p,u_n=q.
    residual=-At*p-A*pt+Bn*q+B*qn-C*u-F
    q_reconstructed=s.solve(residual,qn)[0]
    comm=Att*p+At*pt-Btn*q-Bt*qn+Ct*u
    rA,rB,rC,drA,drBn=s.symbols('rA rB rC drA drBn',real=True)
    # A_t/A=rA, B_t/B=rB, C_t/C=rC;
    # A_tt/A=rA_t+rA², B_tn=B_n rB+B drB_n.
    replacements={At:A*rA,Bt:B*rB,Ct:C*rC,
                  Att:A*(drA+rA*rA),Btn:Bn*rB+B*drBn}
    reduced=s.factor(comm.subs(qn,q_reconstructed).subs(replacements, simultaneous=True))
    target=(A*(drA+rA*(rA-rB))*p+A*(rA-rB)*pt
            -B*drBn*q+C*(rC-rB)*u-rB*F)
    assert s.factor(reduced-target)==0
    # Original GN geometry simplifies both dangerous coefficient differences.
    t,n,k=s.symbols('t n k',positive=True)
    a=s.sinh(s.asinh(t)-n)
    N=s.cosh(s.asinh(t)-n)/s.sqrt(1+t*t)
    ra=3*s.diff(a,t)/a-s.diff(N,t)/N
    rb=3*s.diff(a,t)/a+s.diff(N,t)/N
    rc=s.diff(a,t)/a+s.diff(N,t)/N
    assert s.simplify(ra-rb+2*s.diff(N,t)/N)==0
    assert s.simplify(rc-rb+2*N/a)==0
    # B/A=N², C/A=(N/a)² k², exact coefficients for graph norm.
    AA=a**3/N;BB=N*a**3;CC=N*a*k*k
    assert s.simplify(BB/AA-N*N)==0
    assert s.simplify(CC/AA-(N/a)**2*k*k)==0
    # Uniform frequency graph level: k² E0, not merely E0+E1.
    x,y,z=s.symbols('x y z',real=True)
    h=s.symbols('h',positive=True)
    assert s.expand((h*x*x+y*y/h-2*x*y)-(s.sqrt(h)*x-y/s.sqrt(h))**2)==0
    # A positive E0+E1 cannot control k²|u| in the source norm uniformly.
    kk=s.symbols('kk',positive=True)
    assert s.limit(kk**2/s.sqrt(1+kk**2),kk,s.oo)==s.oo
    print('PASS exact original-wave radial-jet elimination and necessary k² graph-energy level')

if __name__=='__main__':exact()
