"""AZ: exact volume/shape collar algebra and conformal re-solve negative control.
Standard Gauss/conformal identities; local analytic CK reduction, not global solve.
Source: AY #1554 7268c6ae, check_hopf369_p0ay_jets.py.
"""
import sympy as s


def audit():
    j,m,p2p,p2m,R,Lambda,v=s.symbols('j m p2p p2m R Lambda v', real=True)
    a,b,c,d,e=s.symbols('a b c d e',real=True)
    A=s.Matrix([[a,b,c],[b,d,e],[c,e,-a-d]])
    I=s.eye(3); tf=lambda X:X-s.trace(X)*I/3
    ex=lambda X:X.applyfunc(s.expand)
    pp,pm=m+j/2,m-j/2
    # H=exp(2p) exp(S) in common H0-orthonormal frame;
    # S'=A, S''+=-2j A, S''-=+2j A; p(0)=S(0)=0.
    Bp,Bm=-2*j*A,2*j*A
    kp,km=pp*I+A/2,pm*I+A/2
    D=lambda t,q,B:(q+2*t*t)*I+2*t*A+(B+A*A)/2
    Dp,Dm=D(pp,p2p,Bp),D(pm,p2m,Bm)
    assert ex(kp-km-j*I)==s.zeros(3)
    assert ex(tf(Dp-Dm))==s.zeros(3)
    # Gauss scalar expression independent of shape acceleration B (trace zero).
    for k,Dn,t,q in ((kp,Dp,pp,p2p),(km,Dm,pm,p2m)):
        scalar=R-2*s.trace(Dn)+3*s.trace(k*k)-s.trace(k)**2
        assert s.expand(scalar-(R-6*q-12*t*t-s.trace(A*A)/4))==0
    solve=lambda t:(R-12*t*t-s.trace(A*A)/4-2*Lambda)/6
    Dpc,Dmc=Dp.subs(p2p,solve(pp)),Dm.subs(p2m,solve(pm))
    assert ex(Dpc-Dmc)==s.zeros(3)
    for k,Dn in ((kp,Dpc),(km,Dmc)):
        assert s.expand(R-2*s.trace(Dn)+3*s.trace(k*k)-s.trace(k)**2-2*Lambda)==0
    # Actual time-symmetric lapse first-jet conditions.
    N=s.symbols('N',positive=True); M=(kp+km)/2
    Np,Nm=N*(-s.trace(M)+j/2),N*(-s.trace(M)-j/2)
    assert s.expand(Np-Nm-j*N)==0
    assert s.expand((Np+Nm)/(2*N)+s.trace(M))==0
    # Independent conformal re-solve: q=log v, [n q]=j(v-1).
    # Four-dimensional spatial Ricci TF jump transforms by -2 M_TF [n q].
    X=s.Matrix([[s.Symbol('J'+str(min(i,k))+str(max(i,k))) for k in range(3)] for i in range(3)])
    RicTF=-tf(X)+j*tf(M)
    newRicTF=RicTF-2*tf(M)*j*(v-1)
    newJTF=j*v*tf(M)-newRicTF
    assert ex(newJTF-tf(X)-3*j*(v-1)*tf(M))==s.zeros(3)
    assert newJTF.subs({v:2,j:1,a:1,b:0,c:0,d:-1,e:0,**{x:0 for x in X}})!=s.zeros(3)
    print('PASS first jump, five shape jets, both scalar constraints, full J2, lapse, conformal drift/negative control',flush=True)


if __name__=='__main__': audit()
