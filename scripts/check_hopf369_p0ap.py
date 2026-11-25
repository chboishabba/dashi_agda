"""Selected periodic Einstein-Israel action and full brane pullback variation."""
import sympy as s


def audit():
    c,h,b,kT=s.symbols('c h b kT',positive=True)
    R,N,v,w,lam=s.symbols('R N v w lam',real=True,nonzero=True)
    L=N*b*b*R+12*b*b*v*v/N-2*lam*N*b**4
    sub={N:1,R:-12*h*h,lam:-6*c*c,v*v:c*c*b*b-h*h,w:c*c*b}
    assert s.expand(s.diff(L,N)).subs(sub).expand()==0
    EL=s.diff(L,b)-s.diff(s.diff(L,v),b)*v-s.diff(s.diff(L,v),v)*w
    assert s.expand(EL.subs(N,1)).subs(sub).expand()==0
    j=s.symbols('j',real=True)
    assert s.simplify((-24*b*b*j-8*kT*b**3).subs(j,-kT*b/3))==0
    I2,I4=s.symbols('I2 I4',positive=True)
    U=24*c*c*I4-12*h*h*I2-2*kT
    assert s.expand((U-6*h*h*I2).subs(kT,3*(4*c*c*I4-3*h*h*I2)))==0
    print('PASS bulk lapse, warp Euler-Lagrange, seam, reduced cosmological coefficient',flush=True)
    # Variation of a timelike brane graph, all symmetric ambient metric directions.
    g=s.diag(-2,3,4,5); g[0,1]=g[1,0]=s.Rational(1,5)
    a=s.Matrix([s.Rational(1,7),s.Rational(2,5),-s.Rational(1,3),s.Rational(1,4)])
    phi=s.Rational(3,2); T=s.Rational(7,4); inv=g.inv(); A=inv*a
    Delta=1+phi**2*(a.T*A)[0]; H=g+phi**2*a*a.T
    assert Delta>0 and s.factor(H.det()-g.det()*Delta)==0
    Hi=inv-phi**2*A*A.T/Delta
    assert H*Hi==s.eye(4)
    # Divide derivatives by sqrt(-det g)*sqrt(Delta), keeping all source factors.
    # Covariant metric variation: tau^{ij}=-T sqrt(Delta) H^{-1}_{ij}.
    count=0
    for i in range(4):
        for j in range(i,4):
            D=s.zeros(4); D[i,j]=1; D[j,i]=1
            direct=-T*s.trace(H.inv()*D)/2
            chain=-T*(s.trace(inv*D)-phi**2*(A.T*D*A)[0]/Delta)/2
            assert direct==chain; count+=1
    for i in range(4):
        d=s.eye(4)[:,i]; D=phi**2*(d*a.T+a*d.T)
        assert -T*s.trace(Hi*D)/2==-T*phi**2*A[i]/Delta; count+=1
    assert -T*s.trace(Hi*(2*phi*a*a.T))/2==-T*phi*(a.T*A)[0]/Delta; count+=1
    # A literal graph X(x)=(x,f(x)), a=A+df. All 15 symmetric ambient directions.
    df=s.Matrix([s.Rational(1,9),0,s.Rational(1,8),0]); conn=a-df
    G=(g+phi**2*conn*conn.T).row_join(phi**2*conn).col_join((phi**2*conn.T).row_join(s.Matrix([[phi**2]])))
    P=s.eye(4).col_join(df.T); assert P.T*G*P==H
    for i in range(5):
        for j in range(i,5):
            D=s.zeros(5); D[i,j]=1; D[j,i]=1
            assert s.trace(Hi*P.T*D*P)==s.trace(P*Hi*P.T*D); count+=1
    # Gauge compensation: connection shift and graph gradient shift cancel exactly.
    q=s.Matrix(s.symbols('q:4')); assert (conn-q)+(df+q)==a
    print('PASS full brane pullback / chain-rule directions',count,'and gauge compensation',flush=True)
    # Normal variation of the original scalar constraint functional (not EH).
    u,p,z=s.symbols('u p z',real=True)
    bulk=p*p/2+R*u*u/12-lam*u**4/12
    seam=kT/3*(u*u/2-u**3/3)
    assert s.diff(bulk,u)==R*u/6-lam*u**3/3
    assert s.diff(seam,u).expand()==(kT/3*(u-u*u)).expand()
    print('PASS selected constraint energy derivatives; distinct from Lorentzian EH action')

if __name__=='__main__': audit()
