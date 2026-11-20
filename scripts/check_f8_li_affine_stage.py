"""Exact stage algebra transcribed from mode 3 at blob 6f75288d.
Not a full solver replay. Check compact affine lift and SSPRK3 translation defect.
"""
import sympy as s

def check():
    h,v,b,G,GT,vt,lam=s.symbols('h v b G GT vt lam', nonzero=True)
    a,c=1+v,1-v
    count=0
    for n in (3,5,8):
        D=s.zeros(n)
        D[0,0],D[0,1],D[-1,-2],D[-1,-1]=-1,1,-1,1
        for i in range(1,n-1): D[i,i-1],D[i,i+1]=-s.Rational(1,2),s.Rational(1,2)
        D/=h
        chi=s.Matrix([(1-s.Rational(i,n-1))**4 for i in range(n)])
        L=G/v*chi; LT=(GT/v-G*vt/v**2)*chi
        U=s.zeros(n,1); P=L; M=L
        # Literal mode-3 stage: common radial and warp force, incoming SATs.
        force=-lam*U-s.diag(*[3/(2*(b+i*h)) for i in range(n)])*(P-M)
        dU=(a*P+c*M)/2; dP=a*D*P+force; dM=-c*D*M+force
        dP[-1]-=2*a*P[-1]/h
        dM[0]+=2*(a*P[0]-c*M[0]-2*G)/h
        for actual,expected in ((dU,L),(dP-LT,a*D*L-LT),(dM-LT,-c*D*L-LT),(D*dU-(dP-dM)/2,U)):
            assert all(s.expand(x)==0 for x in actual-expected); count+=1
    # A pure time-dependent shift of u'=0 exposes a finite RK quadrature defect.
    T,k=s.symbols('T k'); p=s.symbols('p0:5')
    L=sum(p[j]*T**j for j in range(5)); f=-s.diff(L,T)
    inc=k*(f+f.subs(T,T+k)+4*f.subs(T,T+k/2))/6
    assert s.expand(inc+L.subs(T,T+k)-L)==0; count+=1
    L=T**5; f=-s.diff(L,T)
    inc=k*(f+f.subs(T,T+k)+4*f.subs(T,T+k/2))/6
    assert s.expand(inc+L.subs(T,T+k)-L)==-k**5/24; count+=1
    # Exact stage-wise affine translation of original Shu-Osher updates.
    x,l0,l1,lh,F0,F1,Fh=s.symbols('x l0 l1 lh F0 F1 Fh')
    y=x-l0; x1=x+k*F0; y1=y+k*F0+l0-l1
    assert s.expand(y1+l1-x1)==0; count+=1
    x2=3*x/4+(x1+k*F1)/4; y2=3*y/4+(y1+k*F1)/4+3*l0/4+l1/4-lh
    assert s.expand(y2+lh-x2)==0; count+=1
    x3=(x+2*(x2+k*Fh))/3; y3=(y+2*(y2+k*Fh))/3+l0/3+2*lh/3-l1
    assert s.expand(y3+l1-x3)==0; count+=1
    print(f'{count}/{count} exact SymPy assertions PASS')
if __name__=='__main__': check()
