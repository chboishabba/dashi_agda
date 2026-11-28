"""Independent Schwarzschild vacuum master reconstruction two-jet oracle.
Axisymmetric rational manufactured master Cauchy jets; not an interface inverse.
"""
import sympy as s
from itertools import product
I=range(4); Z=lambda:s.zeros(4)

def ricci1(g,dg,ddg,h,dh,ddh):
    G=g.inv(); H=-G*h*G
    dG=[-G*d*G for d in dg]
    dH=[-dG[k]*h*G-G*dh[k]*G-G*h*dG[k] for k in I]
    def low(D,a,b,c):return (D[b][a,c]+D[c][a,b]-D[a][b,c])/2
    def conn(A,D,a,b,c):return sum(A[a,j]*low(D,j,b,c) for j in I)
    C={(a,b,c):conn(G,dg,a,b,c) for a,b,c in product(I,repeat=3)}
    E={(a,b,c):conn(H,dg,a,b,c)+conn(G,dh,a,b,c) for a,b,c in product(I,repeat=3)}
    def de(k,a,b,c):return conn(dH[k],dg,a,b,c)+conn(H,ddg[k],a,b,c)+conn(dG[k],dh,a,b,c)+conn(G,ddh[k],a,b,c)
    return s.Matrix(4,4,lambda b,c:s.cancel(sum(de(a,a,b,c)-de(c,a,b,a)+sum(E[a,a,j]*C[j,b,c]+C[a,a,j]*E[j,b,c]-E[a,c,j]*C[j,b,a]-C[a,c,j]*E[j,b,a] for j in I) for a in I)))

def main():
    t,r,th,ph=s.symbols('t r theta phi',real=True); x=(t,r,th,ph)
    M=s.Rational(7,500); F=1-2*M/r; g=s.diag(-F,1/F,r*r,r*r*s.sin(th)**2)
    for ell in (2,3):
      n=s.Rational((ell-1)*(ell+2),2); L=ell*(ell+1)
      Y=s.legendre(ell,s.cos(th)); S=s.sin(th)*s.diff(Y,th)
      for r0 in (s.S.One,s.Rational(3,2)):
        pt={t:0,r:r0,th:s.acos(s.Rational(4,5)),ph:0}
        ev=lambda A:A.subs(pt).applyfunc(s.simplify)
        def jets(A):
            B=[A.diff(t,k).subs(t,0) for k in range(3)]
            def jet(ks):
                v=B[ks.count(t)]
                for k in ks:
                    if k!=t:v=v.diff(k)
                return ev(v)
            return jet([]),[jet([k]) for k in x],[[jet([k,j]) for j in x] for k in x]
        base=jets(g)
        for parity in ('odd','even'):
          V=F*(L/r**2-6*M/r**3) if parity=='odd' else 2*F*(n*n*(n+1)*r**3+3*n*n*M*r*r+9*n*M*M*r+9*M**3)/(r**3*(n*r+3*M)**2)
          wave=lambda u:s.cancel(F*s.diff(F*s.diff(u,r),r)-V*u)
          a=1+r+r*r/3; b=r-r*r/5
          # Need fourth time jet for even h_rr and h_tt, containing psi_rr.
          p=a+t*b+t*t*wave(a)/2+t**3*wave(b)/6+t**4*wave(wave(a))/24
          h=Z()
          if parity=='odd':
            h[0,3]=h[3,0]=-F*s.diff(r*p,r)*S/2
            h[1,3]=h[3,1]=-r*s.diff(p,t)*S/(2*F)
            master=r**3/n*(s.diff(h[1,3]/(r*r*S),t)-s.diff(h[0,3]/(r*r*S),r))
          else:
            A=(n*(n+1)*r*r+3*n*M*r+6*M*M)/(r*r*(n*r+3*M))
            K=A*p+F*s.diff(p,r)
            H2=( (n+3*M/r)*((n+1)*p/r-K)/F+r*s.diff(K,r) )
            H1=r*s.diff(p,t,r)+(n*r*r-3*n*M*r-3*M*M)/((r-2*M)*(n*r+3*M))*s.diff(p,t)
            h[0,0]=F*H2*Y;h[1,1]=H2*Y/F;h[0,1]=h[1,0]=H1*Y
            h[2,2]=r*r*K*Y;h[3,3]=r*r*s.sin(th)**2*K*Y
            master=r/(n+1)*(K+F/(n+3*M/r)*(H2-r*s.diff(K,r)))
          assert s.simplify((master-p).subs(pt))==0
          res=ricci1(*base,*jets(h))
          assert res==Z(),(ell,r0,parity,res)
          print('PASS',ell,r0,parity,flush=True)
if __name__=='__main__':main()
