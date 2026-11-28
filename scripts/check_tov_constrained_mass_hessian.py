"""Original TOV constrained time-symmetric radial ADM mass Hessian.
Moving level-set boundary; negative second variation, NOT a spectral theorem.
"""
import sympy as s
r,R,v,m=s.symbols('r R v m',positive=True); x,l=s.symbols('x l',positive=True); p=l/(8*s.pi)
rho=(2+l)*p*(1-x); pr=-p*(1-x)**2
f=1-l*(2+l)*(x/3-x*x/5); P=(2+l)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
pt=s.factor(pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*f)); a=s.factor((rho+pt)/2); d=s.factor((rho+pr)/(2*f)); V=s.factor(rho-2*a-d*f)
f0=f.subs(x,r*r); m0=r*(1-f0)/2; d0=d.subs(x,r*r)
W=d.subs(x,R*R)*(1-2*m/r)*v*v+2*a.subs(x,R*R)*R*R/r**2+V.subs(x,R*R)
at=lambda z:s.cancel(z.subs({R:r,v:1,m:m0},simultaneous=True)); eq=lambda z:s.cancel(z)==0
A=8*s.pi*r*r*d0*f0
assert eq(s.diff(A,r)+8*s.pi*r*d0*A-4*s.pi*r*r*at(s.diff(W,R)))
assert eq(A-4*s.pi*r*r*at(s.diff(W,v)))
assert eq(at(s.diff(W,m))+2*d0/r)
assert eq(8*s.pi*r*d0-r*l*P.subs(x,r*r)/f0+s.diff(f0,r)/(2*f0))
# m_e'=4pi r² W, first variation mu=A u.
# Second derivative solves mu2'+8pi r d mu2=4pi r² z^T H z.
# j'/j=8pi r d, j(1)=1. Moving upper endpoint r_b=1/(1+e)
# for R=(1+e)r gives boundary term 2 phi mu'(1)+phi² m''(1)
# (m'(1)=0), equal to -4pi rho_r(1) for u=r, phi=-1.
assert eq(s.diff(A*r,r).subs(r,1)-s.diff(m0,r,2).subs(r,1))
boundary=s.cancel((-2*s.diff(A*r,r)+s.diff(m0,r,2)).subs(r,1)/(4*s.pi*p))
assert eq(boundary-2*(2+l))
H=s.hessian(W,(R,v,m)); vec=s.Matrix([r,1,A*r]); I=s.factor(r*r*at((vec.T*H*vec)[0])/p)
assert eq(s.integrate(s.limit(I,l,0),(r,0,1))+4+s.Rational(4,5))
I=s.factor(I.subs(l,s.Rational(1,10)))
num,den=s.fraction(I)
def interval(poly,a,b):
    lo=hi=s.S.Zero
    for c in s.Poly(poly,r).all_coeffs():
        v=[lo*a,lo*b,hi*a,hi*b];lo,hi=min(v)+c,max(v)+c
    return lo,hi
upper=s.S.Zero
for i in range(256):
    a0,b0=s.Rational(i,256),s.Rational(i+1,256)
    n0,n1=interval(num,a0,b0);d0_,d1_=interval(den,a0,b0);assert d0_>0
    q=max(n0/d0_,n0/d1_,n1/d0_,n1/d1_)
    upper+=max(q,s.Rational(47,50)*q)/256
# donor f>=93/100, 0<=8pi r d<=lambda(2+lambda)r(1-r²)/f.
# Thus j=exp(-integral 8pi r d) >= 1-lambda(2+lambda)/(4 fmin).
assert 1-s.Rational(1,10)*s.Rational(21,10)/(4*s.Rational(93,100))>s.Rational(47,50)
bound=upper+boundary.subs(l,s.Rational(1,10))
assert bound<0
print('PASS exact constrained radial mass variation and moving boundary term')
print('PASS rational certified normalized ADM mass Hessian upper bound',float(bound))
print('OPEN dynamical domain, conserved charges, spectral instability, alternative constitutive action')
