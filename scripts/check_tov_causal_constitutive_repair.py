"""Background-preserving causal strain correction: radial constrained ADM Hessian.
Exact original TOV donor, selected lambda=1/10. Not a nonlinear stability theorem.
"""
import sympy as s
r,R,v,m=s.symbols('r R v m',positive=True); x,l=s.symbols('x l',positive=True); p=l/(8*s.pi)
rho=(2+l)*p*(1-x); pr=-p*(1-x)**2
f=1-l*(2+l)*(x/3-x*x/5); P=(2+l)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
pt=s.factor(pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*f)); a=s.factor((rho+pt)/2); d=s.factor((rho+pr)/(2*f)); V=s.factor(rho-2*a-d*f)
f0=f.subs(x,r*r); m0=r*(1-f0)/2; d0=d.subs(x,r*r)
W=d.subs(x,R*R)*(1-2*m/r)*v*v+2*a.subs(x,R*R)*R*R/r**2+V.subs(x,R*R)
at=lambda z:s.cancel(z.subs({R:r,v:1,m:m0},simultaneous=True))
A=8*s.pi*r*r*d0*f0
assert s.cancel(s.diff(A,r)+8*s.pi*r*d0*A-4*s.pi*r*r*at(s.diff(W,R)))==0
assert s.cancel(A-4*s.pi*r*r*at(s.diff(W,v)))==0
u,w=s.symbols('u w',real=True); vec=s.Matrix([u,w,A*u]); H=s.hessian(W,(R,v,m))
Q=s.factor(r*r*at((vec.T*H*vec)[0])/p)
# normalized residual: B0^-1/2 (B-B0) B0^-1/2.
z=s.cancel(2*w-(2*A/r+s.diff(f0,r))*u/f0); y=2*u/r
c=p*(1-r*r)/2
Qadd=s.cancel(r*r*c*(4*z*y+2*y*y)/p)
# Background-preserving correction and acoustic rank-one identity.
X=s.Matrix(3,3,lambda i,j:s.Symbol('X%d%d'%(min(i,j),max(i,j))))
T=(s.trace(X)**2-s.trace(X*X))/2
zero={v:0 for v in X}
assert T.subs(zero)==0 and all(s.diff(T,v).subs(zero)==0 for v in set(X))
n=s.Matrix(s.symbols('n0:3',real=True)); b=s.Matrix(s.symbols('b0:3',real=True))
D=n*b.T+b*n.T
assert s.expand(s.trace(D)**2-s.trace(D*D)-2*((n.dot(b))**2-n.dot(n)*b.dot(b)))==0
# Original donor DEC slack: min(a,df) >= c*(1+lambda*slack).
slack=1-s.Rational(21,20)*s.Rational(50,93)
assert slack>0 and s.cancel(d*f/c.subs(r,s.sqrt(x))-(1+l+x))==0
# Kinetic Hessian unchanged (background static); spatial acoustic Hessian
# 2 diag(df,a,a) - 2c(I-n n^T), for unit n. Hence 0<speed²<=1
# in open interior, using donor bound for a; surface degeneracy retained.
def interval(poly,a,b):
    lo=hi=s.S.Zero
    for c in s.Poly(poly,r).all_coeffs():
        vv=[lo*a,lo*b,hi*a,hi*b];lo,hi=min(vv)+c,max(vv)+c
    return lo,hi
def bounds(expr):
    num,den=s.fraction(s.factor(expr)); out=[]
    for i in range(256):
        aa,bb=s.Rational(i,256),s.Rational(i+1,256)
        n0,n1=interval(num,aa,bb);d0_,d1_=interval(den,aa,bb);assert d0_>0
        z=[n0/d0_,n0/d1_,n1/d0_,n1/d1_];out.append((min(z),max(z)))
    return out
lam=s.Rational(1,10)
assert 1-lam*(2+lam)/(4*s.Rational(93,100))>s.Rational(47,50)
J=s.factor((Q+Qadd).subs({u:r,w:1}))
assert s.integrate(s.limit(J,l,0),(r,0,1))+4==s.Rational(4,5)
lo=hi=s.S.Zero
for a_,b_ in bounds(J.subs(l,lam)):
    lo+=min(a_,s.Rational(47,50)*a_)/256
    hi+=max(b_,s.Rational(47,50)*b_)/256
lo+=s.Rational(21,5);hi+=s.Rational(21,5)
assert lo>s.Rational(57,100)
print('PASS repaired dilation interval',float(lo),float(hi),flush=True)
q=s.Poly(Q+Qadd,u,w); B=q.coeff_monomial(w*w); C=q.coeff_monomial(u*w)/2; D=q.coeff_monomial(u*u)
jlog=8*s.pi*r*d0
eff=s.factor(D-s.diff(C,r)-jlog*C)
assert s.cancel(C.subs(r,1)+2*(l+2))==0
assert s.cancel(B.subs(r,1))==0
assert s.cancel(B-r*r*2*d0*f0/p)==0
# Boundary contribution +2(l+2)u(1)^2 cancels the mixed integration term.
# Ground-state transform with h=(log(r exp(4r²/5)))'.
h=1/r+s.Rational(8,5)*r
g=s.factor(eff-B*(s.diff(h,r)+h*h)-(s.diff(B,r)+jlog*B)*h)
lower=min(z[0] for z in bounds(g.subs(l,lam)/r**2))
assert lower>s.Rational(3,2)
print('PASS ground-state radial Hessian remainder / r² lower bound',float(lower),flush=True)
print('OPEN weighted dynamical domain, nonspherical coupled energy, nonlinear boundary evolution')
