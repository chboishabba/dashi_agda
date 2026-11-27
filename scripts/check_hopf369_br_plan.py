"""BR planning controls: reduced shell constraint and periodic DtN; no PDE solve."""
import sympy as s
j,c,k,a=s.symbols('j c k a',real=True)
assert s.expand((4*j*c+6*j*k).subs(k,-a*c)-(4-6*a)*j*c)==0
# Flat adapted linearized contracted Christoffel and wall trace.
div,hn,qn,Hn,boxf=s.symbols('div hn qn Hn boxf')
Cn=div+qn/2-hn/2-Hn
kap=-boxf+hn/2-div
assert s.expand(kap+Cn-(-boxf+qn/2-Hn))==0
# Exact cut interval constant-coefficient DtN, with signed endpoint jump d.
y,L,l=s.symbols('y L l',positive=True); m,d=s.symbols('m d')
v=m*s.cosh(l*(y-L/2))/s.cosh(l*L/2)-d*s.sinh(l*(y-L/2))/(2*s.sinh(l*L/2))
assert s.simplify(s.diff(v,y,2)-l*l*v)==0
assert s.simplify(v.subs(y,0)-v.subs(y,L)-d)==0
assert s.simplify((v.subs(y,0)+v.subs(y,L))/2-m)==0
p=s.diff(v,y); assert s.simplify((p.subs(y,0)+p.subs(y,L))/2+l*s.coth(l*L/2)*d/2)==0
assert s.simplify(p.subs(y,0)-p.subs(y,L)+2*l*s.tanh(l*L/2)*m)==0
assert s.limit(l*s.coth(l*L/2),l,0)==2/L
assert s.limit(l*s.tanh(l*L/2),l,0)==0
# Mean/jump energy identity, no positivity inference.
u0,u1,p0,p1=s.symbols('u0 u1 p0 p1'); assert s.expand(u0*p0-u1*p1-(u0+u1)*(p0-p1)/2-(u0-u1)*(p0+p1)/2)==0
# Conformal-jump normal channel in a simplified frozen half-space model.
f=s.symbols('f'); mean=-l*(-2*j*f)/2
assert s.expand(l*l*f+mean/2-l*(l+j/2)*f)==0
print('PASS 11 symbolic reduced-wall, periodic DtN, zero-mode, flux and frozen model controls')
