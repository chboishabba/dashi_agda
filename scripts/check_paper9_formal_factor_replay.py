from sympy import symbols, diff, expand, Rational, __version__
x,y,e,f,f1,f2,f3=symbols('x y e f f1 f2 f3')
flow={x:(e*x-y)/3,y:(e*y-x*x)/2,e:(e*e-x)/12,f:f1,f1:f2,f2:f3}
def D(p): return expand(sum(diff(p,k)*v for k,v in flow.items()))
u=D(x);w=D(y);d=x**3-y*y;A=y*u-x*w;B=y*D(A)-2*A*w
P3=72*x**3*y*y;P2=108*x*x*y*(2*A-d);P1=72*x*(A*A+x*B)-108*x*d*A-46*x*y*y*d;P0=-5*y**3*d
r=e*x-y;Q2=36*x*x*y*y;Q1=-36*x*y*y*r;Q0=Rational(15,2)*y*y*(r*r-d)
S=2*x*D(f)-D(x)*f
left=P3*f3+P2*f2+P1*f1+P0*f
right=Q2*D(D(S))+Q1*D(S)+Q0*S
assert expand(left-right)==0
assert expand(D(S)-(2*x*f2+u*f1-D(u)*f))==0
assert expand(D(D(S))-(2*x*f3+3*u*f2-D(D(u))*f))==0
assert expand(x*D(f*f-x)-u*(f*f-x)-f*S)==0
print('SymPy',__version__,': 4/4 exact symbolic operator, differentiated defect and square-defect checks PASS')
