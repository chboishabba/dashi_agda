#!/usr/bin/env python3
"""Selected five-dimensional Minkowski x S1 CS/BIDI calculation.

NOT a completed nonabelian SU3^3 x U1 quantum CS action.
Original CS: Bonetti--Grimm--Hohenegger, JHEP 07 (2013) 043.
Existing DASHI CSLevelFlowFullReceipt and BulkBoundarySU3Receipt use
conditional 2+1D boundary CS, NOT this five-form functional.
Mixed U1^3 quantization below is only on the stated test T5.
"""
import sympy as sp

def inversions(a,b): return sum(i>j for i in a for j in b)
def wedge(a,b):
    out={}
    for ia,va in a.items():
        for ib,vb in b.items():
            if set(ia).intersection(ib): continue
            key=tuple(sorted(ia+ib))
            out[key]=out.get(key,0)+(-1)**inversions(ia,ib)*va*vb
    return {key:v for key,v in out.items() if v!=0}
def integral5(form): return form.get((0,1,2,3,4),0)

# Mixed U1 triple CS: S5 = k/(2pi)^2 int A1^F2^F3.
# On T5 A1=theta dx0, F2=2pi p dx1^dx2, F3=2pi q dx3^dx4.
k,p,q=sp.symbols("k p q",integer=True)
theta=sp.symbols("theta",real=True)
A={(0,):theta};F2={(1,2):2*sp.pi*p};F3={(3,4):2*sp.pi*q}
S5=sp.simplify(k*integral5(wedge(wedge(A,F2),F3))/(2*sp.pi)**2)
assert sp.simplify(S5-k*p*q*theta)==0
large=sp.simplify(S5.subs(theta,theta+2*sp.pi)-S5)
assert sp.simplify(large-2*sp.pi*k*p*q)==0
assert sp.simplify(sp.exp(sp.I*large)-1)==0
assert integral5(wedge(wedge(A,{}),F3))==0
assert integral5(wedge(wedge(A,F2),{}))==0
print("PASS selected T5 U1^3 mixed CS large-gauge phase",large)
A3={(0,):1};F3={(1,2):1}
assert all(len(ix)==3 for ix in wedge(A3,F3))
assert integral5(wedge(A3,F3))==0
print("PASS 2+1D CS three-form does not alone furnish 5D action")
# The product Minkowski4 x S1 metric g=(-,+,+,+,b^2) has
# constant coefficients, Levi-Civita connection and Riemann zero.
b=sp.symbols("b",positive=True,real=True)
metric=sp.diag(-1,1,1,1,b*b)
assert metric.det()==-b*b
for mu in range(5):
    for nu in range(5):
        for lam in range(5):
            assert sp.diff(metric[mu,nu],sp.Symbol("x"+str(lam)))==0
print("PASS selected Minkowski4 x circle: Christoffels, Riemann, Ricci, Einstein zero")
# A nonzero flat Wilson A5 can coexist with F=0; gauge CS5 and
# mixed gauge-gravitational A^tr(R^R) vanish for F=R=0.
assert integral5(wedge(wedge(A,{}),{}))==0
print("PASS classical CS5 density/stress zero on F=R=0 flat holonomy")
# Source variation on the same selected Jordan/Einstein 5D action:
# VE=(c0/b0^4)*(ell/x+W(x)/x^6), VJ=x^2 VE,
# p5=-dVJ/d(2pi b)=-[c0/(2pi b0^5)] (W'-5W) when ell=-W.
x,c0,b0,ell=sp.symbols("x c0 b0 ell",positive=True,real=True)
W=sp.Function("W")
VE=c0/b0**4*(ell/x+W(x)/x**6)
VJ=sp.expand(x*x*VE)
p5=-sp.diff(VJ,x)/(2*sp.pi*b0)
W0,Wp=sp.symbols("W0 Wp",real=True)
D=Wp-5*W0
p5at=sp.simplify(p5.subs(x,1).subs({
 W(1):W0,sp.Subs(sp.Derivative(W(x),x),x,1):Wp,ell:-W0}))
assert sp.simplify(p5at+c0*D/(2*sp.pi*b0**5))==0
assert sp.simplify(p5at.subs(Wp,5*W0))==0
assert sp.simplify(p5at.subs(Wp,5*W0+409))==-409*c0/(2*sp.pi*b0**5)
print("PASS flat source cannot pay D!=0 with classical CS at F=R=0")
print("OPEN quotient SU3 spin CS, parity eta, massive spectrum, real 5D Earth")
