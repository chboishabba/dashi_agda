"""Four reference-field realization of conserved prescribed F8 stress at linear order.
Designer action, not independently specified apparatus or nonlinear solution.
"""
import sympy as s
b=s.symbols('b',positive=True); a=1/b; beta=s.sqrt(1+b*b)
rho=beta-1; p=-rho+b*b/(3*beta); K=rho+p; lam=(rho-p)/2
H=s.Matrix([[0,0,0],[0,1,2],[0,2,-1]])
P=s.Matrix([[1,2,3],[2,-2,4],[3,4,1]])
e=s.symbols('e'); I=s.eye(3)
g=s.diag(-1,a*a*(I+e*H)); gi=s.diag(-1,b*b*(I-e*H))
T=s.diag(rho,a*a*(p*(I+e*H)+e*P))
gamma=T+lam*g; V=-p
tr=lambda A:s.expand(s.trace(A))
assert s.simplify(tr(gi*gamma).subs(e,0)-K)==0
assert s.simplify(s.diff(tr(gi*gamma),e).subs(e,0))==0
# Hilbert stress; both covariant and mixed, preserve full 4x4 tensor.
S=gamma-g*(tr(gi*gamma)/2+V)
for order in (0,1):
 assert (S-T).diff(e,order).subs(e,0).applyfunc(s.simplify)==s.zeros(4)
 assert (gi*S-s.diag(-rho,p*I+e*P)).diff(e,order).subs(e,0).applyfunc(s.simplify)==s.zeros(4)
assert s.simplify(gamma[0,0]-K/2)==0
assert s.simplify(V-(beta-1)*(2*beta-1)/(3*beta))==0
assert s.simplify(b*s.diff(rho,b)-3*K)==0
# Momentum/energy coupling of linear TT stress to isotropic background.
assert s.trace(H)==0 and s.trace(P)==0
# Maxwell triad reverse-source compatibility, eta and q independent.
eta=s.symbols('eta',real=True); q,E=s.symbols('q E',positive=True)
h=s.Function('h')(eta); pi=s.Function('pi')(eta); U=s.Function('U')(eta)
# b=e^-eta, P=pi/b^4. Required U'=E h/2 - P/(2E).
Pscaled=pi*s.exp(4*eta); up=E*h/2-Pscaled/(2*E)
# Maxwell U''+q U=E h' -> residual U''-E h'+q U.
res=s.diff(up,eta)-E*s.diff(h,eta)+q*U
compat=s.diff(up,eta,2)-E*s.diff(h,eta,2)+q*up
assert s.simplify(s.diff(res,eta).subs(s.diff(U,eta),up)-compat)==0
assert s.simplify(2*E*compat-(E**2*(-s.diff(h,eta,2)+q*h)-s.diff(Pscaled,eta,2)-q*Pscaled))==0
print(s.__version__, '12 exact assertions PASS')
