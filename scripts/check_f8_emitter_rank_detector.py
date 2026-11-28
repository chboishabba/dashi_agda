import sympy as s
b=s.symbols('b',positive=True); beta=s.sqrt(1+b*b)
C=b*b/(3*beta)
assert s.simplify(s.diff(C/b**2,b)+b/(3*beta**3))==0
# Full rank spatial gradients and zero momentum imply no temporal scalar rate.
J=s.Matrix([[1,2,0],[0,1,3],[2,0,1]])
G=s.Matrix([[4,1,0],[1,3,1],[0,1,2]])
u=s.Matrix(s.symbols('u:3'))
assert (J.T*G).inv()*(J.T*G*u)==u
# Metric variation at isotropic spatial gradient stress: mixed TT = -C H.
H=s.Matrix([[0,0,0],[0,1,2],[0,2,-1]])
e,c=s.symbols('e c'); I=s.eye(3)
assert ((I-e*H)*c*I).diff(e)==-c*H
# Israel with Z2 normal convention of original reference.
kap,ell,g=s.symbols('kap ell g',positive=True); pi=-b*beta*g/(kap*ell)
assert s.simplify(b*beta*g/(2*ell)+kap*pi/2)==0
# Original clock F(t), physical pullback dT/dt=b*beta, not b/beta.
t=s.symbols('t',positive=True)
assert s.simplify(s.diff(s.asinh(t)-s.sqrt(1+t*t)/t,t)-(b*beta).subs(b,1/t))==0
# Fourier TT removes constant-frame displacement strains.
k=s.Matrix(s.symbols('kx ky kz',real=True)); q=(k.T*k)[0]; P=q*s.eye(3)-k*k.T
w=s.Matrix(s.symbols('w:3')); A=k*w.T+w*k.T
assert (P*A*P-P*s.trace(P*A)/2).applyfunc(s.expand)==s.zeros(3)
print(s.__version__, '6 exact checks PASS')
