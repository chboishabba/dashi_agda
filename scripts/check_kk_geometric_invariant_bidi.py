import sympy as s
n,F,U=s.symbols('n F U', positive=True)
# toroidal Einstein-frame log radius metric I+11^T/2
for N in range(1,13):
    e=s.ones(N,1); G=s.eye(N)+e*e.T/2
    assert G.inv()==s.eye(N)-e*e.T/(N+2)
    q=e/2
    assert (q.T*G.inv()*q)[0]==s.Rational(N,2*(N+2))
    v=s.eye(N)[:,0]+q
    assert (v.T*G.inv()*v)[0]==s.Rational(3,2)
    # pure reparameterization invariant
    A=s.eye(N)*3+e*e.T
    assert (q.T*G.inv()*q)[0]==((A.T*q).T*(A.T*G*A).inv()*(A.T*q))[0]
print('PASS 12 torus dimensions, inverse metric, universal and pure momentum charges, congruence')
print('general charge norm = n/(2(n+2))+2F/(n+2)+U-F^2/(n+2)')
B,S,d,X=s.symbols('B S d X', positive=True)
E=S*X**2/2+(S+d)*X**2/2-S*X**2-B*X
assert s.simplify(E-(d*X**2/2-B*X))==0
assert s.simplify(E.subs(X,B/d)+B**2/(2*d))==0
assert s.simplify(s.diff(-B**2/(2*d),d)-B**2/(2*d**2))==0
print('PASS full equilibrium ledger and reversible tuning work')
G=6.67430e-11; g=9.80665; a=.1
E0=g*g*a**3/(2*G)
print('10 cm canonical ball energy',E0,'J; ratio needed for 2073 J field-only budget',E0/2073)
