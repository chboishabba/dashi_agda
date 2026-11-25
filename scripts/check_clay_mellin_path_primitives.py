"""Exact compact polynomial controls for the Mellin primitive theorem.
These are signed-density fixtures, not elliptic L-functions or rank proofs.
"""
import sympy as s
from fractions import Fraction as Q

u, v = s.symbols('u v', real=True)
checks = 0

def check(ok):
    global checks
    if not ok:
        raise AssertionError('exact control failed')
    checks += 1

def integral(p):
    p = s.Poly(p, u)
    return sum(c * s.Rational(2, j[0]+1) for j,c in p.terms() if j[0]%2 == 0)

for m in range(9):
    B = s.expand((1-u*u)**(m+2))
    H = (-1)**m*s.diff(B,u,m)
    check(s.expand(H.subs(u,-u)-(-1)**m*H)==0)
    for j in range(m):
        check(integral(u**j*H)==0)
    check(integral(u**m*H)==s.factorial(m)*integral(B)>0)
    T=H
    for k in range(1,m+1):
        # Right-tail primitive on [-1,1], zero outside under lower moments.
        p=s.integrate(T,u)
        U=s.expand(p.subs(u,1)-p)
        expected=(-1)**(m-k)*s.diff(B,u,m-k)
        check(s.expand(U-expected)==0)
        check(U.subs(u,-1)==U.subs(u,1)==0)
        check(s.expand(U.subs(u,-u)-(-1)**(m-k)*U)==0)
        for j in range(5):
            check(integral(u**(j+k)*H)==s.factorial(j+k)/s.factorial(j)*integral(u**j*U))
        T=U
    check(s.expand(T-B)==0)
    # First unpaid moment makes the next tail primitive nonzero at left.
    p=s.integrate(T,u)
    check(p.subs(u,1)-p.subs(u,-1)==integral(B)>0)

# Universal eventual positivity: |a_n|<=2n, q<=1/8.
q=Q(1,8)
check(1-2*(1/(1-q)**2-1)==Q(19,49)>0)
# A period-lattice endpoint forgets an arbitrary winding integer.
for a in range(-8,9):
    for b in range(-8,9):
        x=Q(1,3)+a; y=Q(1,3)+b
        check(x%1==y%1 and (x==y)==(a==b))
print(f'{checks}/{checks} exact checks PASS')
