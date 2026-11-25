"""Exact arithmetic regression of native Horner multiplication and Bishop shell bounds.
Not an Agda typecheck or analytic convergence proof.
"""
from itertools import product
from fractions import Fraction as F
import sympy as s


def require(ok):
    if not ok:
        raise AssertionError('tower/shell fold')


def add(a, b):
    out, carry = [], 0
    for x, y in zip(a, b):
        q = x + y + carry
        d = (q + 1) % 3 - 1
        out.append(d)
        carry = (q - d) // 3
    return tuple(out)


def scale(d, a):
    return tuple(d*x for x in a)


def mul(a, b):
    if not a:
        return ()
    return add(scale(a[0], b), (0,) + mul(a[1:], b[:-1]))


def value(a):
    return sum(d*3**j for j, d in enumerate(a))


checks = 0
for n in range(1, 5):
    xs = list(product((-1,0,1), repeat=n))
    for a, b in product(xs, repeat=2):
        p = mul(a,b)
        require((value(p)-value(a)*value(b)) % 3**n == 0)
        require(p[:-1] == mul(a[:-1],b[:-1]))
        checks += 1
# Exact ramified coefficient step and product in the original polynomial quotient.
i, pi, a, b, c, d, r = s.symbols('i pi a b c d r')
G = s.groebner([i*i+1, pi*pi+3*pi+3], pi, i)
# Reduce in pi only (symbolic coefficient variables).
red = lambda e: s.rem(s.expand(e), pi*pi+3*pi+3, pi).expand()
require(red((a+b*pi)*(c+d*pi) - ((a*c-3*b*d)+(a*d+b*c-3*b*d)*pi)) == 0)
require(red(r+pi*(a+b*pi)-((r-3*b)+(a-3*b)*pi)) == 0)
# Verify the selected source square-shell guard and arithmetic majorant.
# Rational upper-half-plane points; sum absolute real and imaginary terms.
# Use exact Gaussian rational inverse powers, not a new analytic source.
def cmul(z,w):
    return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])


def cpow(z,k):
    w=(F(1),F(0))
    for _ in range(k):
        w=cmul(w,z)
    return w


shell_checks=0
for x,y in [(F(0),F(1)),(F(1,2),F(3,4)),(F(-5,3),F(1,3))]:
    K=(1+x*x+y*y)/(y*y)
    for r0 in range(1,9):
        shell=[(m,n) for m in range(-r0,r0+1) for n in range(-r0,r0+1) if max(abs(m),abs(n))==r0]
        require(len(shell)==8*r0 and (0,0) not in shell)
        M=K/r0**2
        for k,h in [(4,2),(6,3)]:
            terms=[]
            for m,n in shell:
                u,v=m*x+n,m*y
                q=u*u+v*v
                terms.append(cpow((u/q,-v/q),k))
            for j in (0,1):
                actual=sum(abs(z[j]) for z in terms)
                require(actual<=len(shell)*M**h<=(2*r0+1)**2*M**h<=9*K**h/r0**2)
                shell_checks+=1
print(f'PASS {checks} native multiplication/reduction pairs; symbolic ramified product and prefix; {shell_checks} exact component shell and Basel majorant checks')
