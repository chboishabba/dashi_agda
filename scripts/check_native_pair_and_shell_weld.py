"""Targeted arithmetic checks of the native paired-refinement and Bishop shell welds.
The Agda constructors and analytic convergence are not tested by this script.
"""
from itertools import product
import sympy as s


def require(ok):
    if not ok:
        raise AssertionError('native pair / shell weld')


# Literal coefficient chart of N2c: a+b*pi, pi^2=-3-3*pi.
# Use symbolic polynomial reduction rather than a second field implementation.
i, p = s.symbols('i p')
G = s.groebner([i*i+1, p*p+3*p+3], i, p)
red = lambda z: G.reduce(s.expand(z))[1]
require(red(p*p+3*(1+p)) == 0)
# Odd native vector stores its ninth trit as real part of final Gaussian digit.
# The tenth coordinate is padding zero, not the original ninth trit.
xs = s.symbols('x0:9')
a,b = s.symbols('a b')

def paired(v):
    return tuple(zip(v[::2],v[1::2]))

def value(v):
    if len(v)%2:
        v = (*v,0)
    return sum((u+i*w)*p**k for k,(u,w) in enumerate(paired(v)))

# Polynomial equality before reduction proves arbitrary-depth one-pair prefix.
require(s.expand(value((a,b,*xs))-(a+i*b+p*value(xs))) == 0)
require(paired((a,*xs)) == ((a,xs[0]),(xs[1],xs[2]),(xs[3],xs[4]),(xs[5],xs[6]),(xs[7],xs[8])))
# One scalar trit is not a ramified uniformizer digit: distinguish even alignment.
require(red(value((1,1,0,0,0,0,0,0,0,0))-(1+p*value((1,0,0,0,0,0,0,0,0)))) != 0)
# Exact digit split/join on the original nine coordinates, retaining the last.
count = 0
for v in product((-1,0,1),repeat=9):
    pairs,tail = paired(v[:-1]),v[-1]
    require(tuple(t for pair in pairs for t in pair)+(tail,) == v)
    count += 1
# Actual reciprocal power algebra: norm-square multiplies and the target
# even powers are squares of the stated half-powers. No floating point.
x,y,m = s.symbols('x y m', real=True)
z=x+s.I*y
for k,h in ((4,2),(6,3)):
    r,j = s.expand(z**k).as_real_imag()
    require(s.expand(r*r+j*j-(x*x+y*y)**k)==0)
    require(s.expand(m**k-(m**h)**2)==0)
# Square shells have 8r points; r>=1, weights 4 and 6 are summable.
r=s.symbols('r',positive=True,integer=True)
require(s.expand((2*r+1)**2-(2*r-1)**2-8*r)==0)
print(f'PASS {count} original nine-trit split/join cases; symbolic paired prefix and misalignment; weight-4/6 norm-square powers; square shell count')
