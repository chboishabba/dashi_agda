"""Exact finite controls; not a native kernel, general Selmer solver, PDE or Chow computation."""
from itertools import permutations, product
from fractions import Fraction as Q
import sympy as S


def need(ok):
    if not ok:
        raise ArithmeticError('exact control failed')

# BSD: actual cubic point and principal-divisor norm, then actual finite group.
x = S.symbols('x')
f = x**3 - 6*x + 10
h = x*x + 2*x - 2
need(S.expand(h*h-f) == S.expand((x**3-2)*(x+3)))
need(h.subs(x,-3)==1 and f.subs(x,-3)==1)
disc = -16*(4*(-6)**3+27*10**2)
need(disc != 0 and disc % 7 != 0)
p = 7
pts = [None]+[(a,b) for a,b in product(range(p),repeat=2) if (b*b-a**3+6*a-10)%p==0]
def add(P,R):
    if P is None: return R
    if R is None: return P
    a,b=P; c,d=R
    if a==c and (b+d)%p==0: return None
    m=((d-b)*pow(c-a,-1,p) if a!=c else (3*a*a-6)*pow(2*b,-1,p))%p
    e=(m*m-a-c)%p
    return e,(m*(a-e)-b)%p
three={add(add(P,P),P) for P in pts}
need(len(pts)==6 and len(three)==2 and (4,6) in pts and (4,6) not in three)
for P,R,T in product(pts,repeat=3):
    need(add(add(P,R),T)==add(P,add(R,T)))
print('BSD: discriminant',disc,'E(F7)',pts,'3E(F7)',sorted(map(str,three)),'216 associativity controls')

# NS: exact weighted Cauchy-Schwarz controls for a finite positive pair majorant.
# This is only a discrete check of the inequality, not an HLS/PDE test.
vecs=list(product(range(3),repeat=3))
checks=0
for w,k in product(vecs,repeat=2):
    for j in ((1,1,1),(1,2,3),(0,1,2)):
        lhs=sum(a*a*b*c for a,b,c in zip(w,k,j))
        rhs=sum(a*a*b*b for a,b in zip(w,k))*sum(a*a*c*c for a,c in zip(w,j))
        need(lhs*lhs<=rhs)
        checks+=1
print('NS:',checks,'weighted Cauchy-Schwarz controls')

# RH: exact Laurent polynomial mean-square control with repeated signed frequencies.
# Integration over a rational common period picks the constant term.
checks=0
for w in product(range(3),repeat=4):
    if not any(w): continue
    mass={}
    for f,a in zip((-2,2,-2,2),w): mass[f]=mass.get(f,0)+a
    second=sum(a*b for f,a in mass.items() for g,b in mass.items() if f+g==0)
    need(second==2*mass[-2]*mass[2])
    # General symmetric weights have mean-square equal to sum of squares.
    if mass[-2]==mass[2]: need(second==sum(a*a for a in mass.values()))
    checks+=1
print('RH:',checks,'finite repeated-frequency controls')

# Hodge: actual Clifford multiplication in an eight-dimensional split-test fixture.
# q=diag(1,...,1), e_i^2=1. Use six slots and right factor e_7.
def mul(a,b):
    s=1
    for i in range(8):
        if a>>i&1:
            if (b&((1<<i)-1)).bit_count()%2: s=-s
    return s,a^b
basis=[a for a in range(256) if a.bit_count()%2==0]
vol=(1<<6)-1
need(mul(vol,vol)==(-1,0))
for a in basis:
    # L_vol commutes with even monomials internal to either orthogonal block.
    if (a&vol).bit_count()%2==0:
        need(mul(vol,a)==mul(a,vol))

def apply_h(i,a):
    s,b=mul(1<<i,a); t,c=mul(b,1<<6)
    return s*t,c

def parity(p):
    return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
alt=0
for perm in permutations(range(6)):
    tr=0
    for a in basis:
        s,b=1,a
        for i in reversed(perm):
            t,b=apply_h(i,b);s*=t
        t,b=mul(vol,b);s*=-t # left volume inverse
        need(b==a)
        tr+=s
    need(tr==parity(perm)*len(basis))
    alt+=parity(perm)*tr
need(alt==720*len(basis)==92160)
# ordinary trace without volume insertion vanishes for the ordered word.
for a in basis:
    b=a
    for i in reversed(range(6)):
        _,b=apply_h(i,b)
    need(b!=a)
print('Hodge: 720 ordered traces on 128 even basis states; inserted alternating trace',alt)
