from fractions import Fraction as F
from itertools import product
from collections import Counter
from sympy import Poly, symbols, cyclotomic_poly, Matrix, eye

# pi^2=3*pi-3, O_K/pi^4=O_K/9.
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def mul(x,y):
    a,b=x;c,d=y
    return (a*c-3*b*d,a*d+b*c+3*b*d)
def pw(x,n):
    r=(1,0)
    for _ in range(n): r=mul(r,x)
    return r
def red(x): return tuple(a%9 for a in x)
def rm(x,y): return red(mul(x,y))
one=(1,0); pi=(0,1); zeta=(1,-1); c=(3,-2)
assert mul(zeta,pi)==c
ring=list(product(range(9),repeat=2))
units={x for x in ring if x[0]%3}
# Norm of 1+w^j, w^3=c. Independent determinant in K[w].
z=symbols('z'); W=Matrix([[0,0,z],[1,0,0],[0,1,0]])
gens=[(8,0)]
for j in range(1,12):
    n=red(pw(add(one,pw(c,j//3)),3) if j%3==0 else add(one,pw(c,j)))
    poly=Poly((eye(3)+W**j).det(),z)
    acc=(0,0)
    for (k,),v in poly.terms(): acc=add(acc,mul((int(v),0),pw(c,k)))
    assert red(acc)==n
    gens.append(n)
H={one}
for g in gens:
    H={rm(h,p) for h in H for p in [red(pw(g,j)) for j in range(54)]}
assert len(units)==54 and len(H)==18
v=red(add(one,pw(pi,3)))
assert v not in H
chi={rm(h,red(pw(v,j))):j for h in H for j in range(3)}
assert set(chi)==units and {u for u in units if chi[u]==0}==H
for a,b in product(units,repeat=2): assert chi[rm(a,b)]==(chi[a]+chi[b])%3
p=-chi[red(zeta)]%3
assert p==0
for j in range(1,5):
    U={red(add(one,mul(pw(pi,j),x))) for x in ring}
    assert len(U)==3**(4-j)
    assert {chi[x] for x in U}==({0,1,2} if j<4 else {0})
for a,b in units:
    assert chi[red((a+3*b,-b))]==-chi[a,b]%3
# psi_K=psi_Q3 composed trace; c_eps=pi^5.
inverse=pw((F(1),F(-1,3)),5)
def phase(u):
    a,b=mul(u,inverse); tr=2*a+3*b
    assert (9*tr).denominator==1
    return int(9*tr)%9
# Additive pairing on O_K/9 is nondegenerate, and lifts are independent.
assert len({tuple(phase(mul(x,y)) for y in [(1,0),(0,1)]) for x in ring})==81
for a,b in ring:
    assert phase((a+9,b))==phase((a,b+9))==phase((a,b))
T=symbols('T'); cycl=Poly(cyclotomic_poly(9,T),T)
for sign in (1,-1):
    ex=[(phase(u)-3*sign*chi[u]+3*sign*5*p)%9 for u in units]
    gauss=Poly(sum(T**e for e in ex),T)%cycl
    assert gauss==Poly(9,T)
    print('orientation',sign,'exponents',sorted(Counter(ex).items()),'Gauss',gauss.as_expr())
# Q3 quadratic sign: norm of pi is 3; residue character is Legendre mod 3.
# (zeta_3-zeta_3^2)^2=-3; normalized lambda=i for positive psi.
cycl3=Poly(T*T+T+1,T)
assert Poly((T-T*T)**2,T)%cycl3==Poly(-3,T)
print('PASS: 11 norm determinants, 2916 character products, 4 conductor strata, 54 conjugations, 81 additive characters and lifts, 2 wild Gauss sums, quadratic lambda')
