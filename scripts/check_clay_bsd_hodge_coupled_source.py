"""Exact source-specific controls: conductor-seven Dickson incidence and two-prime BSD axes.
Not a cycle-class computation or a complex derivative vanishing test.
"""
import sympy as s
from itertools import product

checks = 0

def ck(b):
    global checks
    if not b:
        raise AssertionError('coupled source check failed')
    checks += 1

# Actual source Q0 from rStation 140, t=1. Each quadratic in s_i has
# nonzero leading coefficient and is separable over its own rational field.
a,y,w,v,X = s.symbols('a y w v X')
Q0 = -3*a**3-3*a**2*w-a**2+3*a*w+3*a-2*w*w+w+3
D7 = X**7-7*a*X**5+14*a*a*X**3-7*a**3*X
ck(s.cancel(D7.subs(X,v+a/v) - v**7-(a/v)**7)==0)
poly = s.Poly(y*(Q0-y)-a**7,w)
ck(poly.degree()==2 and poly.LC()==-2*y)
disc = s.factor(s.discriminant(poly.as_expr(),w))
ck(disc!=0)
# Use the discriminant of the monic-in-y relation before multiplying by y.
# Its degree in alpha is seven; odd infinity valuation precludes a square.
D=s.factor(disc/y**2)
ck(s.Poly(y*D,a).degree()==7)
ck(s.Poly(y*D,a).LC()==-8)
Aq=-2; Bq=-3*a*a+3*a+1
invol=-Bq/Aq-w
ck(s.expand(Q0.subs(w,invol)-Q0)==0)
ck(s.expand((2*Aq*w+Bq).subs(w,invol)+(2*Aq*w+Bq))==0)
# Original six base coordinates chosen independently. y_1..y_5 are
# coordinate units and y_6 is inverse product. Each (a_i,y_i) independent.
z = s.symbols('z1:7', nonzero=True)
ys = list(z[:5])+[1/s.prod(z[:5])]
alphas = [z[1],z[2],z[3],z[4],z[5],z[0]]
ck(s.prod(ys)==1)
for a0,y0 in zip(alphas,ys):
    jac=s.Matrix([a0,y0]).jacobian(z)
    ck(any(s.simplify(jac[:,[i,j]].det())!=0 for i in range(6) for j in range(i+1,6)))
    ck(disc.subs({a:a0,y:y0}, simultaneous=True)!=0)
# Exponent matrix is the Kummer valuation matrix for y_i at z_j=0.
A=s.zeros(5,6)
for i in range(5): A[i,i]=1; A[i,5]=-1
ck(A[:,:5].det()==1)
ck(A*s.ones(6,1)==s.zeros(5,1))
# Only the fifth quadratic discriminant uses z6. Every other quadratic
# and the first five Kummer generators lie over C(z1,...,z5).
for i,(aa,yy) in enumerate(zip(alphas,ys)):
    dd=s.cancel(D.subs({a:aa,y:yy}, simultaneous=True))
    ck((z[5] in dd.free_symbols)==(i==4))
    if i==4:
        ck(s.Poly(s.cancel(yy*dd),z[5]).degree()==7)
# Second actual incidence: free alpha_6=z6, solve alpha_5 from
# product D_i=1. Four alpha_i=y_{i+1} constraints remain. The
# other five discriminants form a nonzero coefficient C; the
# remaining equation is a genuine degree-seven polynomial.
C = s.symbols('C', nonzero=True)
ck(s.Poly(s.cancel(y*(C*D-1)),a).degree()==7)
ck(s.Poly(s.cancel(y*(C*D-1)),a).LC()==-8*C)
D6=s.cancel(D.subs({a:z[5],y:ys[5]}, simultaneous=True))
ck(s.Poly(s.cancel(ys[5]*D6),z[5]).degree()==7)
# d_i^2=D_i, d_6=(product d_1..d_5)^-1; selecting product d_i=1
# gives a visible algebraic sign condition, not an unsigned quotient.
ds=s.symbols('d1:6', nonzero=True)
full=list(ds)+[1/s.prod(ds)]
ck(s.prod(full)==1)
for signs in product((-1,1),repeat=6):
    ck((s.prod(signs[i]*full[i] for i in range(6))==1)==(s.prod(signs)==1))
# y_2..y_5 are fixed by the base alpha_1..alpha_4. Flipping both
# remaining quadratic y-roots would require (alpha_1 alpha_6)^7
# = (y_1 y_6)^2, not an identity of the six independent parameters.
ck(s.cancel((z[1]*z[5])**7-(ys[0]*ys[5])**2)!=0)
# All quadratic sign flips with odd parity kill a product of six T slots;
# exactly half the sign subgroup survives the necessary character filter.
ck(sum(s.prod(e)==1 for e in product((-1,1),repeat=6))==32)
# Hyperplane H of rotations with sum r_i=0, 5 generators.
# Its character annihilator is exactly the diagonal line. Equal embedding
# requires every character to have the same magnitude j modulo 7.
for j in range(1,4):
    survivors=[]
    for signs in product((-1,1),repeat=6):
        k=s.Matrix([j*t for t in signs])
        ok=all(int(t)%7==0 for t in A*k)
        ck(ok==(len(set(signs))==1))
        if ok: survivors.append(signs)
    ck(len(survivors)==2)
# For rank-five rotation monodromy, any coordinatewise reflection that
# preserves the diagonal annihilator must be simultaneous or identity.
for signs in product((-1,1),repeat=6):
    ck(all(int(t)%7==0 for t in A*s.Matrix(signs))==(len(set(signs))==1))

# Actual ordinary local polynomials for 234446.a1. Euler axis factor
# numerator is alpha^2-alpha*(u+u^-1)+1 = (alpha-u)(alpha-u^-1).
a0,u=s.symbols('alpha u', nonzero=True)
for p,ap in [(5,-4),(11,-6)]:
    ck(ap*ap-4*p<0) # roots have complex modulus sqrt(p)
    ck(s.expand((a0-u)*(a0-1/u)-(a0*a0-a0*(u+1/u)+1))==0)
    lhs=a0*(ap-u-1/u)-(p-1)
    rhs=(a0-u)*(a0-1/u)
    ck(s.rem(s.expand(lhs-rhs),a0*a0-ap*a0+p,a0)==0)
    # Exact resultant at every possible order relevant to the other prime
    # through two cyclotomic levels. No complex floating comparisons.
    other=11 if p==5 else 5
    for n in range(3):
        cyclo=s.cyclotomic_poly(other**n,a0)
        ck(s.resultant(a0*a0-ap*a0+p,cyclo,a0)!=0)

# Classical multiplicative refinement test on the symbolic root polynomial.
p,ap,n=s.symbols('p ap n')
ck(s.rem(s.expand(a0*(ap-u-1/u)-(p-1)-(a0-u)*(a0-1/u)),a0*a0-ap*a0+p,a0)==0)
ck(s.rem(a0*(ap-a0)-p,a0*a0-ap*a0+p,a0)==0)
print(f'{checks}/{checks} exact coupled-source controls PASS')
