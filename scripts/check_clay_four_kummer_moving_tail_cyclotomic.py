"""Finite exact source controls; not zeta, Selmer, PDE or Chow proof."""
from fractions import Fraction as Q
from itertools import product, permutations
import sympy as S


def need(b):
    if not b:
        raise ArithmeticError('regression failed')

# RH: square-channel change of variables in triangular integral (t>1).
x,t=S.symbols('x t', real=True)
I=S.integrate(1+2*x-t,(x,(t-1)/2,t/2))+S.integrate(1-2*x+t,(x,t/2,(t+1)/2))
need(S.simplify(I)==Q(1,2))
for j in range(-100,101):
    y=Q(j,50)
    need(max(0,1-abs(y))==max(0,y+1)-2*max(0,y)+max(0,y-1))
print('RH 201 tent identities, square channel mass 1/2')

# BSD: actual S3 coefficient cocycle and Kummer local cube tests.
G=list(permutations(range(3))); e=G[0]; a=(1,2,0); b=(0,2,1)
def mul(g,h): return tuple(g[h[i]] for i in range(3))
# Label cube roots by j in F3: a translates, b negates. j=0 chosen cube root.
sign=lambda g: 1 if sum(g[i]>g[j] for i in range(3) for j in range(i+1,3))%2==0 else -1
c=lambda g:g[0]
for g,h in product(G,repeat=2):
    need((c(mul(g,h))-c(g)-sign(g)*c(h))%3==0)
need(c(a)==1 and c(b)==0)
need(not any(all((c(g)-(sign(g)-1)*u)%3==0 for g in G) for u in range(3)))
need({x**3%9 for x in range(9) if x%3}=={1,8})
# Away from 2,3 Hensel: 2 cube iff residue cube.
classes=[]
for p in list(S.primerange(5,100)):
    roots=[j for j in range(p) if j**3%p==2]
    if p%3==2: need(len(roots)==1)
    else: need(len(roots)==(3 if pow(2,(p-1)//3,p)==1 else 0))
    classes.append((p,len(roots)))
print('BSD 36 cocycle checks; nontrivial class; 23 good-prime cube root counts',classes)

# NS: moving-cutoff scalar inequalities; dyadic weight exact controls.
# A highest active shell j means 2^j E_j>delta^2, so D>=delta^2*2^j.
for J in range(1,41):
    lam=2**J; delta=Q(1,7)
    energy=[Q(1,2**(2*j+1)) for j in range(J+1)]
    energy[J]=2*delta**2/lam
    D=sum(2**(2*j)*v for j,v in enumerate(energy))
    need(D>=delta**2*lam)
    need(sum(Q(2**(2*j),lam**2) for j in range(J+1))<Q(4,3))
print('NS 80 exact moving-cutoff and geometric sum controls')

# Hodge: actual conductor-7 determinant square-class arithmetic, not cycle proof.
x,y=S.symbols('x y'); f=x**3+x**2-2*x-1
red=lambda p:S.rem(S.expand(p),f,x)
pi=2-x; u=x*x+x-1
need(red(u*u-(x+2))==0)
need(red(-pi*u*u-(x*x-4))==0)
need(S.resultant(f,pi,x)==7)
need(red((7+x+3*x*x)**2+pi-16*(3+x+4*x*x))==0)
# root z=(theta+u*j)/2 with j^2=-pi; exact tower reductions.
def tower(p): return red(S.rem(S.expand(p),y*y+pi,y))
z=(x+u*y)/2; zi=(x-u*y)/2
need(tower(z*zi)==1 and tower(z+zi)==x)
need(tower(z**7)==1 and tower(z-1)!=0)
need(tower(sum(z**k for k in range(7)))==0)
need(tower(z-zi-u*y)==0)
# Three conjugate reciprocal quadratic factors multiply to Phi_7.
need(S.expand(S.resultant(f,y*y-x*y+1,x)-S.cyclotomic_poly(7,y))==0)
print('Hodge norm, square class, dyadic certificate and cyclotomic forward/reverse identities PASS')
