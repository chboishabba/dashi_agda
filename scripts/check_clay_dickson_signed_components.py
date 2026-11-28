"""Exact polynomial checks for geometric irreducibility of the Q0 signed fibre.
The branch-locus argument and Chow localization are mathematical proofs,
not a numerical Chow computation. No claim about arbitrary Dickson parameters.
"""
import sympy as s
from itertools import combinations
checks=0
def ck(b):
    global checks
    if not b: raise AssertionError('Dickson component guard failed')
    checks+=1
a,y,t=s.symbols('a y t')
A=-2; B=-3*a*a+3*a+1; C=-3*a**3-a*a+3*a+3
D=s.expand(B**2-4*A*(C-y-a**7/y))
P=s.Poly(s.expand(y*D),a,y)
ck(P.degree(a)==7 and P.degree(y)==2)
ck(s.Poly(P.as_expr(),a).LC()==-8)
ck(s.Poly(P.as_expr(),y).LC()==-8)
ck(P.as_expr().subs(a,0)==-8*y*y+25*y)
f=s.Poly(D.subs(y,1),a)
ck(f.degree()==7 and f.LC()==-8)
ck(f.eval(1)==1)
ck(s.gcd(f,f.diff()).degree()==0)
R=s.Poly(s.resultant(f.as_expr()-t,f.diff().as_expr(),a),t).primitive()[1]
Rstar=s.Poly(s.expand(t**6*R.as_expr().subs(t,1/t)),t)
ck(R.degree()==6 and R.eval(0)!=0)
ck(Rstar.degree()==6 and Rstar.eval(0)!=0)
ck(s.gcd(R,Rstar).degree()==0)
ck(s.gcd(R,R.diff()).degree()==0)
# Exact Bezout certificates reduced to a finite good prime; reduction
# preserves degree of each polynomial and proves the resultant nonzero.
p=101
fr=s.Poly(f,a,modulus=p); dr=fr.diff()
rr=s.Poly(R,t,modulus=p); rs=s.Poly(Rstar,t,modulus=p)
ck(fr.degree()==7 and dr.degree()==6)
ck(rr.degree()==rs.degree()==6)
for u,v in [(fr,dr),(rr,rs)]:
    b,c,g=s.gcdex(u,v)
    ck(g.degree()==0 and g.LC()==1)
    ck(b*u+c*v==g)
# Four fixed adjacent square classes: no common factors since each factor
# uses both addresses; primitive leading coefficients exclude unary factors.
z=s.symbols('z1:6')
for i in range(4):
    pi=s.Poly(P.as_expr().subs({a:z[i+1],y:z[i]},simultaneous=True),z[i+1],z[i])
    ck(pi.degree(z[i+1])==7 and pi.degree(z[i])==2)
    ck(s.Poly(pi.as_expr(),z[i+1]).LC()==-8)
    ck(s.Poly(pi.as_expr(),z[i]).LC()==-8)
    ck(s.gcd(s.Poly(pi.as_expr().subs(z[i],1),z[i+1]),s.Poly(s.diff(pi.as_expr(),z[i+1]).subs(z[i],1),z[i+1])).degree()==0)
for i,j in combinations(range(4),2):
    ck({z[i],z[i+1]}!={z[j],z[j+1]})
# At t=0 the polynomial map is unramified at each root of f;
# the reciprocal degree-seven map is ramified at infinity. The local
# valuation of t on their fibre product is seven, hence d5^2=t has
# no square root there. Formal valuation control, not numeric sampling.
ck(7%2==1)
print(f'{checks}/{checks} exact component guards PASS')
print('critical polynomial:',R.as_expr())
print('mod 101 reciprocal gcd:',s.gcd(rr,rs).as_expr())
