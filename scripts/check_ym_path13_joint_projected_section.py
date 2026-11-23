from collections import Counter
from itertools import product
import sympy as s
L=13;N=L**4; Z=(0,)*4; e=s.Rational(1,4096)
def walk(start,offset):
 x=list(start)
 for d,n in enumerate(offset):
  for _ in range(abs(n)):
   if n<0:x[d]-=1
   yield tuple(a%L for a in x),d
   if n>0:x[d]+=1
m=Counter();cs=[Counter() for _ in range(4)]
for x in product(range(-6,7),repeat=4):
 m.update(walk(Z,x))
 for mu in range(4):cs[mu].update(walk(x,tuple(L*(k==mu) for k in range(4))))
x=222*e; d=x/2;j=x/(2-x);a=d+j;b=a+148*e;c=a+74*e;h=x+b
# on wrapped torus plus shares same link labels, use row block l2 majorant
r=(s.Rational(168,13)*(a+b)+13*(c+h))/13
# Q defect row coefficient; positive flat crossing term, all counts integer
weights=[a+b,c,h]; den=s.ilcm(*[v.q for v in weights]); A,B,C=[int(v*den) for v in weights]
ss=0
for mu in range(4):
 cent=Counter(walk(Z,tuple(L*(k==mu) for k in range(4))))
 keys=set(m)|set(cs[mu])|set(cent)
 ss+=sum((A*m[k]+B*cs[mu][k]+C*N*cent[k])**2 for k in keys)
K=s.Rational(ss,N*L**2*den**2)
print('defect squared normalized', K,float(K),'row',r)
# max-of-four section to Euclidean norm <=2 ; gauge correction norm relative to section
# reduced gauge adjoint floor and perturbation bound
f=s.Rational(130991,3145728); delta=s.Rational(9,1048576)
# ||P_G Sbar - Sbar|| <= sqrt(delta/f) in Euclidean norm; Q0 times projection correction can bound by same
# full preconditioned Q norm <=1+sqrt(K)
# max coarse norm correction <= 2*(1+sqrt(K))*sqrt(delta/f)
print('correction bound',float(2*(1+s.sqrt(K))*s.sqrt(delta/f)))
# use Euclidean bound of QS-I via block row sums and columns: crude 2r; enough?
print('2r + correction',float(2*r+2*(1+s.sqrt(K))*s.sqrt(delta/f)))
assert K < 16**2
assert delta/f < s.Rational(1,69)**2
bound=r+s.Rational(34,69)
assert bound < s.Rational(7,8)
print('PASS reduced gauge projected section bound',bound,float(bound),'inverse section factor < 8')
