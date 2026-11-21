from itertools import product
from collections import Counter
import sympy as s
L=13; N=L**4; e=s.Rational(1,4096); x=222*e
j=x/(2-x); a=x/2+j
# paired connectors (R C = U V U^-1); central average cancels linear term
p=26*e*(2+j)
c=a+74*e
h=x*x*s.Rational(5,12)+(1+j)*x*x*(s.Rational(1,4)+(1+x/2)/6)
m=Counter()
for z in product(range(-6,7),repeat=4):
 for d in range(4):
  for k in range(min(0,z[d]),max(0,z[d])):
   v=z[:d]+(k,)+(0,)*(3-d)
   m[tuple(t%L for t in v),d]+=1
assert sum(m.values())==4*42*L**3
# crossing counts L at every bond of direction mu, central N on line
weights=[p,c,h]; den=s.ilcm(*[v.q for v in weights]); P,C,H=[int(v*den) for v in weights]
ss=0
for mu in range(4):
 for z in product(range(L),repeat=4):
  for d in range(4):
   ss+=(P*m[z,d]+C*L*(d==mu)+H*N*(d==mu and all(z[k]==0 for k in range(4) if k!=mu)))**2
K=s.Rational(ss,N*L**2*den**2)
r=(s.Rational(168,13)*p+13*(c+h))/13
print('paired',p,float(p),'crossing',float(c),'central',float(h),'K',K,float(K),'row',r,float(r))
# A0 is isometry adjoint, mean/detail split; A h=0 implies norm mean <= 2 sqrt(K)/(1-r) norm detail
# max norm inverse and coarse 2-norm conversion
ratio=4*K/(1-r)**2
floor=1/(18*(1+ratio))
print('mean/detail ratio squared',float(ratio),'flat scalar difference floor',floor,float(floor),'64rho',float(s.Rational(64,8192)))
assert r<1
assert K<4
ratio_e=K/(1-2*r)**2
floor_e=1/(18*(1+ratio_e))
delta=s.Rational(9,1048576)
loss=96*e
remaining=floor_e-delta-loss
print('Euclidean ratio',float(ratio_e),'difference floor',float(floor_e),'ambient Wilson Hessian floor',remaining,float(remaining))
assert floor_e>s.Rational(1,25)
assert remaining>s.Rational(1,64)
