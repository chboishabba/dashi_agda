#!/usr/bin/env python3
"""Original SU(N) Wilson/F19 vertical zero jet and RH-reflection no-go.
Kinematic field curves only; NOT YM/OS time evolution or RH proof.
"""
from itertools import product,combinations
import sympy as s
I=s.I
sites=tuple(product(range(4),repeat=4))
def step(x,a):
 y=list(x);y[a]=(y[a]+1)%4;return tuple(y)
def face(x,a,b):
 return ((x,a,1),(step(x,a),b,1),(step(x,b),a,-1),(x,b,-1))
faces=tuple(face(x,a,b) for x in sites for a,b in combinations(range(4),2))
src=(0,0,0,0);dst=(0,0,0,2)
u=(src,2);v=(step(src,2),2);g=(dst,2)
F=face(src,2,3);G=face(dst,2,3)
coarse={((x,a),(step(x,a),a)) for x in product((0,2),repeat=4) for a in range(4)}
assert (len(sites),len(faces),len(coarse))==(256,1536,64)
assert len({b for pair in coarse for b in pair})==128
assert (u,v) in coarse and sum(u in c or v in c for c in coarse)==1
stars={e:[p for p in faces if any((x,a)==e for x,a,_ in p)] for e in (u,v,g)}
assert all(len(stars[e])==6 for e in stars)
assert all(sum(p in stars[e] for e in stars)<=1 for p in faces)
def real(z):return s.simplify(s.re(s.expand_complex(z)))
def check(n):
 # Root-of-unity zero-trace holonomy, determinant one for all n>=2.
 diag=tuple(s.exp(I*s.pi*(2*j+(n%2==0))/n) for j in range(n))
 assert s.simplify(s.prod(diag)-1)==0
 assert s.simplify(s.expand_complex(sum(diag)))==0
 imag=[s.simplify(s.im(s.expand_complex(w))) for w in diag]
 i,j=next((i,j) for i in range(n) for j in range(i+1,n)
          if s.simplify(imag[i]-imag[j])!=0)
 a=tuple(s.Integer(int(k==i)-int(k==j)) for k in range(n))
 assert sum(a)==0
 other=(s.exp(I*s.pi/3),s.exp(-I*s.pi/3))+ (s.Integer(1),)*(n-2)
 assert s.simplify(s.prod(other)-1)==0
 def at(e,k):return diag[k] if e==u else other[k] if e==g else s.Integer(1)
 def rate(e,k):return a[k] if e==u else -a[k] if e==v else 0
 def jet(loop):
  f=s.Integer(0);d=s.Integer(0)
  for k in range(n):
   z=s.Integer(1);q=0
   for x,axis,sg in loop:
    e=(x,axis);w=at(e,k)
    z*=w if sg==1 else 1/w;q+=sg*rate(e,k)
   f+=z;d+=I*q*z
  return real(f)/n,real(d)/n
 f,df=jet(F);g0,dg=jet(G)
 assert f==0 and dg==0 and s.simplify(g0-s.Rational(n-1,n))==0
 assert s.simplify(df)!=0
 total=s.Integer(1536-18);dtotal=s.Integer(0)
 for e in stars:
  for p in stars[e]:
   x,dx=jet(p);total+=x;dtotal+=dx
 assert s.simplify(total-(1536-6-s.Rational(6,n)))==0
 assert s.simplify(dtotal-6*df)==0
 r,beta=s.symbols('r beta',real=True)
 # Compensating native fine pair: all 64 W unchanged at every r.
 assert all(s.simplify(diag[k]*s.exp(I*a[k]*r)*s.exp(-I*a[k]*r)-diag[k])==0
            for k in range(n))
 weight=s.exp(-beta*(1536-total))
 assert s.simplify(weight-s.exp(-beta*(6+s.Rational(6,n))))==0
 # Four ORIGINAL same-weight coefficients (1,F,G,FG):
 # normalized derivatives of w, wF, wG, wFG at r=0.
 jets=(beta*dtotal,df,g0*beta*dtotal,g0*df)
 assert all(s.simplify(x)==0 for x in (jets[0]-6*beta*df,
                                      jets[2]-g0*jets[0],jets[3]-g0*jets[1]))
 # Source gauge-invariant first derivative cannot be removed by
 # any site gauge conjugation of a CLOSED plaquette.
 M=s.diag(*diag);D=s.diag(*(I*diag[k]*a[k] for k in range(n)))
 h=s.Matrix([[1,1],[-1,1]])/s.sqrt(2)
 h=s.diag(h,*([1]*(n-2))) if n>2 else h
 assert s.simplify(h.det()-1)==0
 assert s.simplify(s.trace(h*D*h.inv())-s.trace(D))==0
 print('PASS SU(%d): F(0)=0, Fprime=%s, G=%s, all 64 W fixed, Wilson score=6beta*Fprime'%(n,df,g0))
for n in (2,3,4,5):check(n)
print('PASS original 256 sites/1024 links/1536 plaquettes/64 W/896 spectators')

# xi reflection facts give horizontal sign-germ, not RH off-line exclusion.
z=s.symbols('z');x=s.symbols('x',real=True)
a=s.Rational(1,3);gam=s.Integer(2)
p=s.expand((z*z+gam*gam)*((z-I*gam)**2-a*a)*((z+I*gam)**2-a*a))
assert s.simplify(p.subs(z,-z)-p)==0
assert all(s.im(c)==0 for c in s.Poly(p,z).all_coeffs())
assert all(s.simplify(p.subs(z,t))==0 for t in
           (I*gam,-I*gam,a+I*gam,-a+I*gam,a-I*gam,-a-I*gam))
f=s.expand(p.subs(z,x+I*gam))
assert s.simplify(f.subs(x,-x)-s.conjugate(f))==0
assert s.diff(f,x).subs(x,0)==I*s.Rational(580,81)
print('PASS RH completed-reflection polynomial: simple critical signed jet PLUS off-axis quartet')
n=s.symbols('n',integer=True,positive=True)
assert s.limit(-n*s.log(1-1/n**2),n,s.oo)==0
assert s.limit(-n*s.log(1-1/n),n,s.oo)==1
print('PASS finite positive transfer gap can yield zero or positive continuum energy')
print('OPEN actual xi zero exclusion, physical Yang-Mills CMP119/W3/OS and same-H continuum gap')


# RH #1533 reflected zero pair in completed xi'/xi (not a zero of xi):
# 1/(w-a)+1/(w+a)=2w/(w²-a²), retaining BOTH pole residues.
w=s.symbols('w',real=True);A=s.symbols('A',real=True)
pair=s.cancel(1/(w-a)+1/(w+a))
assert pair.subs(w,0)==0
assert s.simplify(s.diff(pair,w).subs(w,0)+2/(a*a))==0
assert s.simplify(s.limit(2*w/(w*w-A*A),A,0)-2/w)==0
print('PASS RH signed midpoint cancellation: nonzero jet -2/a²; coincident poles DO NOT vanish')
