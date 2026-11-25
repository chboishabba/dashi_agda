"""Exact controls, not a full Selmer/PDE/Chow computation."""
from fractions import Fraction as Q
from itertools import product, combinations, permutations
import sympy as S

def need(ok):
    if not ok: raise ArithmeticError('control failed')

x,a=S.symbols('x a'); A=-66; B=289; f=x**3+A*x+B
h1=10+3*(x-5)**2/4;h2=15-x+(x-4)**2/2
need(S.expand(h1*h1-f-(9*x-61)*(x**3-15*x*x+75*x-141)/16)==0)
need(S.expand(h2*h2-f-(x-12)*(x**3-12*x*x+48*x-80)/4)==0)
P=[(Q(61,9),Q(-334,27)),(Q(12),Q(-35))]
for h,(n,m),R in zip((h1,h2),((5,2),(4,2)),P):
    z=n+m*a; y=h.subs(x,z)
    need(S.rem(S.expand(y*y-f.subs(x,z)),a**3-2,a)==0)
    need(-h.subs(x,R[0])==R[1] and R[1]**2==R[0]**3+A*R[0]+B)
res={(i,j) for i,j in product(range(3),repeat=2) if i or j}
for p in (5,11,41):
    need((4*A**3+27*B*B)%p!=0)
    pts=[None]+[(x,y) for x,y in product(range(p),repeat=2) if (y*y-x**3-A*x-B)%p==0]
    def add(P,R):
        if P is None:return R
        if R is None:return P
        x,y=P;u,v=R
        if x==u and (y+v)%p==0:return None
        m=((v-y)*pow(u-x,-1,p) if x!=u else (3*x*x+A)*pow(2*y,-1,p))%p
        z=(m*m-x-u)%p;return z,(m*(x-z)-y)%p
    three={add(add(R,R),R) for R in pts}
    if p==5:need(len(pts)==8);continue
    mod=lambda r:r.numerator*pow(r.denominator,-1,p)%p
    U,V=[tuple(map(mod,R)) for R in P]; need(U in pts and V in pts)
    us=[None,U,add(U,U)];vs=[None,V,add(V,V)]
    res={(i,j) for i,j in res if add(us[i],vs[j]) in three}
    need((len(pts),len(three),res)==((12,4,{(0,1),(0,2)}) if p==11 else (51,17,set())))
    print('BSD p',p,'group',len(pts),'3image',len(three),'remaining',sorted(res))
# Fourier heat signed difference: exact rational collinear/sphere directions.
# reverse triangle inequality and heat denominator <= 1/(2pq).
vec=[v for v in product(range(-3,4),repeat=3) if sum(x*x for x in v) in (1,4,9,16,25)]
from math import isqrt
n=0
for p,q in product(vec,repeat=2):
    r=isqrt(sum(x*x for x in p)); s=isqrt(sum(x*x for x in q)); k2=sum((x+y)**2 for x,y in zip(p,q))
    need((r-s)**2<=k2 and (r+s)**2>=k2)
    need(Q(1,r*r+s*s)<=Q(1,2*r*s));n+=1
print('NS',n,'signed-radius and heat denominator controls')
# Pfaffian cubic on wedge^2 of a rank6 diagonal form: signed perfect matchings.
pairs=list(combinations(range(6),2)); z=S.symbols('z:15'); index={ij:i for i,ij in enumerate(pairs)}
def sign(seq):return (-1)**sum(seq[i]>seq[j] for i in range(len(seq)) for j in range(i+1,len(seq)))
poly=0;triples=0
for i,j,k in combinations(range(15),3):
    seq=pairs[i]+pairs[j]+pairs[k]
    if len(set(seq))==6:poly+=sign(seq)*z[i]*z[j]*z[k];triples+=1
need(triples==15)
# exterior cubic: each matching appears 6 times; reflection reverses all terms.
need(S.expand(poly.subs({z[i]:-z[i] for i,ij in enumerate(pairs) if 0 in ij},simultaneous=True)+poly)==0)
# verify derivatives correspond to the 15 four-slot Pfaffians with signs
for i,(a,b) in enumerate(pairs):
    c,d,e,f=[k for k in range(6) if k not in (a,b)]
    pf=z[index[c,d]]*z[index[e,f]]-z[index[c,e]]*z[index[d,f]]+z[index[c,f]]*z[index[d,e]]
    need(S.expand(S.diff(poly,z[i])-sign((a,b,c,d,e,f))*pf)==0)
print('Hodge 15 signed matchings; 15 Pfaffian derivatives; reflection sign')
