"""Independent finite/symbolic diagnostic; not a native Agda acceptance."""
from fractions import Fraction as F
from itertools import product
import sympy as s

counts = dict(address=0, chart=0, cofinal=0, algebra=0, majorant=0)

def offset(bits):
    return sum(b << i for i, b in enumerate(bits[:-1])) - (bits[-1] << (len(bits)-1)) if bits else 0

def reopen(j, m):
    r = j % (1 << m)
    return tuple((r >> i) & 1 for i in range(m))

for m in range(1, 13):
    N=1<<m
    seen=set()
    for bits in product((0,1),repeat=m):
        j=offset(bits)
        assert -N//2 <= j < N//2 and reopen(j,m)==bits and j not in seen
        seen.add(j); counts['address']+=1
        x,y=F(7,13),F(11,17)
        a,b=x,y
        for i,bit in enumerate(bits):
            a=(a+bit*(-1 if i==m-1 else 1))/2; b/=2
        assert (a,b)==((x+j)/N,y/N)
        counts['chart']+=1
    assert seen==set(range(-N//2,N//2))
    for j in range(-N//2,N//2):
        assert offset(reopen(j,m+1))==j
        counts['cofinal']+=1

h,x,y,r,c,t,p,q,i=s.symbols('h x y r c t p q i', real=True)
X=q*i**2; Y=q*(-h*i)**2
for lhs,rhs in [(Y,h*h*X),(h**4*(X+6*X**2),h*h*Y+6*Y**2),(h**6*(X+30*X**2+120*X**3),h**4*Y+30*h*h*Y**2+120*Y**3),((x*y)**2,(x*x)*(y*y))]:
    assert s.expand(lhs-rhs)==0; counts['algebra']+=1
# Gap identity, reduce by the actual Pythagorean and doubled cosine laws.
gap=(1-r*c)**2+(r*t)**2
want=(1-r)**2+4*r*p*p
assert s.reduced(s.expand(gap-want),[c*c+t*t-1,c-(1-2*p*p)],t,c,r,p)[1]==0
counts['algebra']+=1
# Uniform majorant algebra (nonnegative values, b<=B, 0<h<=1).
for n in range(1,81):
    B=F(n,9)
    for J in range(1,65):
        b=B/(J*J)
        for m in (1,2,4,8):
            h=F(1,1<<m)
            assert h*h*b+6*b*b <= (1+6*B)*b
            assert h**4*b+30*h*h*b*b+120*b**3 <= (1+30*B+120*B*B)*b
            counts['majorant']+=2
print(counts, 'total',sum(counts.values()), 'PASS')
