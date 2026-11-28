"""Symbolic source rechart, not a kernel proof or new cube."""
import sympy as S


def require(ok):
    if not ok:
        raise AssertionError('single prefix chart')


p, i, t, u = S.symbols('p i t u')
G = S.groebner([p*p+3*p+3, i*i+1], p, i, domain=S.EX)
red = lambda x: G.reduce(S.expand(x))[1].expand()
aR,aI,bR,bI = S.symbols('aR aI bR bI')
z = aR+i*aI+p*(bR+i*bI)
A = aR+p*bR
B = aI+p*bI
single = lambda t,A,B: (t+p*B,A)
R,I = single(t,A,B)
require(red(R+i*I-((t-3*bI)+i*aR+p*((aI-3*bI)+i*bR)))==0)
R2,I2 = single(u,R,I)
require(red(R2+i*I2-(u+i*t+p*z))==0)
# Original observer: four pairs and ninth real trit. Actual H05 single
# prefix re-packs them as five pairs, never assumes one trit is one pi digit.
a = S.symbols('a:5')
b = S.symbols('b:4')
A = sum(a[j]*p**j for j in range(5))
B = sum(b[j]*p**j for j in range(4))
raw = [q for ab in zip(a[:4],b) for q in ab]+[a[4]]
prefix = [t]+raw
packed = sum((prefix[2*j]+i*prefix[2*j+1])*p**j for j in range(5))
require(red(packed-(t+p*B+i*A))==0)
# Existing X/Y act on last two source trits. Signed differences are
# explicit (the balanced wrap may be -2, not always +1).
dx,dy = S.symbols('dx dy')
changed = raw[:-2]+[raw[-2]+dx, raw[-1]+dy]
old9 = sum((raw[2*j]+i*raw[2*j+1])*p**j for j in range(4))+raw[8]*p**4
new9 = sum((changed[2*j]+i*changed[2*j+1])*p**j for j in range(4))+changed[8]*p**4
require(red(new9-old9-(i*p**3*dx+p**4*dy))==0)
changed10 = [t]+changed
new10 = sum((changed10[2*j]+i*changed10[2*j+1])*p**j for j in range(5))
require(red(new10-packed-p**4*(dx+i*dy))==0)
print('PASS five symbolic identities: coefficient rechart, double prefix, actual 9-to-10 alignment, signed X/Y upper and lower differences')
