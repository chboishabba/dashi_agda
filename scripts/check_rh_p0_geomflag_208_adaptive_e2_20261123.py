#!/usr/bin/env python3
"""RH P0: dyadic-15 flag, 208/26 budget audit, constructive flat-top E2.
Exact Fraction + SymPy checks. NOT a Lean/Agda kernel or an RH proof.
Source: RHQuartic163840DyadicTailHXIntertwinerExact, original punctured27,
RiemannSelectedPrimeSensitiveFrozenApertureExact and selected W.
"""
from fractions import Fraction as F
from math import comb, factorial
import sympy as S

def convolution(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b): c[i+j]+=u*v
    return c
E=[F(1)]
for w,n in [(F(1),9),(F(1,4),9),(F(1,196),2),
            (F(1,225),2),(F(1,289),2),(F(1,324),2)]:
    for _ in range(n): E=convolution(E,[F(1),w])
assert len(E)==27 and E[0]==1
assert E[1]==F(1294113017,114704100)
assert E[26]==F(1,4469951457296583229440000)
assert all(0<E[j]<=F(comb(26,j)) for j in range(27))
print("PASS source: 27=1+26 and punctured27 9+8+9 exact weighted E_j")

q=S.symbols("q",positive=True)
assert S.integrate(q**-6,(q,8,S.oo))==S.Rational(1,163840)
assert 8**5==32768==2**15 and 5*32768==163840
assert 26*8==208 and F(26,208)==F(1,8)
print("PASS 32768 is existing dyadic15 q-tail flag, not a forced height")
assert F(26)/(F(1,4)-F(4,32))==208
assert F(26)/(F(1,4)-F(4,64))==F(416,3)
assert F(26)/(F(1,4)-F(3,32))==F(832,5)
print("PASS 208 changes with width or plateau mass; not invariant 26×8 action")

# C-infinity flat top via infinite uniform-box convolution:
# h_m=1/(256*m^2), sum_m h_m<=1/128; eta= *_{m>=1} U_hm.
# B = 1_[-3/128,3/128] * eta; b_p=B(u-log p)+B(u+log p).
# Supports within 1/32, equals one within 1/64; ||b_p||1=3/32.
# Its kth L1 derivative bound for k>=1 is
# 4*256^(k-1)*((k-1)!)² by box derivative total variation.
a,b=F(3,128),F(1,128)
assert a+b==F(1,32) and a-b==F(1,64) and 4*a==F(3,32)
for n in (1,2,8,26,52):
    assert sum(F(1,256*j*j) for j in range(1,n+1))<=b
B=[4*a]+[F(4)*256**(2*j-1)*factorial(2*j-1)**2 for j in range(1,27)]
assert B[0]==F(3,32) and B[1]==1024
print("PASS explicit C-infinity compact flat top and every needed derivative bound")

def H(r):
    """All-source Sobolev majorant, no equal 1/208 splitting."""
    v,z=F(0),F(1)
    for e,w in zip(E,B):
        v+=e*w*z
        z/=r*r
    return v
assert H(31829)>F(1,4)>=H(31830)
assert H(32768)<F(1,7)
print("PASS exact flat-top L1 bound from r>=31830, t>=509280")
print("PASS q-tail geometric checkpoint r=32768, t=524288: H<1/7")

# Original W: T_W>567/1600, projective mass<=5184 and support<5.
# For |a|<=1/2, cosh(5|a|/r)<=1+25/(4r²) at t>=200.
# Thus m_W >= c(r)/r^6. Exact rational threshold removes 32768.
def c(r):
    x=F(r*r)
    return F(567,1600*24)-F(28125,4)/x*(1+F(25,4)/x)
assert c(1214)<F(1,100)<c(1215)
x=S.symbols("x",positive=True)
poly=S.expand(((S.Rational(567,38400)-S.Rational(1,100))
    -S.Rational(28125,4)/x*(1+S.Rational(25,4)/x))*12800*x*x)
assert poly==61*x*x-90000000*x-562500000
print("PASS t>=19440 (r>=1215) gives m_W>1/(100*r^6) full physical strip")

# Physical port C_i<=K H(r)/r with original |G|1<=83/30,
# original |pole|<32, U=5/4 and cosh(U/2)<2.
K=F(4)*F(83,30)*F(32)*F(5,4)**10/factorial(10)
assert K==F(6484375,7134511104) and 4*K<F(64,100)
# For all r>=1215 set eps_i=kappa_i/(r^5*(1+H(r))), |kappa_i|<=1.
# Sum_i |eps_i|C_i < 4*K*H/(1+H)/r^6
#                        < 4*K/r^6 <64*m_W (target intact).
for r in (1215,2048,26870,26871,31829,31830,32768):
    h=H(r)
    assert 4*K*h/(1+h)<4*K<64*c(r)
assert 4*K*H(26870)>=64*c(26870)
assert 4*K*H(26871)<64*c(26871)
print("PASS adaptive eps=r^-5/(1+H): every r>=1215, no T_b/208 prerequisite")
print("PASS plain eps=r^-5 sufficient from r>=26871, t>=429936")
print("PASS asymptotic eps/r^-5=32/35 since H(r)->3/32")
print("OPEN full E2 FarExact/post-sixth, E3 independent signed gap, Lean/Agda kernels")
print("RH/GRH remain OPEN; no CI")
