"""Exact contraction constants from actual 234446.a1 B-M7s receipt.
This proves scalar estimates, not coalescence or a new Mellin quadrature.
"""
from fractions import Fraction as Q
from itertools import product
checks=0
def ck(ok):
    global checks
    if not ok: raise AssertionError('signed root contraction guard failed')
    checks+=1
A=Q(8270793387711404,12*10**12)
B=Q(25600); m=Q(13,10**12); r=Q(7,50_000_000); R=r*r
eta=(m+B*R*R/(1-R))/A
L=B*(2*R-R*R)/(A*(1-R)**2)
ck(A>0 and 0<R<1)
ck(eta<R)
ck(0<L<Q(1,10**11))
ck(B*R/(A*(1-R))<1)
ck(B*R*R/(A*(1-R))<Q(2,10**26))
# exact factorization of differences, including zero and signs
for x,y in product((Q(-2,3),Q(-1,5),Q(0),Q(1,5),Q(2,3)),repeat=2):
    for n in range(1,13):
        ck(x**n-y**n==(x-y)*sum(x**i*y**(n-1-i) for i in range(n)))
        ck(abs(x**n-y**n)<=n*Q(2,3)**(n-1)*abs(x-y))
# truncated geometric derivative remainder (exact finite identity)
for n in range(2,20):
    ck(sum(k*R**(k-1) for k in range(2,n+1))< (2*R-R*R)/(1-R)**2)
print(f'{checks}/{checks} exact rational guards PASS')
print('self-map ratio',float(eta/R),'contraction',float(L),'radius squared',float(R))
