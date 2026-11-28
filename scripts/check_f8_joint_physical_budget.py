"""Independent rational re-evaluation of inherited F8 tilted budget.
Analytic kernel, clock, bump and localization inequalities are prerequisites.
"""
from fractions import Fraction as Q
from math import factorial, floor, isqrt
K=Q(1780000); eps=Q('.04'); rho=Q('.000361'); scale=10**300; E=Q('2.71828')
def root(x):
    d=10**20; n=isqrt((x*d*d).numerator//(x*d*d).denominator)
    return Q(n,d),Q(n+1,d)
def expneg(x):
    assert x>0
    return E**(-floor(x))
def laplace(a,b):
    t0=root(a/b)[1]
    return root(2*Q(22,7)*t0/b)[1]+4/b,2*root(a*b)[0]
def selfrho(m,b,a,d,g):
    v=g*(g+2*d); w=root(v)[0]
    return Q(3,2)/(b*K*w)+a*(1+m*m)/(2*K*v*w)
def ceilgrid(x): return (x.numerator*scale+x.denominator-1)//x.denominator
assert sum(Q(1,factorial(j)) for j in range(11))>E
wr,er=laplace(eps/2,K); ws,es=laplace(Q('.065')/4,Q('.8')*K); wq,eq=laplace(Q('.05')*Q('.99'),Q('1.03')*K)
radA=eps**5*wr; radB=8*eps**6; source=8*ws
P=[Q(1)]+[(Q(j)/Q('.027'))**j for j in range(1,5)]
obsP=15*Q('.027')*wq*(Q('.3')*(2*P[2]+8*P[3]+4*P[4])+Q('.18')*P[2]+Q('.009'))
obs0=15*Q('.027')*wq*Q('.003'); base=es+eq-K*rho-3
edges=list(map(Q,['0','.5','1','1.5','2','2.5','3','4','5','6','7','8']))
low=0
for a,m in zip(edges,edges[1:]):
    e=selfrho(m,Q('.997'),Q('.26'),Q('.7'),Q('.09'))
    r=selfrho(m,Q('.087'),Q('.09'),Q('.99'),Q('.035'))
    assert max(e,r)<1
    d=r**6/(1-r)
    c=sum(e**i*r**(6-i) for i in range(6))/(1-r)+e**6/((1-r)*(1-e))
    residual=Q('.001')*d+30*(1+m*m)*c
    k2=K*K*(1+m*m); obs=(obsP*k2**2+obs0*k2**3)/2
    radial=min(radA*expneg(base+er),radB*expneg(base+root(eps*K*a)[0]))
    low+=ceilgrid(K*(m-a)/3*source*radial*obs*residual)
# For omega>=8K, complex angular estimate gives same 2a sqrt(omega) sqrt(tau) coefficient.
assert (Q(65,64)**2)*8<16 # (sqrt(65/64)*2^(3/4))^4 < 2^4
C=Q(3617,250000); B=Q(102919,144565); loss=4*C**3/(27*Q('.01')**2)
assert B+loss<1
for h,b,a in ((Q('.0037'),Q('.997'),Q('.26')),(Q('.01'),Q('.087'),Q('.09'))):
    assert h*(Q(3,2)/b+Q(8,3)*a)<2
assert Q('.001')+7*60<421
w0=floor(root(8*K)[0]); a=Q('.19'); assert w0*w0<=8*K
poly=2*sum(Q(factorial(23),factorial(j))*Q(w0)**j/a**(24-j) for j in range(24))
tail=source*radB*(2*obsP+4*obs0)*Q(108*64*421,3)/K**2*poly*expneg(base+a*w0)
num=low+ceilgrid(tail)
assert num==7100901973797509969638
R=Q(num,scale); direct=Q(4536110765573153915383864911903,scale)
assert direct-R>Q('4.536e-270')
assert Q('.04')*direct-4*R>Q('1.814e-271')
absrow=Q(25625913306690676040506148447313974772973827225035760610806855962525604705888543158345301526058010132023028426526837691,scale)
assert Q(3,2)*absrow<Q('3.844e-182')
assert direct-R+(Q('.04')*direct-4*R)/2>Q('4.6267e-270')
print('Exact inherited tilted numerator:',num,'/ 1e300; high tail grid units:',ceilgrid(tail))
print('Conditional joint tidal magnitude: >4.6267e-270 and <3.844e-182')
