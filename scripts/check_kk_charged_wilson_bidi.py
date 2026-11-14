#!/usr/bin/env python3
"""KK S1 charged Wilson-line + radion: same-spectrum one-loop BIDI audit.
Free fields: graviton(-5), Maxwell(-3), scalar(-1), three neutral massive
Dirac fermions(+12), one charged massive Dirac(+4). mQ=4*mN.
The standard free-field periodic S1 Casimir sum is the sourced input.
No exact 5D rotating Earth or Standard Model is claimed.
"""
from mpmath import mp
mp.dps=55
N=180
Z=mp.zeta(5)
C=3*Z/(64*mp.pi**6)
A,D,Q,K=9,12,4,mp.mpf(4)
HC=mp.mpf('0.1973269804e-15')
MP=mp.mpf('2.435e18')
e=mp.sqrt(4*mp.pi/mp.mpf('137.035999084'))
b=mp.mpf('1e-24')/HC

def f(z,t=mp.mpf(0),kind='value'):
    terms=[]
    for n in range(1,N+1):
        nz=n*z; p=mp.exp(-nz); co=mp.cos(n*t); si=mp.sin(n*t)
        if kind=='value': v=p*(1+nz+nz*nz/3)*co/n**5
        elif kind=='z': v=-z*p*(1+nz)*co/(3*n**3)
        elif kind=='zz': v=-p*(1+nz-nz*nz)*co/(3*n**3)
        elif kind=='theta': v=-p*(1+nz+nz*nz/3)*si/n**4
        elif kind=='thetatheta': v=-p*(1+nz+nz*nz/3)*co/n**3
        elif kind=='ztheta': v=z*p*(1+nz)*si/(3*n**2)
        else: raise ValueError(kind)
        terms.append(v)
    return mp.fsum(terms)/Z

def h(z,t): return f(z,t)-z*f(z,t,'z')/5
def hp(z,t): return (4*f(z,t,'z')-z*f(z,t,'zz'))/5
def equation(z,k): return D*h(z,0)+Q*h(k*z,mp.pi)-A
def eqprime(z,k): return D*hp(z,0)+Q*k*hp(k*z,mp.pi)
z=mp.findroot(lambda v:equation(v,K),(mp.mpf('1.4'),mp.mpf('1.8')))
zq=K*z
ell=A-D*f(z)-Q*f(zq,mp.pi)
def U(x,t):
    return ell/x+(-A+D*f(z*x)+Q*f(zq*x,t))/x**6
Ux=-ell-6*(-A+D*f(z)+Q*f(zq,mp.pi))+D*z*f(z,0,'z')+Q*zq*f(zq,mp.pi,'z')
Uxx=D*(z*z*f(z,0,'zz')-4*z*f(z,0,'z'))+Q*(zq*zq*f(zq,mp.pi,'zz')-4*zq*f(zq,mp.pi,'z'))
Utt=Q*f(zq,mp.pi,'thetatheta')
Uxt=Q*(zq*f(zq,mp.pi,'ztheta')-6*f(zq,mp.pi,'theta'))
assert abs(U(1,mp.pi))<mp.mpf('1e-45') and abs(Ux)<mp.mpf('1e-45')
assert abs(Q*f(zq,mp.pi,'theta'))<mp.mpf('1e-45')
assert Uxx>0 and Utt>0 and abs(Uxt)<mp.mpf('1e-45')
for x,t in ((mp.mpf('.999'),mp.pi),(mp.mpf('1.001'),mp.pi),(1,mp.pi-mp.mpf('.005')),(1,mp.pi+mp.mpf('.005'))):
    assert U(x,t)>0

# For zq>=6, an analytic harmonic tail bound proves the Wilson minimum
# is globally at pi: |sin(n*t)| <= n sin(t) for 0<t<pi.
q=mp.exp(-zq)
first=q*(1+zq+zq*zq/3)
tail=q*q/(1-q)+zq*q*q*(2-q)/(1-q)**2+zq*zq*q*q*(4-3*q+q*q)/(3*(1-q)**3)
assert zq>6 and tail<first
# Compare analytic derivatives with independent arbitrary-precision differentiation.
assert abs(mp.diff(lambda t:f(zq,t),mp.pi,2)-f(zq,mp.pi,'thetatheta'))<mp.mpf('1e-45')
assert abs(mp.diff(lambda x:U(x,mp.pi),1,2)-Uxx)<mp.mpf('1e-44')

# New saddle-node: a lower, unstable Minkowski stationary radius exists.
foldz,foldk=mp.findroot((equation,eqprime),(mp.mpf('1.0'),mp.mpf('3.1')))
assert abs(equation(foldz,foldk))<mp.mpf('1e-42')
assert abs(eqprime(foldz,foldk))<mp.mpf('1e-42')
assert mp.mpf('3.012')<foldk<mp.mpf('3.014')
lower=mp.findroot(lambda v:equation(v,K),(mp.mpf('.3'),mp.mpf('.7')))
assert lower<foldz<z
lowxx=D*(lower*lower*f(lower,0,'zz')-4*lower*f(lower,0,'z'))+Q*((K*lower)**2*f(K*lower,mp.pi,'zz')-4*K*lower*f(K*lower,mp.pi,'z'))
assert lowxx<0

# Canonical kinetic normalisation: ftheta=1/(2*pi*b*e), theta=e5 integral B5.
radcoeff=mp.sqrt(2*C*Uxx/3)
lrad=HC*MP*b*b/radcoeff
ftheta=1/(2*mp.pi*b*e)
mtheta=mp.sqrt(C*Utt/b**4)/ftheta
ltheta=HC/mtheta
mneutral=z/(2*mp.pi*b)
mcharged=zq/(2*mp.pi*b)
mlight=mp.sqrt(mcharged*mcharged+(1/(2*b))**2)
M5=(MP**2/(2*mp.pi*b))**(mp.mpf(1)/3)
assert mcharged<M5 and b*M5>1000 and lrad<mp.mpf('1e-10')
assert mlight>mp.mpf('1e8')  # Not the observed electron!
for name,value in [('z_neutral',z),('z_charged',zq),('tuned_cosmological_term',ell),
 ('radion_curvature',Uxx),('Wilson_curvature',Utt),('mixed_curvature',Uxt),
 ('radion_range_m',lrad),('Wilson_range_m',ltheta),('lightest_charged_mass_GeV',mlight),
 ('fold_charged_neutral_mass_ratio',foldk),('lower_unstable_curvature',lowxx),
 ('first_harmonic_tail_ratio_upper_bound',tail/first)]:
    print(name,mp.nstr(value,17))
print('PASS coupled Minkowski, positive Hessian, Wilson global minimum and nontrivial fold')
print('FAIL observed-electron consumer: all charged periodic 4D modes are extremely heavy and vectorlike')
print('OPEN real 5D Earth matter source, full chiral charged spectrum, interactions and kernel proof')

# GLOBAL STEELMAN FAILURE: local positive Hessian is NOT a global lower bound.
# At x->0 the massive fermions become massless. At theta=pi,
# f(0,pi)=-15/16, so coefficient -9+12-4*15/16=-3/4<0.
collapse_coeff=-A+D-Q*mp.mpf(15)/16
assert collapse_coeff==-mp.mpf(3)/4
assert U(mp.mpf('.05'),mp.pi)<0
def Wx(x):
    return D*z*f(z*x,0,'z')+Q*zq*f(zq*x,mp.pi,'z')
def W(x):
    return -A+D*f(z*x)+Q*f(zq*x,mp.pi)
def derivU(x):
    return -ell/x**2+Wx(x)/x**6-6*W(x)/x**7
barrier=mp.findroot(derivU,(mp.mpf('.27'),mp.mpf('.31')))
height=U(barrier,mp.pi)
assert 0<barrier<1 and height>0
assert U(barrier-mp.mpf('.01'),mp.pi)<height
assert U(barrier+mp.mpf('.01'),mp.pi)<height
print('collapse_asymptotic_coefficient',collapse_coeff)
print('collapse_barrier_x',mp.nstr(barrier,16),'dimensionless_height',mp.nstr(height,16))
print('FAIL global-radius-stability consumer: U(x,pi) -> -infinity for x -> 0')
print('OPEN bounce action / tunneling lifetime / UV stabilization; not identified with low-branch retuned Minkowski root')
