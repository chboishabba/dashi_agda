#!/usr/bin/env python3
"""RH P0 E0/E1/E2 local regression against original Lean two-scale source.

SymPy: exact atomic/corridor Fourier determinant, projective nonlinearity,
literal even-cone factor four. Numerics: SAME four-window formula with smooth
C-infinity fixture b(x)=exp(-1/(1-x^2)); J2=0 solved numerically; source-normalized
pole determinant, quartic target, eight-invariant even bump projection,
two-prime signed-projective formula and conservative ||h''||1 cost.

The fixture is NOT Mathlib's noncomputably selected unitContDiffBump.
Not a Lean kernel receipt, interval arithmetic, or RH/GRH proof.
"""
import math
import numpy as np
import sympy as S
from scipy.optimize import brentq

mh, mt = S.symbols("mh mt", real=True)
mu0h, mu0t = -S.Rational(1,78), S.Rational(1,162)
D = S.expand((S.Rational(1,2)-mh)*(S.Rational(5,6)+mt)
             -(1+mh)*(S.Rational(1,2)-mt))
assert D == -S.Rational(1,12)-S.Rational(4,3)*mh+S.Rational(3,2)*mt
assert D.subs({mh:mu0h,mt:mu0t}) == -S.Rational(20,351)
assert S.Rational(20,351)-S.Rational(17,60000)>0

s,t,L=S.symbols("s t L", real=True)
assert S.trigsimp(2*(S.cos((s-t)*L)+S.cos((-s-t)*L))
                      -4*S.cos(s*L)*S.cos(t*L))==0
r,A1,A2,e2,e3,L2,L3=S.symbols("r A1 A2 e2 e3 L2 L3",real=True)
change1=2*(e2*S.cos(r*L2)+e3*S.cos(r*L3))
change2=2*(e2*S.cos(2*r*L2)+e3*S.cos(2*r*L3))
ordinary=e2*(S.cos(2*r*L2)*A1*(1+change1)-S.cos(r*L2)*A2*(1+change2))
frozen=e2*(S.cos(2*r*L2)*A1-S.cos(r*L2)*A2)
assert S.Poly(S.expand(ordinary),e2,e3).total_degree()==2
assert S.Poly(S.expand(frozen),e2,e3).total_degree()==1
print("PASS exact corridor determinant and 4x Weil phase; frozen affine vs ordinary quadratic")

# Positive even C-infinity source bump and the original four-window geometry.
x,weight=np.polynomial.legendre.leggauss(160)
bx=np.exp(-1/(1-x*x))
bmass=float(np.dot(weight,bx));wx=weight*bx/bmass
bprime=-2*x/(1-x*x)**2
bprime2=-2/(1-x*x)**2-8*x*x/(1-x*x)**3
bsecondL1=float(np.dot(weight,np.abs(bx*(bprime2+bprime*bprime))))
width=.0035
centres=(0,np.pi/3,np.pi/2,np.pi)

def avg(c,k,f):
    up=c+width*x;down=-c+width*x
    return float(np.dot(wx, (up**k*f(up)+down**k*f(down))/2))

def mom(lam,mu,k,f):
    return sum(a*avg(c,k,f) for a,c in zip((1,-1,lam,mu),centres))

def am(lam,mu,k,s):
    return mom(lam,mu,k,lambda u:np.cos(s*u))

def J(lam,mu,k):
    return am(lam,mu,0,1)*am(lam,mu,k,2)-am(lam,mu,0,2)*am(lam,mu,k,1)

muH=brentq(lambda mu:J(.5,mu,2),float(mu0h)-.0001,float(mu0h)+.0001,xtol=1e-15)
muT=brentq(lambda mu:J(2/3,mu,2),float(mu0t)-.0001,float(mu0t)+.0001,xtol=1e-15)
assert abs(J(.5,muH,2))<1e-12 and abs(J(2/3,muT,2))<1e-12
assert J(.5,muH,4)<0 and J(2/3,muT,4)<0
F1=float(np.dot(wx,np.cos(width*x)));F2=float(np.dot(wx,np.cos(2*width*x)))
det=am(.5,muH,0,1)*am(2/3,muT,0,2)-am(.5,muH,0,2)*am(2/3,muT,0,1)
assert abs(det-F1*F2*float(D.subs({mh:muH,mt:muT})))<2e-13 and det<0
print("PASS true C-infinity fixture J2=0 and nonproportional smooth endpoints",
      "muH=",muH,"muT=",muT,"det=",det)

def A(lam,mu,rr):
    return am(lam,mu,0,1)/rr,am(lam,mu,0,2)/rr

def pole(lam,mu,tt):
    weight=lambda u,c:np.cosh(8*u/tt)*np.cos(16*u)*np.cos(c*u)
    w1=mom(lam,mu,0,lambda u:weight(u,1))
    w2=mom(lam,mu,0,lambda u:weight(u,2))
    return w1*am(lam,mu,0,2)-w2*am(lam,mu,0,1)

def shape(tt,lp,lam,mu):
    rr=tt/16;a1,a2=A(lam,mu,rr)
    return a1*np.cos(2*rr*lp)-a2*np.cos(rr*lp)

def source_weights(tt,u,lam,mu):
    rr=tt/16;a1,a2=A(lam,mu,rr)
    bg=a1*np.cos(2*rr*u)-a2*np.cos(rr*u)
    pp=np.cosh(u/2)*np.cos(tt*u)
    return np.vstack((np.cos(rr*u),np.cos(2*rr*u),
      u**2*bg,u**4*bg,u**6*bg,u**8*bg,
      pp*np.cos(rr*u),pp*np.cos(2*rr*u)))

def col(tt,c,delta,lam,mu,prime=False):
    val=source_weights(tt,c+delta*x,lam,mu)@wx
    return val*(2*delta*bmass*math.e if prime else 1.)

log2,log3=np.log(2),np.log(3)
aux=np.array([a for a in np.linspace(.25,1.35,29)
              if min(abs(a-log2),abs(a-log3))>.033])
assert len(aux)>=20 and .25<log2<log3<1.35<np.log(4)
record=[]
for tt in (300.,1000.,80000.,1000000.):
    rr=tt/16
    assert 16*(np.pi+width)/tt<.25  # core and two-scale shifts are disjoint
    poleH,poleT=pole(.5,muH,tt),pole(2/3,muT,tt)
    strength=poleT*(-J(.5,muH,4))-poleH*(-J(2/3,muT,4))
    assert poleH>0 and poleT>0 and strength>7*np.pi**4/1600
    delta=min(.0014,.14/tt)
    norm2=[]
    for endpoint,lam,mu in (("half",.5,muH),("two",2/3,muT)):
        matrix=np.column_stack([col(tt,c,delta,lam,mu) for c in aux])
        sig=np.linalg.svd(matrix,compute_uv=False)
        assert sig[-1]>1e-11*sig[0]
        for label,prime in (("2",log2),("3",log3)):
            port=col(tt,prime,delta,lam,mu,prime=True)
            coeff=np.linalg.lstsq(matrix,-port,rcond=1e-12)[0]
            residual=float(np.max(abs(matrix@coeff+port)))
            assert residual<5e-12
            # Triangle bound, not a certified optimal minimum:
            # port h'' L1 = 2*e*||b''||1/delta;
            # auxiliary normalised-even bump h'' L1 = ||b''||1/(mass*delta^2).
            d2=2*math.e*bsecondL1/delta+np.sum(abs(coeff))*bsecondL1/(bmass*delta**2)
            norm2.append(d2)
            record.append((tt,endpoint,label,residual,float(sig[0]/sig[-1]),d2))
    c2,c3=np.cos(tt*log2),np.cos(tt*log3)
    w2,w3=log2/np.sqrt(2),log3/np.sqrt(3)
    v=np.array((4*w2*c2*poleT*shape(tt,log2,.5,muH),
      -4*w2*c2*poleH*shape(tt,log2,2/3,muT),
      4*w3*c3*poleT*shape(tt,log3,.5,muH),
      -4*w3*c3*poleH*shape(tt,log3,2/3,muT)))
    assert max(abs(v))>1e-6
    eps=np.array([1e-6,-2e-6,3e-6,-1.5e-6])
    answer=eps@v
    independent=4*(w2*c2*(poleT*eps[0]*shape(tt,log2,.5,muH)
                      -poleH*eps[1]*shape(tt,log2,2/3,muT))
                 +w3*c3*(poleT*eps[2]*shape(tt,log3,.5,muH)
                      -poleH*eps[3]*shape(tt,log3,2/3,muT)))
    assert np.isclose(answer,independent,rtol=1e-10,atol=1e-13)
    assert np.isclose(-answer,(-eps)@v,rtol=1e-12,atol=1e-15)
    print("PASS t=",int(tt),"target=",round(strength,7),
      "prime slope max=",float(max(abs(v))),
      "P(eps)=",float(answer),"P(-eps)=",float(-answer),
      "worst ||h''||1 triangle=",float(max(norm2)))
assert len(record)==16
print("PASS 16 projected smooth-fixture ports; worst 8-residual=",max(x[3] for x in record),
      "worst conditioning=",max(x[4] for x in record))

# The source phases never vanish together, but irrational rotation makes them
# arbitrarily CLOSE to jointly zero. This is a genuine negative control for
# any claimed high-t uniform arithmetic gain. Values below are numerical;
# mathematical density follows from irrational log(3)/log(2).
import mpmath as mp
mp.mp.dps=65
for k,cap in ((485,mp.mpf('0.003')),(7800,mp.mpf('0.00005')),
              (39667,mp.mpf('0.00001'))):
    resonance=(mp.mpf(k)+mp.mpf('0.5'))*mp.pi/mp.log(2)
    phase2=mp.cos(resonance*mp.log(2))
    phase3=mp.cos(resonance*mp.log(3))
    assert abs(phase2)<mp.mpf('1e-55') and abs(phase3)<cap
    print("PASS near joint prime resonance k=",k,"t=",mp.nstr(resonance,17),
          "|cos(t log 3)|=",mp.nstr(abs(phase3),12))
print("OPEN no height-uniform phase floor; bound full signed completed source independently")

print("OPEN exact Mathlib witness carrier inhabitation, E2 high-tail, strict P0 signed bound; NO RH/GRH")
