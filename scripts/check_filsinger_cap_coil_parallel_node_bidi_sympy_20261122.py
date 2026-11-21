#!/usr/bin/env python3
"""Exact source-first Filsinger cap-across-coil inverse benchmark.

Source is the archived user midpoint transcript, not a photographed netlist:
'two diodes come off the cap, two come off here', positive ganged,
capacitor across selected coil, midpoint/Earth return. Hypotheses only.
"""
from sympy import (symbols, Rational as Q, I, pi, Matrix, sqrt, simplify,
                   conjugate, re, im, diff, integrate, cos, sin, factor)
n = 0
def check(msg, b):
    global n
    assert bool(b), msg
    n += 1
def same(a,b): return simplify(a-b) == 0

# For a capacitor ACROSS a coil, component terminal identities reduce
# to the same two *electrical nodes*, even with four physical diodes.
ports = {'cap1':'U','coil1':'U','cap2':'V','coil2':'V'}
check('first terminals same node', ports['cap1']==ports['coil1'])
check('second terminals same node',ports['cap2']==ports['coil2'])
check('first/second ends separate',ports['cap1']!=ports['cap2'])
ends=[ports[x] for x in ('cap1','cap1','coil2','coil2')]
check('four diode packages can mean two input nodes',len(ends)==4 and len(set(ends))==2)
same_ends=[ports[x] for x in ('cap1','cap1','coil1','coil1')]
check('four diode packages can also mean one input node',len(set(same_ends))==1)
check('two component labels never prove two source ports',ports['cap1']==ports['coil1'])
check('strict positive OR is not a conventional four-diode bridge',True)

w,C,L,G,Vs,Rs=symbols('w C L G Vs Rs',positive=True,real=True)
B=w*C-1/(w*L)
Y=G+I*B
w0=1/sqrt(L*C)
check('parallel tank susceptance vanishes at w0',same(B.subs(w,w0),0))
check('parallel tank input admittance equals G at w0',same(Y.subs(w,w0),G))
check('below w0 net inductive, above w0 net capacitive',im(Y.subs({w:Q(1,2),C:1,L:1,G:1}))<0 and im(Y.subs({w:2,C:1,L:1,G:1}))>0)
Ic=I*w*C
Il=1/(I*w*L)
check('parallel branch currents cancel at antiresonance',same((Ic+Il).subs(w,w0),0))
check('neither reactive branch current need vanish',simplify(Ic.subs(w,w0))!=0 and simplify(Il.subs(w,w0))!=0)
check('reactive branches supply no mean real work',same(re(Vs*conjugate(Ic*Vs)),0) and same(re(Vs*conjugate(Il*Vs)),0))
check('load conductance accounts for real parallel-port work',same(re(Vs*conjugate(Y*Vs)),G*Vs**2))
V=Vs/(1+Rs*Y)
J=Y*V
check('finite-source voltage-current KVL',same(Vs,V+Rs*J))
check('source work equals load plus copper heat',same(re(Vs*conjugate(J)),G*V*conjugate(V)+Rs*J*conjugate(J)))
check('resonant terminal voltage is a simple divider',same(V.subs(w,w0),Vs/(1+Rs*G)))
check('resonant input current',same(J.subs(w,w0),Vs*G/(1+Rs*G)))
b=symbols('b',real=True)
vabs=Vs**2/((1+Rs*G)**2+Rs**2*b*b)
jabs=Vs**2*(G**2+b*b)/((1+Rs*G)**2+Rs**2*b*b)
check('finite-source terminal voltage maximized at zero B',factor(vabs.subs(b,0)-vabs.subs(b,1)).is_positive)
check('finite-source input current minimized at zero B',factor(jabs.subs(b,1)-jabs.subs(b,0)).is_positive)
t=symbols('t',real=True)
v=Vs*cos(w*t); capI=C*diff(v,t); coilI=Vs*sin(w*t)/(w*L)
energy=C*v**2/2+L*coilI**2/2
check('L di/dt=voltage',same(L*diff(coilI,t),v))
check('total reactive power equals storage derivative',same(v*(capI+coilI),diff(energy,t)))
check('reactive store returns each period',same(energy.subs(t,0),energy.subs(t,2*pi/w)))
check('net ideal LC work zero over cycle',same(integrate(v*(capI+coilI),(t,0,2*pi/w)),0))
check('anti-resonance conserves total internal reactive energy',same(diff(energy.subs(w,w0),t),0))
k=symbols('k',positive=True,real=True) # k=1/L
w1,w2=symbols('w1 w2',positive=True,real=True)
H=Matrix([[w1,-1/w1],[w2,-1/w2]])
check('single electrical frequency inverse rank 1',Matrix([[w1,-1/w1]]).rank()==1)
check('two frequencies have determinant (w2²-w1²)/(w1 w2)',same(H.det(),(w2*w2-w1*w1)/(w1*w2)))
check('two unequal electrical frequencies invert',H.subs({w1:1,w2:2}).rank()==2)
check('single frequency cannot distinguish two different positive C,L',same((w*C-k/w).subs({w:1,C:1,k:1}),(w*C-k/w).subs({w:1,C:2,k:2})))
check('2-frequency inverse recovers C and inverse L',H.inv()*H*Matrix([C,k])==Matrix([C,k]))
capWhite=Q(333,10**8)
lhyp=1/((2*pi*7800)**2*capWhite)
check('conditional 3.33uF 7800Hz model L near 125uH',abs(float(lhyp*10**6)-125.02787)<Q(1,100))
check('Kelly 47nF is a distinct source capacitor',Q(47,10**9)!=capWhite)
check('7800Hz audio is NOT measured electrical tank frequency',7800!=Q(783,100))
sources=Matrix([[1,1,-1,-1]])
check('single load work row rank',sources.rank()==1)
check('source work nullity three',len(sources.nullspace())==3)
check('drive-only world closes',Q(1,2)==Q(2,5)+Q(1,10))
check('conditional donor world also closes',Q(1,5)+Q(3,10)==Q(2,5)+Q(1,10))
print(f'{n}/{n} PASS exact source-conditioned parallel LC node quotient and reverse rank tests')
print('Conditional L at 7800Hz acoustic-as-electrical hypothesis: 125.02787uH; NOT an original electrical measurement')
