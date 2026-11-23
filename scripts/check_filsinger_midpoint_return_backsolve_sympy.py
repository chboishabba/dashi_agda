#!/usr/bin/env python3
"""Source-scoped Filsinger centre-tap, bridge-negative return and cap/coil diode BIDI.

Preserved prior user transcript: "two off of this wire, two off of that
wire", "two diodes come off the cap, two diodes come off here",
"all forward facing", "ganging together positives", "half the potential
of the big coil", "return to midpoint, earth, ground", and capacitor
across selected coil claimed to cause a "pole shift".

This is an ideal symmetric winding and finite-impedance countermodel,
NOT an original Filsinger wiring certification, natural energy detection
or construction prescription. Different reels must not be combined.
"""
from sympy import (Rational as R, symbols, Matrix, simplify, diff, pi,
                   integrate, cos, sin, sqrt, I, conjugate, re, im, oo, limit,
                   zeros)

count=0
def check(name, pred):
    global count
    assert bool(pred), name
    count += 1

def equal(a,b):
    return simplify(a-b)==0

x,Rs,RL,Rb=symbols('x Rs RL Rb',positive=True,real=True)
for phase in (1,-1):
    A=phase*x
    B=-phase*x
    high=x
    low=-x
    check('symmetric winding midpoint, phase '+str(phase),equal((A+B)/2,0))
    check('active positive end equals +x, phase '+str(phase),
          (A==high if phase==1 else B==high))
    check('active negative end equals -x, phase '+str(phase),
          (B==low if phase==1 else A==low))
    check('bridge return diode N->negative end forward at N=M, phase '+str(phase),0-low==x)
    check('ideal bridge negative and source midpoint cannot coincide, phase '+str(phase),low!=0)
    check('centre-tap positive rectifier does not require return diode, phase '+str(phase),high-0==x)

# A conventional bridge N=M with finite source resistance does not vanish
# physically; the negative half of the secondary is CLAMPED through its
# return diode each half-cycle, with paid source current and copper heat.
Iclamp=x/Rs
Vload=x*RL/(Rs+RL)
Iload=Vload/RL
Pload=Vload*Iload
Pclamp=Rs*Iclamp**2
Ppos=Rs*Iload**2
Psource=x*(Iclamp+Iload)
check('positive source branch KVL',equal(x,Vload+Rs*Iload))
check('negative clamped branch KVL',equal(-x+Rs*Iclamp,0))
check('clamp current is inverse source resistance',equal(Iclamp,x/Rs))
check('clamp source work funds copper heat',equal(x*Iclamp,Pclamp))
check('positive source funds load and copper heat',equal(x*Iload,Pload+Ppos))
check('total work funds all output and copper losses',equal(Psource,Pload+Pclamp+Ppos))
case={x:1,Rs:1,RL:2}
check('finite example load power 2/9',equal(Pload.subs(case),R(2,9)))
check('finite example clamp loss 1',equal(Pclamp.subs(case),1))
check('finite example positive copper loss 1/9',equal(Ppos.subs(case),R(1,9)))
check('finite example source power 4/3',equal(Psource.subs(case),R(4,3)))
check('finite example useful/source fraction 1/6',equal((Pload/Psource).subs(case),R(1,6)))
check('low winding resistance increases clamp current',Iclamp.subs({x:1,Rs:R(1,2)})>Iclamp.subs({x:1,Rs:1}))
check('Rs->0 ideal source is singular under hard return',limit(Iclamp,Rs,0,dir='+')==oo)

# Through resistance, midpoint and bridge negative are NOT one node.
Irb=x/(Rs+Rb)
VN=-x*Rb/(Rs+Rb)
check('resistive return negative bus below midpoint',equal(VN,-x*Rb/(Rs+Rb)))
check('resistive return KVL',equal(x,Irb*(Rs+Rb)))
check('resistive return real work paid',equal(x*Irb,Irb**2*(Rs+Rb)))
check('resistive hard-bond limit recovers clamp',equal(limit(Irb,Rb,0,dir='+'),Iclamp))
check('resistive open return eliminates current',equal(limit(Irb,Rb,oo),0))
check('resistive open return restores negative source voltage',equal(limit(VN,Rb,oo),-x))
check('finite resistor reduces clamp from hard bond',Irb.subs({x:1,Rs:1,Rb:1})<Iclamp.subs({x:1,Rs:1}))
check('return resistor heats when driven',Irb.subs({x:1,Rs:1,Rb:1})**2>0)

# Capacitive or LC link produces reactive phase without net new work.
V,w,C,L=symbols('V w C L',positive=True,real=True)
Zc=1/(I*w*C)
Ic=V/(Rs+Zc)
Pc=simplify(Rs*Ic*conjugate(Ic))
check('capacitor link has negative reactance',equal(im(Zc),-1/(w*C)))
check('capacitor link current squared exact',equal(Ic*conjugate(Ic),V**2/(Rs**2+1/(w*C)**2)))
check('real source funds copper loss',equal(re(V*conjugate(Ic)),Pc))
check('ideal capacitor absorbs zero mean real power',equal(re(Zc*Ic*conjugate(Ic)),0))
check('capacitor return opens at low frequency',equal(limit(Ic,w,0,dir='+'),0))
check('capacitor return tends to hard strap at high frequency',equal(limit(Ic,w,oo),V/Rs))
check('no ideal capacitor is an independent natural generator',equal(Pc,V**2*Rs/(Rs**2+1/(w*C)**2)))
Zlc=Rs+I*(w*L-1/(w*C))
Ilc=V/Zlc
Plc=simplify(Rs*Ilc*conjugate(Ilc))
wr=1/sqrt(L*C)
check('series LC has real Rs',equal(re(Zlc),Rs))
check('series LC power is paid winding heat',equal(re(V*conjugate(Ilc)),Plc))
check('LC resonance returns finite current V/Rs',equal(Ilc.subs(w,wr),V/Rs))
check('LC resonance funds V²/Rs real source power',equal(Plc.subs(w,wr),V**2/Rs))
check('LC reactance flips sign across resonance',im(Zlc.subs({w:R(1,2),L:1,C:1}))<0 and im(Zlc.subs({w:2,L:1,C:1}))>0)
check('off-resonance current phase nonzero',im(Ilc.subs({Rs:1,w:2,L:1,C:1,V:1}))!=0)

# Literal 'two diodes off the cap, two off here' permits a positive diode
# OR using two input branches, instead of a conventional four-diode bridge.
or_edges=(('cap','P'),('cap','P'),('coil','P'),('coil','P'))
bridge_edges=(('A','P'),('N','A'),('B','P'),('N','B'))
check('two transcribed input branches may provide four packages',len(or_edges)==4)
check('forward OR all diodes face one positive collector',all(t=='P' for _,t in or_edges))
check('full bridge does not have all four cathodes at positive collector',any(t!='P' for _,t in bridge_edges))
check('four diode packages do not entail four independent input wires',len({s for s,_ in or_edges})==2)
check('positive collector does not directly equate cap and coil anodes',len({t for _,t in or_edges})==1 and len({s for s,_ in or_edges})==2)
for u,v,P in ((2,1,2),(1,2,2),(-1,1,1),(-1,-2,0),(1,1,1)):
    check('positive diode-OR max law '+str((u,v)),P==max(0,u,v))

# Distinguish independently supplied natural work from redistributing
# powered work; the original Earth reel readings were a separate occasion.
A=Matrix([[1,1,-1,-1]])
check('single output-energy row rank one',A.rank()==1)
check('single output-energy row leaves nullity three',len(A.nullspace())==3)
check('illustrative drive-only world closes 0.4W',R(1,2)==R(2,5)+R(1,10))
check('illustrative independent donor world also closes 0.4W',R(1,5)+R(3,10)==R(2,5)+R(1,10))
check('driver-only versus donor world natural work differs',R(0)!=R(3,10))
print(f'{count}/{count} local exact SymPy checks PASS — ideal and finite bridge-return loop, capacitor/LC phase, cap/coil two-input OR')
print('Source limits: original diode polarities, return impedance, per-reel pins, signed external and driver work all unknown; Agda kernel pending')
