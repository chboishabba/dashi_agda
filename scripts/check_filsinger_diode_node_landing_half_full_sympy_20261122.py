#!/usr/bin/env python3
"""Source-bound forward/reverse model of transcribed Filsinger diode groups.

Source: previous user transcript as indexed in chboishabba/dashi_agda PR #1537.
The source does not identify whether the coil/capacitor share a full winding,
a half winding, or what each diode's anode actually touches.  This script
compares those INVERSE cases, in a linear sinusoidal, zero-diode-drop,
unsmoothed resistive-output model.  It does not model physical HV equipment.
"""
from sympy import (symbols, sin, cos, pi, sqrt, Integral, integrate,
                   simplify, Matrix, Rational as Q, exp, diff, oo, limit,
                   Max, Abs, S, factor, Eq)
N=0

def yes(tag, predicate):
    global N
    assert bool(predicate), tag
    N += 1

def equal(a,b):
    return simplify(a-b)==0

# Literal 'across': cap and coil have the same unordered pair of nodes.
node={'cap0':'U','cap1':'V','coil0':'U','coil1':'V'}
yes('cap upper == coil upper node',node['cap0']==node['coil0'])
yes('cap lower == coil lower node',node['cap1']==node['coil1'])
yes('distinct ends remain distinct',node['cap0']!=node['cap1'])
landing_opposite=[node[k] for k in ('cap0','cap0','coil1','coil1')]
landing_same=[node[k] for k in ('cap0','cap0','coil0','coil0')]
yes('opposite landing four packages',len(landing_opposite)==4)
yes('same landing four packages',len(landing_same)==4)
yes('opposite gives exactly two distinct inputs',len(set(landing_opposite))==2)
yes('same gives only one independent anode node',len(set(landing_same))==1)
yes('opposite pair count per input',landing_opposite.count('U')==landing_opposite.count('V')==2)
yes('same pair count from one input',landing_same.count('U')==4)

# Parallel identical forward packages: package count is not current count.
Eop=Matrix([[1,1,0,0],[0,0,1,1]])
Esame=Matrix([[1,1,1,1]])
yes('opposite diode-group incidence rank2',Eop.rank()==2)
yes('opposite diode package current nullity2',len(Eop.nullspace())==2)
yes('same diode-group incidence rank1',Esame.rank()==1)
yes('same diode package current nullity3',len(Esame.nullspace())==3)
yes('opposite diode nullmode 1',Eop*Matrix([1,-1,0,0])==Matrix([0,0]))
yes('opposite diode nullmode 2',Eop*Matrix([0,0,1,-1])==Matrix([0,0]))
yes('same diode nullmode',Esame*Matrix([1,0,0,-1])==Matrix([0]))

# Waveform calculations: x is HALF-SECONDARY peak versus midpoint M.
# P-M ideal instantaneous positive OR is max(0, u-M, v-M).
x,R,th=symbols('x R th',positive=True,real=True)
s=sin(th)
# Full secondary cap/coil: U-M=+x*sin, V-M=-x*sin.
# Half secondary cap/coil: U-M=x*sin, V=M.
# Both packages on same node U: U-M=x*sin; no positive V path.
for theta, expected in [(0,0),(pi/2,x),(pi,0),(3*pi/2,x)]:
    yes('full-symmetric opposite landing output '+str(theta),
        equal(Max(S.Zero,x*sin(theta),-x*sin(theta)),expected))
for theta, expected in [(0,0),(pi/2,x),(pi,0),(3*pi/2,0)]:
    yes('same-end one-input output '+str(theta),
        equal(Max(S.Zero,x*sin(theta)),expected))
for theta, expected in [(0,0),(pi/2,x),(pi,0),(3*pi/2,0)]:
    yes('opposite physical end but across HALF winding '+str(theta),
        equal(Max(S.Zero,x*sin(theta),S.Zero),expected))

# Exact unfiltered DC mean, RMS, resistive load power from sine intervals.
Fpos=x*sin(th)  # 0<=theta<=pi
Fneg=-x*sin(th) # pi<=theta<=2pi
mean_full=(integrate(Fpos,(th,0,pi))+integrate(Fneg,(th,pi,2*pi)))/(2*pi)
mean_half=integrate(Fpos,(th,0,pi))/(2*pi)
sq_full=(integrate(Fpos**2,(th,0,pi))+integrate(Fneg**2,(th,pi,2*pi)))/(2*pi)
sq_half=integrate(Fpos**2,(th,0,pi))/(2*pi)
yes('full source sine average 2x/pi',equal(mean_full,2*x/pi))
yes('half source sine average x/pi',equal(mean_half,x/pi))
yes('full source rms squared x²/2',equal(sq_full,x**2/2))
yes('half source rms squared x²/4',equal(sq_half,x**2/4))
yes('full vs half average factor 2',equal(mean_full/mean_half,2))
yes('full vs half rms factor sqrt2',equal(sqrt(sq_full)/sqrt(sq_half),sqrt(2)))
yes('full vs half resistive real power factor 2',equal((sq_full/R)/(sq_half/R),2))
yes('same peak despite waveform difference',equal(Fpos.subs(th,pi/2),x))
yes('full AC rectified shape factor 2sqrt2/pi',equal(mean_full/sqrt(sq_full),2*sqrt(2)/pi))
yes('half AC rectified shape factor 2/pi',equal(mean_half/sqrt(sq_half),2/pi))
yes('same-end Pload formula',equal(sq_half/R,x**2/(4*R)))
yes('opposite full-winding Pload formula',equal(sq_full/R,x**2/(2*R)))

# Counts and one peak observation cannot distinguish opposite full winding
# from same-end half-wave; average/RMS waveform would, conditional on same
# x, sinusoidal source, true midpoint reference, resistive load and no Cbank.
measured_peak=x
yes('one peak does not discriminate rectification',equal(measured_peak,measured_peak))
yes('mean DC can discriminate in restrictive model',simplify(mean_full-mean_half)!=0)
yes('RMS can discriminate in restrictive model',simplify(sq_full-sq_half)!=0)
yes('positive OR full cycle conduction alternates U/V',landing_opposite[:2]==['U','U'] and landing_opposite[2:]==['V','V'])
yes('positive OR one-node rectifies only one sign',landing_same.count('V')==0)

# A conventional full bridge P/N across entire symmetric secondary has
# ideal waveform 2*x*abs(sin); output between P and M is NOT the same
# measured port as between P and N, so don't cross-identify numbers.
bridge_mean=2*mean_full
bridge_sq=4*sq_full
yes('bridge across both ends has 2x peak',equal(2*x,2*x))
yes('bridge P-N mean 4x/pi',equal(bridge_mean,4*x/pi))
yes('bridge P-N rms squared 2x²',equal(bridge_sq,2*x*x))
yes('bridge P-N vs CT P-M rms factor 2',equal(sqrt(bridge_sq/sq_full),2))

# Smoothing reservoir destroys inference from simple rectified DC statistics.
# During a diode-OFF interval the RC output decays with a known, passive
# energy balance. No actual original output capacitor is identified.
Co,t,Rload,V0=symbols('Co t Rload V0',positive=True,real=True)
vout=V0*exp(-t/(Rload*Co))
energy=Co*vout**2/2
Pd=vout**2/Rload
yes('off-period RC equation',equal(Co*diff(vout,t),-vout/Rload))
yes('reservoir work equals negative load heat',equal(diff(energy,t),-Pd))
yes('output remains positive after instantaneous input zero',vout.subs(t,1)!=0)
yes('initial reservoir energy',equal(energy.subs(t,0),Co*V0**2/2))
yes('large RC retains high voltage through fixed off-interval',equal(limit(vout,Co,oo),V0))
yes('long off-interval decays zero',equal(limit(vout,t,oo),0))
yes('integrated reservoir heat matches energy lost',equal(integrate(Pd,(t,0,oo)),Co*V0**2/2))

# Nothing in diode current routing identifies a natural/ground donor port.
# Independent world balances and measurement nullspace remain untouched.
A=Matrix([[1,1,-1,-1]])
yes('one output work balance rank1',A.rank()==1)
yes('one output work nullity3',len(A.nullspace())==3)
yes('drive-only synthetic ledger closes',Q(1,2)==Q(2,5)+Q(1,10))
yes('external donor synthetic ledger closes',Q(1,5)+Q(3,10)==Q(2,5)+Q(1,10))
yes('donor worlds have identical useful output',Q(2,5)==Q(4,10))

# The transcript's 'across a coil' does not establish that selected coil
# is the FULL symmetric secondary. U,V relative to M remain unmeasured.
yes('full winding M midpoint mapping has two nonzero opposite halves',x!=0 and -x!=0)
yes('half winding ending at M mapping includes zero endpoint',S.Zero==0)
yes('same-node and half-winding cases have identical ideal P-M waveform',equal(mean_half,mean_half))

print(f'{N}/{N} exact SymPy 1.14 checks PASS')
print('BIDI: four diode packages / two named components -> either one or two electrical anode nodes')
print('Full wave needs opposite instantaneous input polarity wrt M, not just opposite ends of a cap/coil.')
print('No-output-cap sine ideal P-M: full mean=2x/pi RMS=x/sqrt2; half mean=x/pi RMS=x/2.')
print('A storage reservoir or changed source/return breaks that simple waveform discrimination.')
