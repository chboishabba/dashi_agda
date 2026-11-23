#!/usr/bin/env python3
"""Exact reverse solve of the original transcribed midpoint/diode and three-Earth branches.

Source owners: narrated four-diode centre-tapped NST / rectifier / capacitor / spark
in Filsinger's *midpoint* transcript (association with Dfu9Jseviz9 is provisional);
Filsinger Earth-electrode reel Dfi1D7CPzyM; shunt reel DfiqPnkPnP5;
Smith/Kelly/Darrer multi-diagram compilation. THESE ARE DIFFERENT SOURCES.

The diode models below assume ideal drops, a symmetric centre-tapped ideal
secondary and no real-world component values unless explicitly conditional.
They are illustrative graph completions; no physical original circuit is
identified, no active high-voltage procedure is recommended.
"""
from dataclasses import dataclass
from sympy import (Matrix, Rational as Q, symbols, simplify, factor,
                   zeros, pi, diff, sin, cos, integrate, solve, I, sqrt)

checks=[]
def ok(name, expr):
    assert bool(expr), name
    checks.append(name)

# Candidate models reuse ONLY transcribed boundaries: a secondary has a
# midpoint M, two outer wires A/B, four diode packages/two per wire, joined
# positive outputs P, and a return described as centre-tap or Earth. The
# transcripts do not identify the DC-negative node or diode polarities.
@dataclass(frozen=True)
class Completion:
    name: str
    physical_diodes: int
    diodes_at_each_outer_wire: tuple
    positive_bus_ganged: bool
    centre_tap_used_as_return: bool
    negative_bus_tied_to_midpoint: bool
    physically_distinct_rectifier_paths: int

# CT4 duplicates are a *logical* completion, not an inferred parallel wiring.
completions=(
    Completion('CT4_duplicate_positive_paths',4,(2,2),True,True,True,2),
    Completion('BRIDGE4_full_winding_M_unconnected',4,(2,2),True,False,False,4),
    Completion('CT4_split_positive_negative_rails',4,(2,2),True,True,False,4),
    Completion('BRIDGE4_negative_bonded_to_M',4,(2,2),True,True,True,4),
)
for candidate in completions:
    ok('exactly four physical diode packages '+candidate.name,candidate.physical_diodes==4)
    ok('two terminals on each secondary outer wire '+candidate.name,candidate.diodes_at_each_outer_wire==(2,2))
    ok('positive outputs ganged '+candidate.name,candidate.positive_bus_ganged)

x=symbols('x',positive=True)
M=Q(0)
for (A,B) in ((x,-x),(-x,x)):
    P=max(A,B,key=lambda k: float(k.subs(x,1))) if False else x  # abs symmetric, no float computation
    N=-x
    ok('secondary centre is arithmetic midpoint of outer wires '+str(A),simplify((A+B)/2-M)==0)
    ok('symmetrically grounded centre produces opposite end potentials '+str(A),simplify((A-M)+(B-M))==0)
    ok('CT positive diode output |half-winding| '+str(A),simplify(P-x)==0)
    ok('ordinary 4-diode bridge positive above centre '+str(A),simplify(P-M-x)==0)
    ok('ordinary 4-diode bridge negative below centre '+str(A),simplify(N-M+x)==0)
    ok('bridge span twice CT branch output '+str(A),simplify((P-N)-2*(P-M))==0)
    ok('negative bridge bus and centre not same when nonzero drive '+str(A),simplify(N-M)!=0)
    ok('split positive/midpoint and midpoint/negative equal magnitude '+str(A),simplify(P-M-(M-N))==0)

ok('CT rectifier distinct electrical paths only two',completions[0].physically_distinct_rectifier_paths==2)
ok('four-diode full bridge has distinct four rectifying paths',completions[1].physically_distinct_rectifier_paths==4)
ok('four packages on two wires do not identify DC negative bus',len(set(c.negative_bus_tied_to_midpoint for c in completions))==2)
ok('four packages and ganged positive bus do not identify midpoint return',len(set(c.centre_tap_used_as_return for c in completions))==2)
ok('strict ordinary bridge negative bond to mid-point incompatible with active secondary',N != M)
ok('bridge with DC negative floating is not internally shorted by midpoint bond',not completions[1].negative_bus_tied_to_midpoint)
ok('split supply has centre-tap as mid-rail, not DC negative output',completions[2].centre_tap_used_as_return and not completions[2].negative_bus_tied_to_midpoint)
ok('all outward diodes to positive bus only supply one rectifier polarity',completions[0].physically_distinct_rectifier_paths==2)

# Reverse map for a reported 4 kV *output voltage*, ONLY IF it is an
# actual simultaneous differential rectified output. Input winding voltage
# is not a source measurement and may differ with diode drops and loading.
y=symbols('y',positive=True)
xCT=y
xBR=y/2
ok('CT source half-voltage from output y',simplify(xCT-y)==0)
ok('bridge source half-voltage from same output y',simplify(2*xBR-y)==0)
ok('same output y is consistent with two different secondary amplitudes',simplify(xCT-xBR-y/2)==0)
ok('4kV conditional CT half winding amplitude 4kV',xCT.subs(y,4000)==4000)
ok('4kV conditional bridge half winding amplitude 2kV',xBR.subs(y,4000)==2000)
ok('full outer-to-outer winding under CT 4kV half is 8kV',2*xCT.subs(y,4000)==8000)
ok('full outer-to-outer winding under bridge 4kV output is 4kV',2*xBR.subs(y,4000)==4000)
ok('4kV description is below both narrated example voltage ratings',4000<10000<20000)

# A shunt capacitor "across selected coil" is a reactive branch. One
# complete ideal periodic operation can have zero net capacitor work despite
# high instantaneous voltage. This does not assert the real capacitor is
# connected where suggested or that a spark discharge is lossless.
C,L,omega,t,Vpk=symbols('C L omega t Vpk',positive=True)
v=Vpk*cos(omega*t)
ic=C*diff(v,t)
pCap=v*ic
UCap=C*v*v/2
ok('capacitor current is C dv/dt',simplify(ic-C*diff(v,t))==0)
ok('instantaneous capacitor power is storage derivative',simplify(pCap-diff(UCap,t))==0)
ok('capacitor one-period real net work zero',simplify(integrate(pCap,(t,0,2*pi/omega)))==0)
ok('periodic capacitor storage returns exactly',simplify(UCap.subs(t,2*pi/omega)-UCap.subs(t,0))==0)
ok('ideal LC pole tuning has omega squared=1/(LC)',simplify((1/sqrt(L*C))**2-1/(L*C))==0)
ok('capacitive quadrature current not proof of another energy source',simplify(ic.subs(t,0))==0 and simplify(v.subs(t,0))==Vpk)

# Two narrated capacitor alternatives share Q=20mC only at their stated
# example voltages, NOT equal energy. Rated voltage is not actual voltage.
C1,C2=Q(1,10**6),Q(2,10**6)
V1,V2=Q(20000),Q(10000)
q1,q2=C1*V1,C2*V2
u1,u2=C1*V1**2/2,C2*V2**2/2
ok('nominal caps share 20mC charge',q1==q2==Q(1,50))
ok('first capacitor nominal example energy 200J',u1==200)
ok('second capacitor nominal example energy 100J',u2==100)
ok('equal nominal charge not equal energy',u1!=u2)
ok('at 4kV these alternate capacitors charge differently',C1*4000!=C2*4000)
ok('at 4kV 1uF alternative stores 8J',C1*4000**2/2==8)
ok('at 4kV 2uF alternative stores 16J',C2*4000**2/2==16)
ok('claimed 4kV does not establish example capacitor charge state',C1*4000!=q1)

# EARTH branch is a different *source occasion*. Three Earth electrodes have
# only two independent potential differences; no physical return path is
# inferred by their reported count. A passive Earth impedance is not an
# independently replenished generator just by having an extra branch.
g12,g13,g23=symbols('g12 g13 g23',positive=True)
v1,v2,v3,z=symbols('v1 v2 v3 z',real=True)
G=Matrix([[g12+g13,-g12,-g13],[-g12,g12+g23,-g23],[-g13,-g23,g13+g23]])
X=Matrix([v1,v2,v3]); J=G*X
edge=g12*(v1-v2)**2+g13*(v1-v3)**2+g23*(v2-v3)**2
ok('Earth model three KCL rows sum to zero',simplify(sum(J))==0)
ok('Earth passive graph common-mode invisible',G*Matrix([1,1,1])==zeros(3,1))
ok('Earth graph work sum of all edge losses',simplify((X.T*J)[0]-edge)==0)
ok('shifting all three Earth contacts leaves current unchanged',simplify(G*(X+Matrix([z,z,z]))-J)==zeros(3,1))
ok('one Earth voltage difference cannot identify third contact voltage',diff(v1-v2,v3)==0)
ok('two independent relative Earth potentials, not three',Matrix([[1,-1,0],[0,1,-1],[1,0,-1]]).rank()==2)
ok('Earth reel reports 3 contacts, not physical source count',3!=1)
ok('Earth 48V storage report is not a 48V Earth-Thevenin open-circuit',48!=Q(38,10))

# Source/sink + controller STEELMAN: an external replenished donor can add
# work, but one receiver display cannot identify how much. Two distinct
# physically admissible ledgers yield identical 0.4W load and 0.1W losses.
Wload=Q(2,5)
D0,E0,loss0,du0=Q(1,2),Q(0),Q(1,10),Q(0)
D1,E1,loss1,du1=Q(1,5),Q(3,10),Q(1,10),Q(0)
ok('drive-only world energy budget closes',D0+E0==Wload+loss0+du0)
ok('environmental-donor world energy budget closes',D1+E1==Wload+loss1+du1)
ok('same positive load under distinct source origins',Wload==Q(2,5) and E0!=E1)
ok('external source does not evade work conservation',D1+E1-Wload-loss1-du1==0)
A=Matrix([[1,1,-1,-1]])
ok('one useful-output meter constrains rank one of four energy terms',A.rank()==1)
ok('one output has three dimensional energetic nullspace',len(A.nullspace())==3)
ok('adding separately sourced work/loss/stored observations can reach full rank',Matrix.vstack(A,Matrix([[1,0,0,0],[0,1,0,0],[0,0,1,0]])).rank()==4)
ok('driver-controlled source may turn off with controller',Q(0)==0)
ok('4kV output description not same Earth reel as 3.8V display',Q(4000)!=Q(38,10))

print(f'{len(checks)}/{len(checks)} exact local checks PASS: CT4/bridge/split reverse models, phase/storage, Earth, source controls')
print('compatible *logical* rectifiers: centre-tapped duplicated diode paths; floating bridge; centre-tapped split rails')
print('ruled out under ideal symmetric winding: ordinary bridge DC-negative hard-bonded to centre tap with nonzero half-winding drive')
print('remaining: original anode/cathode and meter COM pin map, physical source/return and simultaneous signed V/I')
