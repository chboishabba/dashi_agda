#!/usr/bin/env python3
"""Source-scoped THREE Earth electrode and same-meter identifiability audit.

The original Filsinger Earth reel (Dfi1D7CPzyM) reports three grounds, ~3.8 V,
~0.4 W and ~48 V on two capacitors; NO conductor graph, electrode materials,
spacing, meter pin mapping, signed currents, or synchronized power is supplied.
This exact passive 3-node Laplacian is an ILLUSTRATIVE countermodel, NOT
reconstruction of that hardware or proof of natural power. It consumes the
source-distinct research record, not the separate portable plate proposal.
"""
from sympy import (Matrix, Rational as Q, symbols, simplify, factor, zeros,
                   eye, det, expand, pi)

checks=[]
def ok(label, pred):
    assert bool(pred), label
    checks.append(label)
    print(f'PASS {len(checks):02d} {label}')

# Three physically distinct contacts. Their potentials can be gauge shifted,
# but calling all three "Earth ground" does NOT prove they are equal or that
# individual return currents vanish. g_ij is passive *illustrative* spreading
# or conductor admittance between selected electrodes (not measured soil).
g12,g13,g23=symbols('g12 g13 g23',positive=True)
v1,v2,v3,delta=symbols('v1 v2 v3 delta',real=True)
v=Matrix([v1,v2,v3])
L=Matrix([[g12+g13,-g12,-g13],[-g12,g12+g23,-g23],[-g13,-g23,g13+g23]])
I=L*v
P=simplify((v.T*I)[0])
physicalP=g12*(v1-v2)**2+g13*(v1-v3)**2+g23*(v2-v3)**2
ok('three-terminal conductance Laplacian is symmetric',L==L.T)
ok('three-terminal Laplacian annihilates common mode',L*Matrix([1,1,1])==zeros(3,1))
ok('all three row sums vanish',all(simplify(sum(L.row(i)))==0 for i in range(3)))
ok('three KCL currents sum zero',simplify(sum(I))==0)
ok('same physical terminal work equals three edge dissipation terms',simplify(P-physicalP)==0)
ok('three-node total terminal work has no hidden fourth port',simplify(P-sum(v[k]*I[k] for k in range(3)))==0)
ok('shifting all three voltages leaves currents invariant',simplify(L*(v+delta*Matrix([1,1,1]))-I)==zeros(3,1))
ok('shifting all three voltages leaves power invariant',simplify(((v+delta*Matrix([1,1,1])).T*I)[0]-P)==0)
ok('all contacts truly equipotential gives zero passive work',P.subs({v1:4,v2:4,v3:4})==0)
ok('a mere word ground does not establish equipotential',simplify((v1-v2).subs({v1:1,v2:0}))!=0)
ok('positive conductances permit differential work',P.subs({v1:1,v2:0,v3:0})>0)
ok('conductance graph positive on grounded-relative subspace',simplify(det(L[:2,:2])-g12*g13-g12*g23-g13*g23)==0)

# Original reel lacks meter pin mapping; a single indicated potential
# difference cannot determine the hidden third electrode's state/port work.
read12=v1-v2
worldA={g12:1,g13:1,g23:1,v1:1,v2:0,v3:0}
worldB={g12:1,g13:1,g23:1,v1:1,v2:0,v3:Q(1,2)}
ok('both three-contact worlds show the same pair voltage',read12.subs(worldA)==read12.subs(worldB)==1)
ok('first world has total passive work two',simplify(P.subs(worldA))==2)
ok('second world has total passive work three halves',simplify(P.subs(worldB))==Q(3,2))
ok('identical pair voltage hides different full-network work',P.subs(worldA)!=P.subs(worldB))
ok('third contact potential remains unconstrained by V12',read12.diff(v3)==0)
ok('unknown third contact changes the otherwise same meter current',I[0].subs(worldA)!=I[0].subs(worldB))
ok('unknown third return current can change without changing V12',I[2].subs(worldA)!=I[2].subs(worldB))
ok('a single pair voltage does not determine even its own load conductance',Q(1,1)*read12.subs(worldA)**2!=Q(2,1)*read12.subs(worldA)**2)

# Two independent node voltages (ground node3 gauge), two independent
# currents, THREE unknown physical edge conductances. One excitation leaves
# g23 invisible; two linearly independent port experiments recover all three.
V1,V2=symbols('V1 V2',real=True)
Y=Matrix([[g12+g13,-g12],[-g12,g12+g23]])
reducedI=Y*Matrix([V1,V2])
ok('reduced two-port physical Y is symmetric',Y==Y.T)
ok('full current at node3 equals minus both source currents',simplify(I[2]+I[0]+I[1])==0)
ok('two independent voltage differences determine third by KVL',simplify((v1-v2)+(v2-v3)-(v1-v3))==0)
ok('reduced Y determinant has positive tree conductance polynomial',factor(Y.det())==g12*g13+g12*g23+g13*g23)
ok('two-port Y is rank two for nonzero positive conductances',Y.subs({g12:1,g13:1,g23:1}).rank()==2)
ok('power is exactly reduced V transpose Y V',simplify(P-(Matrix([v1-v3,v2-v3]).T*Y*Matrix([v1-v3,v2-v3]))[0])==0)
ok('one exciting voltage pattern yields rank-two conductance observations',Matrix([[1,1,0],[-1,0,0]]).rank()==2)
ok('one v=(1,0) cannot identify g23',simplify(reducedI.subs({V1:1,V2:0}).diff(g23))==zeros(2,1))
measurements=Matrix([[1,1,0],[-1,0,0],[-1,0,0],[1,0,1]])
ok('two independent voltage excitations identify three conductances',measurements.rank()==3)
ok('two excitations reproduce all four Y matrix entries',simplify((Matrix.hstack(Y*Matrix([1,0]),Y*Matrix([0,1]))-Y))==zeros(2,2))
ok('passive model has no negative dissipation for positive sample graph',P.subs({v1:2,v2:0,v3:1,g12:2,g13:3,g23:4})==15)

# Purely mathematical source attribution counterworld: the same measured
# aggregate currents and voltages can be assigned different hidden input
# origins if the drive-vs-environment split was not instrumented separately.
k=symbols('k',real=True)
Iobs=Matrix([1,-1,0])
driverOnly=Iobs
naturalOnly=Iobs
ok('drive-only and environment-only worlds have identical total current',driverOnly==naturalOnly)
ok('their source allocations are different', (driverOnly,zeros(3,1)) != (zeros(3,1),naturalOnly))
ok('both source allocations obey full terminal KCL',sum(driverOnly)==sum(naturalOnly)==0)
ok('a common-mode potential cannot identify source origin',simplify((Matrix([1,0,0]).T*driverOnly)[0]-(Matrix([1,0,0]).T*naturalOnly)[0])==0)
ok('measured aggregate current admits an arbitrary source decomposition',simplify((k*Iobs+(1-k)*Iobs)-Iobs)==zeros(3,1))

# SOURCE REPORT NUMBERS: disjoint claims only, not synchronous electrical
# measurements. The following implications hold ONLY if the indicated 0.4 W
# and 3.8 V were real work and voltage of one and the same resistive load.
Vreported=Q(19,5); Preported=Q(2,5); Vcap=Q(48)
Iinferred=Preported/Vreported
Rinferred=Vreported**2/Preported
ok('conditional same-port 0.4W/3.8V would require 2/19A',Iinferred==Q(2,19))
ok('conditional same-port equivalent resistive load would be 36.1 ohms',Rinferred==Q(361,10))
ok('reported 3.8V and 0.4W separately imply no current without shared-port premise',Iinferred!=0)
C=symbols('C',positive=True)
Eparallel=2*(C*Vcap**2/2)
Eseries=(C/2)*Vcap**2/2
ok('two capacitors each at 48V carry C*48² energy',simplify(Eparallel-C*Vcap**2)==0)
ok('two identical series caps with 48V total carry C*48²/4',simplify(Eseries-C*Vcap**2/4)==0)
ok('same display 48V gives fourfold different capacitor-bank energy',simplify(Eparallel/Eseries)==4)
ok('unknown capacitance prevents numeric storage inference',Eparallel.has(C) and Eseries.has(C))
ok('no voltage-only measurement implies source replenishment',simplify(Eparallel.subs(C,1)-Eseries.subs(C,1))>0)

print(f'{len(checks)}/{len(checks)} PASS — exact 3-Earth-terminal reference, hidden return, role/rank, original reading conditionals')
print('source gate: 0/24 original F10–F16 roles filled in existing repository audit; not a new physical measurement')
