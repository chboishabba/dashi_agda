#!/usr/bin/env python3
"""Backward consumer cut: oriented native cube, repaired D3, origin radical.

Classical: cube isometries, finite-group representations, exact linear
algebra. Original DASHI: KKSteelmanBIDIConsumerMaxCut20261024,
ConsumerDescentMinimalObserverExact, C3ReflectionCliffordPinBridgeExact,
Punctured27NineSheetBridgeExact, selected Tian-Yau Jacobian source.
User: infer the geometry backwards from the physical consumer, test
staggered punctures and central zero. New: exact third-moment collision,
full symmetry obstruction and actual multiplication-consumer quotient.
No identification of spatial moments with GR curvature, spin/fermion
chirality, physical Yukawas or internal gauge holonomy follows.
"""
from itertools import product, permutations, combinations_with_replacement
from pathlib import Path
import runpy
import sympy as s

T=(-1,0,1)
cube=set(product(T,repeat=3))
H={(-1,0,1),(0,1,-1),(1,-1,0)}
Hm={tuple(-a for a in p) for p in H}
n=s.ones(3,1)
x,y,z=s.symbols('x y z')
X=s.Matrix([x,y,z])
for A in (H,Hm):
    assert sum((s.Matrix(p) for p in A),s.zeros(3,1))==s.zeros(3,1)
    assert sum((s.Matrix(p)*s.Matrix(p).T for p in A),s.zeros(3))==3*s.eye(3)-n*n.T
p3=lambda A:s.expand(sum((s.Matrix(p).dot(X))**3 for p in A))
assert s.expand(p3(H)+3*(x-y)*(x-z)*(y-z))==0
assert p3(Hm)==-p3(H)
assert p3(cube-H)==-p3(H) and p3(cube-Hm)==-p3(Hm)
# The third moment is the lowest-degree homogeneous raw moment
# distinguishing the two; no claim of minimality among arbitrary queries.
stabilizer=[]
for perm in permutations(range(3)):
    for signs in product((-1,1),repeat=3):
        M=s.Matrix([[signs[i]*int(j==perm[i]) for j in range(3)] for i in range(3)])
        if {tuple(M*s.Matrix(p)) for p in H}==H:
            stabilizer.append(M)
assert len(stabilizer)==6 and all(M.det()==1 for M in stabilizer)
# All cube vertices survive; any Euclidean isometry of the retained set
# must preserve its cube convex hull. Thus this enumerates ALL isometries.
Wset=cube-H
assert all(p in Wset for p in product((-1,1),repeat=3))
half=lambda p:(-p[1],-p[0],-p[2])
assert {half(p) for p in Wset}==Wset
assert sum(half(p)==p for p in Wset)==2
print('PASS two mirror punctures: same degree 0/1/2 moments, opposite cubic')
print('PASS native stabilizer D3, all 6 isometries proper; half-turn trace 2')

# ORIGINAL selected equation source, not a substitute cohomology tensor.
d=runpy.run_path(str(Path(__file__).with_name('check_string369_tian_yau_jacobian_cubic_exact.py')))
data={i:(d['m'+str(i)],d['f'+str(i)],d['r'+str(i)]) for i in (1,2,3)}
B=d['B'];K=d['K'][0]
m1,f1,r1=data[1];m2,f2,r2=data[2];m3,f3,r3=data[3]
idx2={m:i for i,m in enumerate(m2)}
# Actual selected polynomial symmetries: simultaneous coordinate cycle,
# transposition, and exchange the two P3 factors and auxiliary u0,u1.
g=(0,3,1,2,4,7,5,6,8,9,10)
t=(0,2,1,3,4,6,5,7,8,9,10)
h=(4,5,6,7,0,1,2,3,9,8,10)
def act(p,i):
    ms,fs,rs=data[i];idx={m:j for j,m in enumerate(ms)}
    return s.Matrix.hstack(*(s.Matrix(rs[idx[tuple(ms[j][k] for k in p)]]) for j in fs))
for p,tr in [(g,(2,3,1)),(t,(7,8,1)),(h,(3,4,1)),(tuple(t[j] for j in h),(3,4,1))]:
    A,C,E=[act(p,i) for i in (1,2,3)]
    assert (A.trace(),C.trace(),E.trace())==tr
    assert A.T*B*C==E[0,0]*B and C*K==K
G2,T2=act(g,2),act(t,2)
assert G2**3==s.eye(24) and T2**2==s.eye(24) and T2*G2*T2==G2**2
assert T2.trace()==8 # native half-turn trace 2: no full-D3 intertwiner.
# Backward from perfect pairing: select the actual null line FIRST,
# then construct seven standard-plus-trivial triples and two poles.
E=(s.eye(24)+G2+G2**2)/3
plus=(s.eye(24)+T2)/2
res=[];pairs=[]
for e in ((s.eye(24)-E)*plus).columnspace():
    trial=res+[e,G2*e]
    if s.Matrix.hstack(*trial).rank()==len(trial):
        res=trial;pairs.append(e)
assert len(pairs)==7
fixed=[K];fixed_add=[]
for e in (E*plus).columnspace():
    if s.Matrix.hstack(*fixed,e).rank()==len(fixed)+1:
        fixed.append(e);fixed_add.append(e)
    if len(fixed_add)==7:break
assert len(fixed_add)==7
cols=[]
for a,e in zip(fixed_add,pairs):
    w=a+e
    cols.extend([w,G2*w,G2**2*w])
assert len(cols)==21 and s.Matrix.hstack(*cols,K).rank()==22
cols.append(K) # chosen origin, not a canonical geometric identification.
for e in (s.eye(24)+G2+G2**2).columnspace():
    even=(e+T2*e)/2
    if s.Matrix.hstack(*cols,even).rank()==23:break
else:raise AssertionError('even pole direction missing')
for e in (s.eye(24)+G2+G2**2).columnspace():
    odd=(e-T2*e)/2
    if s.Matrix.hstack(*cols,even,odd).rank()==24:break
else:raise AssertionError('odd pole direction missing')
cols.extend([even+odd,even-odd])
J2=s.Matrix.hstack(*cols)
Cyc=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
Rfl=s.Matrix([[1,0,0],[0,0,1],[0,1,0]])
Gm=s.diag(*([Cyc]*7),s.eye(3))
Tm=s.diag(*([Rfl]*7),s.Matrix([[1,0,0],[0,0,1],[0,1,0]]))
assert G2*J2==J2*Gm and T2*J2==J2*Tm
assert J2[:,21]==K and J2.det()!=0
assert J2.det()==-s.Rational(7756176246000,3123405356819)
# Delete only the designated origin coefficient. All Yukawa probes
# recover through the invertible pairing Q. Conversely equal probes
# force equal quotient coordinates. This is the linear instance of
# the original ConsumerDescentMinimalObserverExact theorem.
keep=list(range(21))+[22,23]
Q=B*J2[:,keep]
assert Q.det()!=0
q=J2.inv()[keep,:]
assert Q*q==B
# Actual raw multiplication map rank 24, not a fabricated cubic table.
mu=s.Matrix.hstack(*[s.Matrix(r2[idx2[tuple(a+b for a,b in zip(m1[f1[i]],m1[f1[j]]))]]) for i,j in combinations_with_replacement(range(23),2)])
assert mu.rank()==24
enc=J2.inv()*mu
assert J2*enc==mu
assert Q*enc[keep,:]==B*mu
assert sum(a!=0 for a in enc[21,:])==20
# The origin is invisible to every cubic consumer, but not to raw
# multiplication. Keep this single coefficient as codec side info.
print('PASS actual Jacobian traces C3=3 reflection=8, native half-turn non-isomorphic')
print('PASS exact repaired D3 basis, origin maps to radical and poles exchange')
print('PASS full multiplication rank 24; 23d minimal cubic quotient plus residual')
print('PASS origin residual appears in 20 of 276 selected raw products')
print('OPEN native physical action, geometric residue comparison, Wilson reflection lift, GRQFT')
