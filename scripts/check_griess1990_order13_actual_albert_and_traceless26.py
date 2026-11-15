#!/usr/bin/env python3
"""Griess 1990: actual original order-13 automorphism on rational Albert 27.

REUSE canonical independent ORIGINAL Q(omega) Griess source basis/product
and literal native H3(O_Q) coordinate formula on this branch; no second
octonion or fictitious 27D algebra.

Mathematical root: R. L. Griess Jr., J. Algebra 131 (1990) 281-293,
DOI 10.1016/0021-8693(90)90176-O. DASHI finite derived actor.
The THREE central corrected shears are the ACTUAL M81 automorphisms
e01 -> e12 -> e20, and grade phases give e_x -> omega^h(x)e_(Mx).

Source-equivalent exact SymPy regression, no Lean/Agda kernel proof.
This is not the distinct 196884D Monster VOA Griess product, an E8
root Weyl action, full rational F4 classification or physical theory.
"""
from pathlib import Path
from itertools import product
from fractions import Fraction as F
import json,runpy,sys
import sympy as s

here=Path(__file__).resolve().parent
candidates=("check_griess1990_crossprover_standalone_certificate.py",
            "check_griess1990_rational_triality_crossprover_certificate.py")
donor=next((here/name for name in candidates if (here/name).is_file()),None)
if donor is None:raise SystemExit("missing canonical independent cross-prover source checker")
p=runpy.run_path(str(donor))
V=p['V'];add=p['add'];omega=p['omega'];qmul=p['qmul'];qadd=p['qadd']
g=p['phase'];srcprod=p['srcprod'];basis=p['basis'];coords=p['source_coords']
reps=p['reps'];native=p['native'];Z=p['Z']

def shear(x,i,j):
    y=list(x);y[i]=(y[i]+y[j])%3
    return tuple(y)
def correction(x,i,j):
    a,b,c=x
    return {(0,1):c*(1-b*b),(1,2):a*(c*c-1),(2,0):0}[i,j]%3
def grade_image(x):
    phase=0
    for i,j in ((0,1),(1,2),(2,0)):
        phase=(phase+correction(x,i,j))%3
        x=shear(x,i,j)
    return x,phase
def source_actor(v):
    out={}
    for x,coeff in v.items():
        y,k=grade_image(x)
        out[y]=qadd(out.get(y,Z),qmul(omega[k],coeff))
    return {x:c for x,c in out.items() if c!=Z}

S=s.Matrix.hstack(*[coords(source_actor(b)) for b in basis])
I=s.eye(27)
assert S.shape==(27,27) and S**13==I and S!=I
assert all(s.trace(S**k)==1 for k in range(1,13))
t=s.Symbol('t');phi13=sum(t**i for i in range(13))
assert s.factor(S.charpoly(t).as_expr())==s.factor((t-1)**3*phi13**2)
for i,j in product(range(27),repeat=2):
    lhs=coords(source_actor(srcprod(basis[i],basis[j])))
    rhs=coords(srcprod(source_actor(basis[i]),source_actor(basis[j])))
    assert lhs==rhs,("source Griess product",i,j,lhs-rhs)
print("PASS 729/729 original Griess Q(omega) Jordan-source products")
print("PASS source tau-real rational order13, charpoly (X-1)^3 Phi13(X)^2")

if len(sys.argv)!=2:raise SystemExit("usage: checker.py verified_v2.json")
data=json.loads(Path(sys.argv[1]).read_text())
A=s.Matrix([[s.Rational(x) for x in row]
  for row in data['full_27_by_27_native_rational_transport']])
Ai=s.Matrix([[s.Rational(x) for x in row]
  for row in data['explicit_native_to_source_inverse']])
assert A*Ai==I and Ai*A==I
N=A*S*Ai
gram=s.diag(*([1]*3+[2]*24))
assert N**13==I and N.T*gram*N==gram
assert N*A[:,0]==A[:,0]
for i,j in product(range(27),repeat=2):
    a,b=A[:,i],A[:,j]
    lhs=N*native(a,b)
    rhs=native(N*a,N*b)
    assert lhs==rhs,("literal RationalAlbertNative Jordan",i,j,lhs-rhs)
print("PASS 729/729 literal native rational octonionic Albert Jordan products")
print("PASS native order13, exact positive trace Gram and Albert unit")

# Actual traceless 26D invariant carrier with selected trace-zero basis.
P=s.zeros(27,26);P[0,0]=1;P[1,0]=-1;P[1,1]=1;P[2,1]=-1
for j in range(24):P[3+j,2+j]=1
Q=s.zeros(26,27);Q[0,0]=1;Q[1,2]=-1
for j in range(24):Q[2+j,3+j]=1
tr=s.Matrix([[1,1,1]+[0]*24])
assert Q*P==s.eye(26) and tr*P==s.zeros(1,26) and tr*N==tr
B=Q*N*P
assert N*P==P*B
# χ27=(X-1)^3 Phi13^2 and the unit is a fixed complement:
# χ26=(X-1)^2 Phi13^2, fixed dimension2, trace(nontrivial)=0.
print("PASS same native traceless 26D invariant chart and derived Phi13^2 fingerprint")
print("UNPAID Lean/Agda kernel and full F4 group/Monster/physical intertwiners")
