#!/usr/bin/env python3
"""Original Griess1990 rational A=F3³ character Fourier bridge to periodic C3³.

Reuses the EXISTING Agda #1239 geometric open-vs-periodic matrices from
check_base369_f3cube_albert_hamiltonian_symmetry.py; no duplicate graph owner.
External math: R.L. Griess Jr. (1990) Albert homogeneous fine grading;
standard finite Abelian Fourier duality. No physical 27-site Jordan product
intertwiner or Monster VOA operator is inferred.
Optional argv[1]: Q-rational 27x27 Griess-to-native Albert JSON from Lean #52.
"""
import runpy,sys,json
from pathlib import Path
from itertools import product
import sympy as s
p=runpy.run_path(str(Path(__file__).with_name(
    "check_base369_f3cube_albert_hamiltonian_symmetry.py")))
sites=p["P"]; index=p["ix"]; openL=p["A"]; periodicL=p["B"]
I=s.eye(27); ones=s.ones(27,1)
neg=lambda a:tuple((-u)%3 for u in a)
reps=[a for a in sites if a!=(0,0,0) and a<neg(a)]
assert len(reps)==13
G=s.diag(3,*sum(([6,6] for _ in reps),[]))
for k in range(13):
    G[1+2*k,2+2*k]=G[2+2*k,1+2*k]=-3
hexagon=[s.eye(2),s.Matrix([[0,-1],[1,-1]]),
         s.Matrix([[-1,1],[-1,0]])]
def phase(a,b):return sum(x*y for x,y in zip(a,b))%3
def charact(a):
    M=I.copy()
    for k,x in enumerate(reps):
        M[1+2*k:3+2*k,1+2*k:3+2*k]=hexagon[phase(a,x)]
    return M
def translation(a):
    T=s.zeros(27)
    for x in sites:
        y=tuple((u+v)%3 for u,v in zip(x,a))
        T[index[y],index[x]]=1
    return T
F=s.zeros(27)
for j,t in enumerate(sites):
    F[0,j]=1
    for k,a in enumerate(reps):
        u,v=((1,0),(0,1),(-1,-1))[phase(a,t)]
        F[1+2*k,j]=u
        F[2+2*k,j]=v
assert F.T*G*F==81*I
Finv=F.T*G/81
assert Finv*F==F*Finv==I
assert F*ones==27*I[:,0]
assert F[:,index[(0,0,0)]]!=I[:,0]
for a in sites:
    assert charact(a)*F==F*translation(a)
    assert periodicL*translation(a)==translation(a)*periodicL
assert F*periodicL*Finv==s.diag(0,*sum((
    [3*sum(x!=0 for x in a)]*2 for a in reps),[]))
assert periodicL.eigenvals()=={0:1,3:6,6:12,9:8}
assert openL.eigenvals()=={0:1,1:3,2:3,3:4,4:6,5:3,6:3,7:3,9:1}
for axis in range(3):
    e=tuple(int(i==axis) for i in range(3))
    comm=charact(e)*(F*openL*Finv)-(F*openL*Finv)*charact(e)
    assert comm.rank()==18
assert F.det() in (3**34,-3**34)
print("PASS exact rational Fourier F^T G F=81I and all 27 source-character/periodic-translation intertwiners")
print("PASS periodic Laplacian 0,3,6,9 vs open P3^3 nine eigenvalues; generator open commutator rank18")
print("PASS spatial constant maps to Albert unit, spatial origin delta does NOT")
if len(sys.argv)>1:
    data=json.load(open(sys.argv[1]))
    key="full_27_by_27_native_rational_transport"
    if key not in data:key="native_27x27_map"
    A=s.Matrix([[s.Rational(q) for q in row] for row in data[key]])
    assert A.shape==(27,27) and A.det()!=0
    nativeG=s.diag(*([1]*3+[2]*24))
    assert (A*F).T*nativeG*(A*F)==81*I
    assert A*F*ones/27==A[:,0]
    assert A*F[:,index[(0,0,0)]]!=A[:,0]
    print("PASS source-specific Lean #52 native Albert Fourier/trace/unit transport")
print("SCOPE: NOT native open cube Jordan-hopping, Monster VOA, F4 classified form, KK or physical experiment")
