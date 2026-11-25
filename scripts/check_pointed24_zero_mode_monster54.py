from itertools import product
from collections import Counter
import sympy as s

def require(ok):
    if not ok: raise AssertionError('pointed phase zero-mode')

def lap(n,edges):
    L=s.zeros(n)
    for a,b in edges:
        L[a,a]+=1; L[b,b]+=1; L[a,b]-=1; L[b,a]-=1
    return L

def perm(p):
    return s.Matrix(len(p),len(p),lambda i,j:int(i==p[j]))

def chart(n):
    # 24 unit labels indexed by exponent in C24; 24 is independent origin.
    # Four C6 cosets are the four residues modulo 4.
    edges=[(j,(j+4)%24) for j in range(24)]+[(j,24) for j in range(24)]
    if n==27: edges += [(24,25),(24,26)]
    return edges

def phase(n,k):
    p=[(j+k)%24 for j in range(24)]+[24]
    if n==27: p += [26,25] if k%8==4 else [25,26]
    return p

# C6 generator = zeta^4. Its C3 and C2 powers are 8 and 12.
L25=lap(25,chart(25)); L27=lap(27,chart(27))
require(L25.eigenvals()=={0:1,25:1,1:3,2:8,4:8,5:4})
require(L27.eigenvals()=={0:1,27:1,1:5,2:8,4:8,5:4})
for n,L,expected in [(25,L25,(5,9,13)),(27,L27,(6,11,14))]:
    for k,rank in zip((4,8,12),expected):
        P=perm(phase(n,k)); require(P*L==L*P)
        require(n-(P-s.eye(n)).rank()==rank)
    require(L*s.ones(n,1)==s.zeros(n,1))
# Two original 27 charts, joined at their independent origins by a seam.
e27=chart(27)
L54=lap(54,e27+[(a+27,b+27) for a,b in e27]+[(24,51)])
require(L54.rank()==53 and L54*s.ones(54,1)==s.zeros(54,1))
p=phase(27,8); T=perm(p+[j+27 for j in p]); require(T*L54==L54*T)
require(T.trace()==6 and 54-(T-s.eye(54)).rank()==22)
require(T**3==s.eye(54) and T!=s.eye(54))
# The coarse C3 action from the existing character model is identity, not T.
# Equal traces are necessary for an invertible intertwiner.
require(s.eye(54).trace()==54 and T.trace()!=54)
# Tensor form of the existing C3 representation-ring arithmetic.
F=10*3**9; C=6*9; K=1+5*3**6
require((F,C,K,F+C)==(196830,54,3646,196884))
require(C*K==F+C and C*(K-1)==F and K==1+3*1215)
require(C*1215==65610 and F+C-1==196883)
# Regular C3 character at nonidentity is zero, so coarse action controls trace.
require((F+C, int(T.trace())) != (196884,54))
print('PASS pointed25 spectrum; chart27 spectrum; six symmetry-fixed ranks; connected54 rank53; geometric C3 trace6 vs source trace54; tensor arithmetic')
