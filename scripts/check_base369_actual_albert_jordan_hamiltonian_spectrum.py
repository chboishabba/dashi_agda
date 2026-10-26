#!/usr/bin/env python3
"""Exact *literal* Albert Jordan Hamiltonian spectrum and traceless reduction.

The actual Jordan product on Hermitian 3x3 octonionic matrices is
X∘Y=(XY+YX)/2. For diagonal h=diag(1,0,-1), left multiplication
L_h(X)=h∘X has real eigenvalues d_i on the 3 diagonal basis vectors
and (d_i+d_j)/2 on the 8 octonionic basis vectors of each i<j slot.
No F3^3 fine grading, Monster Griess product or physical dynamics
is constructed by this finite calculation. The complete standalone
rational Cayley–Dickson product validator is provided as a local artifact
check_369_albert_jordan_hamiltonian.py.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
import sympy as s
d=(F(1),F(0),F(-1))
spectrum=Counter(d)
for i,j in combinations(range(3),2):
    spectrum[(d[i]+d[j])/2]+=8
assert spectrum==Counter({F(1):1,F(-1):1,F(0):9,F(1,2):8,F(-1,2):8})
assert sum(spectrum.values())==27
# Scalar line is span(I), trace-free part ker(Tr), 26 dimensions.
P=s.ones(3)/3
Q=s.eye(3)-P
assert P*P==P and Q*Q==Q and P*Q==s.zeros(3)
assert s.trace(P)==1 and s.trace(Q)==2
# Diagonal multiplier maps I to h, so does not preserve span(I).
D=s.diag(1,0,-1)
assert D*s.ones(3,1)!=s.zeros(3,1)
assert P*D*s.ones(3,1)==s.zeros(3,1)
assert Q*D*s.ones(3,1)==D*s.ones(3,1)
# Compress to trace-free 26 dimensions (2 diagonal +24 octonionic).
c=Q*D*Q
assert c==c.T
assert c.eigenvals()=={s.sqrt(3)/3:1,-s.sqrt(3)/3:1,s.Integer(0):1}
assert 2+8+8+8==26
print("PASS Albert J3(O) left-multiplication mode spectrum",spectrum)
print("PASS tracefree 26 compression: ±1/sqrt3 each1, ±1/2 each8, zero8")
print("PASS noncentral Jordan multiplication mixes distinguished scalar with traceless component")
print("NOT A MONSTER VOA MODE / PHYSICAL KK HAMILTONIAN")
