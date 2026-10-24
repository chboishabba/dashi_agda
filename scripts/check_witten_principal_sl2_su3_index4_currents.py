#!/usr/bin/env python3
"""Principal sl2 in sl3: exact Lie/current algebra for SU(2)_4⊂SU(3)_1.

PRIOR MATHEMATICS: Dynkin's embedding indices, affine conformal embeddings;
J. Lacki & Ph. Zaugg, Phys Lett B228 (1989) 223-227,
DOI 10.1016/0370-2693(89)90662-X.
The principal su2↪su3 has Dynkin index 4, and the sl3
adjoint restricts to spin1(dim3) + spin2(dim5). This exact
rational-matrix code checks the underlying complexified Lie
brackets; it is not a constructed affine VOA/OPE/Q-system, nor
a Standard Model SU3_c gauge group or 369 geometry.
"""
from sympy import Matrix, zeros, diag, Rational as Q

def E(i,j):
    m=zeros(3)
    m[i,j]=1
    return m

def bracket(a,b):
    return a*b-b*a

raising=E(0,1)+E(1,2)
lowering=2*(E(1,0)+E(2,1))
cartan=diag(2,0,-2)
assert bracket(cartan,raising)==2*raising
assert bracket(cartan,lowering)==-2*lowering
assert bracket(raising,lowering)==cartan
print("PASS exact principal sl2 Lie commutators inside sl3")

# Relative to the standard sl2 defining doublet normalization:
# tr_2(E12 E21)=1; the principal sl3 normalization is 4.
e2=Matrix([[0,1],[0,0]])
f2=Matrix([[0,0],[1,0]])
assert (e2*f2).trace()==1
assert (raising*lowering).trace()==4
assert Q((raising*lowering).trace(),(e2*f2).trace())==4
assert 4*1==4
print("PASS principal sl2↪sl3 normalized trace index 4: su3 level1 induces su2 level4")

# The highest-weight +4 root E13 generates a complete spin2
# (5-dimensional) module under the chosen principal sl2.
spin_two=[E(0,2)]
for _ in range(4):
    spin_two.append(bracket(lowering,spin_two[-1]))
assert bracket(lowering,spin_two[-1])==zeros(3)
for i,v in enumerate(spin_two):
    assert bracket(cartan,v)==(4-2*i)*v
    if i:
        assert bracket(raising,v)==i*(5-i)*spin_two[i-1]
    assert v.trace()==0

# The 3-dimensional adjoint sl2 plus five new weight-one currents
# span all eight traceless 3x3 complex matrices.
spin_one=[raising,lowering,cartan]
flatten=lambda m: Matrix(9,1,list(m))
assert Matrix.hstack(*[flatten(x) for x in spin_one+spin_two]).rank()==8
assert all(x.trace()==0 for x in spin_one)
print("PASS full sl3 adjoint = principal spin1(3) ⊕ spin2(5), exact Lie weight/rank")
assert 3*4/(4+2)==8*1/(1+3)==2
print("PASS matching affine Sugawara central charge c2; fixed-point resolution still needs Q-system")
print("BOUNDARY complexified Lie algebra witness, not affine VOA sewing, CS theory, or physical color gauge")
