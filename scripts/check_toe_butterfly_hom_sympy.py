"""Exact C3 butterfly and Hom projector identities (SymPy, not Agda).
Donors: TriadicDepthOneCharacters, C3FourierConjugationExact,
MLKEMButterflyStageLocalityInvariantExact (schedule only),
IbrahimMonster3BLinearMultiplicityHomSpaceExact and Y443 Nov 8 projector route.
"""
import sympy as s
from itertools import product
z=s.Symbol('z'); mod=z*z+z+1
red=lambda x:s.rem(s.expand(x),mod,z)
M=lambda X:X.applyfunc(red)
I=s.eye(3); F=s.Matrix(3,3,lambda i,j:z**((i*j)%3)); G=s.Matrix(3,3,lambda i,j:z**((-i*j)%3)); P=s.Matrix(3,3,lambda i,j:int(i==(-j)%3)); T=s.Matrix(3,3,lambda i,j:int(i==(j+1)%3)); D=s.diag(1,z,z*z)
assert M(F*G)==3*I and M(F*F)==3*P
assert M(F*T-D*F)==s.zeros(3)
assert M(F*D-T.T*F)==s.zeros(3)
for phase in (1,2):
 D=s.diag(*[z**((phase*i)%3) for i in range(3)])
 Ps=[M(sum((z**((-phase*b*x)%3)*D**b for b in range(3)),s.zeros(3))/3) for x in range(3)]
 assert sum(Ps,s.zeros(3))==I
 for x,y in product(range(3),repeat=2): assert M(Ps[x]*Ps[y])==(Ps[x] if x==y else s.zeros(3))
 for x in range(3): assert M(T*Ps[x]-Ps[(x+1)%3]*T)==s.zeros(3)
 # A nontrivial multiplicity space; evaluate/recover all linear basis vectors.
 m=3; eye=s.eye(m); TT=s.kronecker_product(T,eye); PP=[s.kronecker_product(p,eye) for p in Ps]
 V=s.kronecker_product(I[:,0],eye)
 Phi=s.Matrix.hstack(*[TT**x*V for x in range(3)])
 Psi=s.Matrix.vstack(*[V.T*TT**((-x)%3)*PP[x] for x in range(3)])
 assert M(Phi*Psi)==s.eye(9) and M(Psi*Phi)==s.eye(9)
print('PASS SymPy C3 butterfly, both phase projector resolutions, 9D linear evaluation inverse')
