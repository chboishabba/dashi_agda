#!/usr/bin/env python3
"""Cross-PR integration: literal selected horn SU3 Wilson vs SU3_1 chiral C3.

PRIOR AUTHORITY: Alexander 1924; Hatcher AT Example 2B.2 (commutator
tower); Goto 1949 (ambient SU3 commutator surjectivity);
Lacki/Zaugg 1989 (SU2_4 subset SU3_1 conformal extension);
Witten 1989 CS/WZW; Hosotani 1989 compact-circle quantum selection.
SIBLING SOURCE: Agda #1247 actual selected NeutrinoHornedSU3RootExact
and NeutrinoHornedWilsonInterferenceExact; Agda #1244 actual shrinking
horn-probe. Their UNMERGED Agda definitions are NOT imported here.
NO source geometry, connection, continuous field equation or spectrum
is identified by finite number/group coincidences.
"""
from fractions import Fraction as F
from math import pi, sqrt, exp, log
import numpy as np

# Original selected cyclotomic Wilson-loop character in Q(zeta3).
a=F(176093404722400,181846007130841)
b=-F(19836986431118,181846007130841)
center_coefficients=((F(3),F(0)),(F(0),F(3)),(F(-3),F(-3)))
assert (a,b) not in center_coefficients
assert (F(1,2)*(1+(a-b/2)/3)) == F(434928608401,648677790003)
print('PASS selected horn W not in SU3 centre by exact character coefficients')

z=np.exp(2j*pi/3)
s12,c12=161/289,240/289
s13,c13=240/1609,1591/1609
s23,c23=20/29,21/29
U=np.array([
 [c12*c13,s12*c13,s13*np.conj(z)],
 [-s12*c23-c12*s23*s13*z,c12*c23-s12*s23*s13*z,s23*c13],
 [s12*s23-c12*c23*s13*z,-c12*s23-s12*c23*s13*z,c23*c13]], dtype=complex)
W=np.diag([1,z,z*z])@(2*np.outer(U[:,0],np.conj(U[:,0]))-np.eye(3))
assert np.linalg.norm(W@W.conj().T-np.eye(3))<1e-12
assert abs(np.trace(W)-complex(float(a)+float(b)*z))<1e-11
delta=float(np.linalg.norm(W-np.eye(3),ord=2))
assert abs(delta-1.4381884752669252)<1e-10

# UNIVERSAL CONDITIONAL bound from elementary unitary identity:
# d([X,Y]) <= 2 d(X)d(Y), d(U)=||U-I||_op.
# If all 2^n leaves at depth n satisfy d<=eps_n, then
# delta <= (2 eps_n)^(2^n)/2;
# hence max_leaf_gap >= (2 delta)^(1/2^n)/2.
# If all depth-n geometric loop lengths <= ell_n and their unitary
# connection norm in COMPATIBLE frames <= M, then
# max_leaf_gap <= M ell_n. The needed shrinking representatives
# have NOT been proved for the intended 3-copy wild exterior.
for n in (1,2,3,5,8,12,20):
    forced=.5*exp(log(2*delta)/(2**n))
    ell=2.0**(-n) # illustrative counterfactual, NOT sourced horn metric
    M_min=forced/ell
    assert forced>.5 and M_min>2**(n-1)
    print(f'depth={n} forced_leaf_gap={forced:.12f} required_M_for_2^-n={M_min:.6f}')
assert abs(.5*exp(log(2*delta)/(2**20))-.5)<2e-6

# 12 ordinary SU3 matrices used only to audit, not prove, the norm inequality.
for aa in (.02,.1,.4,1.1):
 for bb in (.03,.2,.6):
    X=np.diag([np.exp(1j*aa),np.exp(-1j*aa),1])
    R=np.array([[np.cos(bb),np.sin(bb),0],
                [-np.sin(bb),np.cos(bb),0],[0,0,1]], complex)
    Y=R@X@R.conj().T
    C=X@Y@X.conj().T@Y.conj().T
    assert np.linalg.norm(C-np.eye(3),ord=2)<=(
        2*np.linalg.norm(X-np.eye(3),ord=2)*
        np.linalg.norm(Y-np.eye(3),ord=2)+1e-12)
print('PASS unitary commutator finite regression; analytic inequality original prior math')

# Abelian-target obstruction from Hatcher's PERFECT commutator tower.
# Every horn meridian m_w is [m_w0,m_w1]. For a hypothetical group
# homomorphism q:G->Z/3, q(m_w)=q(m_w0)+q(m_w1)
#                         -q(m_w0)-q(m_w1)=0.
# This is about GROUP HOMOMORPHISMS into the pointed fusion group,
# not a no-go for arbitrary categorical/defect representations.
from itertools import product
for x,y in product(range(3),repeat=2):
    assert (x+y-x-y)%3==0
for leaves in product(range(3),repeat=4):
    first=(leaves[0]+leaves[1]-leaves[0]-leaves[1])%3
    second=(leaves[2]+leaves[3]-leaves[2]-leaves[3])%3
    assert (first+second-first-second)%3==0
print('PASS all 9 one-stage and 81 two-stage horn->abelian C3 charge maps trivial')
# For G^3 ⋊ C3 with perfect horn G, any group hom to C3
# kills G^3 and can depend only on the OUTER rotation C3 coordinate.

# A Z3 fusion SIMPLE-OBJECT label is not a holonomy matrix.
# Concrete falsifier for falsely equating selected W with centre z I:
# tr(z I)=3z, unit visibility, P0=1/4, while selected W has
# visibility ~0.34242 and P0~0.670485.
center_visibility=abs(np.trace(z*np.eye(3)))/3
center_port0=.5*(1+z.real)
selected_visibility=abs(np.trace(W))/3
selected_port0=.5*(1+np.trace(W).real/3)
assert abs(center_visibility-1)<1e-12 and abs(center_port0-.25)<1e-12
assert abs(selected_visibility-.3424207192088653)<1e-10
assert abs(selected_port0-.6704848155799947)<1e-10
print('PASS centre-vs-selected observable discriminator (NOT horn-specific)')
print('OPEN actual shrinking physical loop representatives and compatible bounded connection')
print('OPEN SU3_1 chiral categorical charge to gauge Wilson-matrix functor/physical coupling')
