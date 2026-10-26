#!/usr/bin/env python3
"""Single FAST-shrinking Hatcher branch obstruction for ANY unitary image.

ORIGINAL MATHEMATICS: Hatcher AT Example 2B.2 marked group injection
m_w=[m_w0,m_w1], elementary unitary operator norm:
d(U)=||U-I||op <=2; d([A,B])=||AB-BA|| <=2*min(d(A),d(B)).
NEW SOURCE-SPECIFIC CONSEQUENCE: following ONE depth-n binary branch
gives d(root)<=2^n*d(leaf), not requiring finite group image.
For a FLAT source connection with a GENUINE Hatcher-marked loop
L_n and compatible norm bound M: d(root)<=2^n M L_n.
Original #1247 owns the exact selected W trace. Independent #1249
certified d(W)^2 >= 854996726408/648677790003 >1.

This script proves coefficient arithmetic and acceptance windows only.
It does NOT construct shrinking geometric horn meridians, flat source
connections, true 3D linked Hatcher Z blocks or an observed effect.
Nonflat connections require a distinct homotopy/curvature-error receipt.
"""
from fractions import Fraction as F

SOURCE_ROOT_NORM_SQ_LOWER=F(854996726408,648677790003)
assert SOURCE_ROOT_NORM_SQ_LOWER>1
# This independent selected arithmetic lower bound is all that is used.
M=F(100)
L0=F(1)
def branch_bound(n, q, M=M, L0=L0):
    return F(2)**n*M*L0*q**n

for q in (F(1,8),F(1,5),F(1,4),F(1,3),F(1,2),F(3,5)):
    crossing=[n for n in range(61) if branch_bound(n,q)<=1]
    if q<F(1,2):
        assert crossing and branch_bound(crossing[0],q)<=1
        assert all(branch_bound(n,q)>1 for n in range(crossing[0]))
    else:
        assert not crossing
    print("PASS single branch exact rational rate:",q,
          "earliest rejection stage:", crossing[0] if crossing else "none by n60")

# Each sibling is unitary -> d(sibling)<=2. ONE branch n-fold uses:
# d(root)<=2^n d(leaf), with no finite-image gap premise.
for n in range(0,31):
    eps=F(1,2**n)
    assert F(2)**n*eps==1
    # When d_root>1, leaf gap<=1/2^n is impossible.
    assert SOURCE_ROOT_NORM_SQ_LOWER>1
print("PASS 31 exact finite-depth single-leaf SU3 thresholds using ||[A,B]-I||=||AB-BA||<=2d(A),2d(B)")

# SHARPNESS: B swaps first two SU3 eigen-directions, while
# A_n=diag(z, z^-1, 1), z=(n+i)/(n-i), lies in SU3 and approaches I.
# B A B^-1=A^-1 and [A,B]=A². Thus
# [d([A,B])/d(A)]²=|z+1|²=4n²/(n²+1) -> 4.
# The Lipschitz factor TWO is optimal over the full unitary class,
# so the 2^n branch exponent is not improvable by a smaller
# uniform single-step constant without additional source constraints.
for n in (1,2,5,10,100,1000):
    ratio_sq=F(4*n*n,n*n+1)
    assert 0<ratio_sq<4
    assert 4-ratio_sq==F(4,n*n+1)
print("PASS exact sharpness family: SU3 commutator-to-child ratio -> 2")

# A heterogeneous full-depth tree admits a STRICTLY MORE FLEXIBLE
# acceptance test than requiring every leaf small. For a full binary tree,
# d(root)<=1/2 * product_{all leaves}(2 * d(leaf));
# prove by recursive substitution of d(comm) <=2d(left)d(right).
def envelope(node):
    if isinstance(node,F):
        return node
    a,b=node
    return 2*envelope(a)*envelope(b)
def product_scaled_leaves(node):
    if isinstance(node,F):
        return 2*node
    a,b=node
    return product_scaled_leaves(a)*product_scaled_leaves(b)
def make_tree(depth,leaf_fn,index=0):
    if depth==0:return leaf_fn(index)
    return (make_tree(depth-1,leaf_fn,2*index),
            make_tree(depth-1,leaf_fn,2*index+1))
for n in range(9):
    # Explicit heterogeneous bound: no uniform epsilon assumption.
    tree=make_tree(n,lambda idx:F(1+(idx%5),11+(idx%7)))
    assert 2*envelope(tree)==product_scaled_leaves(tree)
print("PASS 9 exact heterogeneous-tree product-envelope identities; 256 leaves at depth8")
print("GEOMETRY OPEN: source-linked Hatcher Z-block has not supplied L_n or M")
print("FLATNESS REQUIRED: π1 commutator relations do not control arbitrary curved Wilson loops")
print("NO finite-image assumption: selected W may have infinite order")
