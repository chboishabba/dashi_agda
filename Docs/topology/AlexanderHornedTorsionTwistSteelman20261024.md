# Torsion, literal interlocking horns, and order-three quotient actors
Date: 2026-10-24. Owner: Alexander horned C3 PR #1244.

## Source audit: verified versus proposed

**Primary classical theorem — Hatcher**, *Algebraic Topology*,
Example 2B.2, printed pages 171–172, PDF pages 179–180:
https://pi.math.cornell.edu/~hatcher/AT/AT.pdf

For the **particular classical** Alexander ball B in R^3, writing
Y_n=R^3\X_n for complements of the nested handle approximations:

    pi1(Y_0) = Z = F_1,
    pi1(Y_n) = F_(2^n),
    pi1(Y_n) -> pi1(Y_(n+1)) is INJECTIVE,
    x_w -> [x_(w0),x_(w1)],
    pi1(R^3\B) = colim_n pi1(Y_n).

Hatcher explicitly derives injectivity from van Kampen and the
nonidentity commutator injection of the attaching annulus.
Compactness of loops and homotopies identifies the limit. Its
abelianization is trivial because every generator becomes a
commutator one stage later. This is a **nontrivial perfect group**.

**Consequence — classical group theory**, not a separate theorem of
Hatcher: all free groups are torsion-free. Every element of the
injective direct limit has some finite-stage representative.
If its kth power is the identity in the limit, injectivity of the
corresponding stage group into the limit makes that power
the identity at the same stage; therefore its representative is
the identity. Hence the group is torsion-free, although neither
abelian nor free at the limit.

**Our THREE-root modification**:
    G_3 = colim_n F_(3*2^n).
Its structural transition is the free product of three copies
of Hatcher's injection. Since free product of injections between
free groups of corresponding factors is injective, G_3 is also
torsion-free; if it is identified as G_A * G_A * G_A, this also
follows directly from the normal-form theorem for free products.
Unlike the ONE-root classical G_A, the geometric identification
G_3=pi1(S^3\H_three) is NOT kernel-certified in PR #1244 and
remains subject to its explicit tame collar / van Kampen inputs.
Do NOT misattribute this three-root realization to Hatcher.

**Formal transfer added in this PR**:
DASHI/Mathematics/Topology/
AlexanderHornedTorsionFreeStageTransportExact.agda
- covered injective, power-preserving finite-stage embeddings;
- prove target torsion-free from each stage torsion-free;
- if a source image in C3 is nonidentity, its cube cannot be
  identity in the source.
These are conditional type-theoretic theorems, NOT a constructor
of the actual classical or three-copy geometric stage system.
No exact-head Agda kernel receipt obtained during this cut.

## What torsion-free does and does NOT say

An element of pi1 is a **homotopy class of based LOOPS IN THE
COMPLEMENT**. It is torsion if the SAME LOOP repeated finitely
many times becomes nullhomotopic. A geometric intertwining or
a curve physically spiralling is not finite order in pi1.

When one walks once around a nontrivial meridian m,
    m != 1;   m^2 != 1;   m^3 != 1; ...
Even if a diagram has three apparent lobes / twists, the
repeated path has no automatic relation m^3=1. A twist,
a braid, a cyclic permutation, an ambient rotation, and a
loop about the horns live in distinct mathematical objects.

Compare a three-strand braid:
    b = sigma1 sigma2 in B3,
    b projects to a 3-cycle in S3,
    b^3 = (sigma1 sigma2)^3 = full twist != 1 in B3.
Nontriviality of this cube already follows from the
exponent-sum map B3 -> Z: sigma1 and sigma2 each map to 1,
so b^3 maps to 6, whereas identity maps to 0.
The stronger theorem that B3 is torsion-free is standard:
J. Gonzalez-Meneses (2011), *Basic results on braid groups*,
https://doi.org/10.5802/ambp.293.
This is a comparator, NOT a proof that the horned complement
is B3 or that its meridians are physical braid motions.

C3 rotations of the AMBIENT SPACE can have order three even
if pi1 of the exterior is torsion-free: a rotation is a
homeomorphism inducing an AUTOMORPHISM pi1->pi1, not a
homotopy class of loops in pi1. Conversely, some 3-manifold
fundamental groups DO have torsion (e.g. RP^3 has pi1=Z/2);
there is no general inference '3D objects cannot have torsion.'
The configuration space SO(3) has pi1=Z/2, so rotational
configuration loops can have torsion; that is a DIFFERENT
space from the Alexander complement.

The key diagnostic is not the word "twist"; it is
    Does there exist g != 1 and n>0 with g^n=1
in the EXACT pi1 presentation being studied?
For Hatcher's exterior group, the injective free tower
provides a decisive negative answer.

## A sharper finite A5/C3 representation discriminator

Existing finite A5 character-restriction owner:
DASHI/Foundations/PolyhedralFiniteRestrictionInstancesExact.agda,
plus the j0..35 exact icosahedral character owner.

Select the concrete order-three A5 permutation
    s=(0 1 2) in A5.
It is itself a commutator of an A5-generating pair (verified
by exhaustive 60-element enumeration), so the independent
recursive commutator assignments can choose one initial
horn meridian m with q(m)=s. The root meridian m is infinite
order in G_3, yet
    q(m)^3=1 and q(m^3)=1 while m^3 != 1.
Thus the finite representation does not preserve element
order, only the quotient image; this is a REPRESENTATION
kernel, not a topological contradiction. It is even more
direct than the earlier root example mapping to order five.

Let r be the external order-three automorphism permuting
three independent factors. Then
    Q = A5^3 rtimes C3_ext
contains C3_int x C3_ext, with diagonal 3-cycle C3_int,
but this 9-element finite subgroup does NOT embed as such
in G_3 rtimes C3_ext.

**No-embedding proof:** G_3 is torsion-free. If K is any
finite subgroup of G_3 rtimes C3_ext, the kernel of
projection K -> C3_ext is the finite subgroup
K intersect G_3. It is trivial. Therefore projection
is injective and |K| divides 3. In particular K cannot
be C3 x C3 of size 9. This theorem concerns the *source*
semidirect product, not the quotient. A finite image may
have strictly more finite subgroup types than its source.

## Important source-discriminator: Riebe 1968

Norman W. Riebe's thesis, *The Fundamental Groups of the
Complements of Some Solid Horned Spheres* (1968),
https://digitalcommons.usu.edu/etd/6821/,
abstract says certain higher-order horned-sphere complement
groups G^k are free of countably infinite rank. This cannot
describe the SAME group as Hatcher's perfect exterior G_A:
a nontrivial free group has nontrivial abelianization.
The thesis also describes homomorphisms onto A5.
**Do not silently fuse these group presentations.**
Full thesis text was not accessible through the current
source fetch (HTTP 403), so the precise choice of
complement/component/embedding/G^k is a SOURCE-MATCHING
OPEN LEAF. The direct citation of Hatcher's actual
presentation is the authority for this programme's G_A.

## Verification and falsification

Finite independent audit:
    python3 scripts/alexander_horned_torsion_steelman_probe.py
Probes an explicit A5 order-three commutator root with A5-generating
children, three sector copies, stage 0..4 free words and powers
1..9; confirms q(m^3)=1 but nonempty reduced word m^3 at
each tested stage; contrasts order-three permutation of
sigma1 sigma2 with nonzero full-twist exponent 6.

This bounded test neither proves the infinite order nor
that the actual geometric three-copy complement has the
claimed pi1. Infinite-order proof uses the injective
free tower (Hatcher / algebra). A geometric counterexample
would have to falsify an injectivity, cover identification,
or actual same-object source correspondence, not merely
display horn twisting.

The largest remaining proof task is source-specific
three-copy geometric van Kampen and exact-head Agda/Lean
kernel checks, NOT more A5 or C3 arithmetic.


## 2026-10-24 p-adic / hypercomplex max-cut

Source-audited complete branch:
`Docs/topology/AlexanderHornedPadicHypercomplexMaxCut20261024.md`.

- Actual **binary** horn branch address is a low-to-high
  `Z_2` prefix stream, independent of the three `C3`
  root sectors. Existing newest-first Agda suffix orientation
  must be reversed for chronological low-order digits.
  `AlexanderHornedBinaryPadicCylinderExact.agda` inhabits
  the pre-existing p-adic `CylinderSystem`, proves prefix
  truncation and sector-rotation compatibility. No exterior
  p-adic metric identification is claimed.
- Actual rational quaternion `q=(1+i+j+k)/2` satisfies
  `q^3=-1`, `(-q)^3=1` and, by conjugation, gives
  the SAME ambient `(x,y,z)->(z,x,y)` rotation. New
  `AlexanderHornedQuaternionC3SpinExact.agda` reuses
  the existing rational quaternion, Cayley-Dickson/Hopf
  and Q8->V4 sources, including conjugation cycling
  `i->j->k->i`. This is not a finite-order loop lift.
- More generally, recursive horn meridian images into
  EVERY finite-derived-length **solvable** group are trivial.
  `AlexanderHornedProPSolvableBlindExact.agda` proves
  it by induction down the derived series using the real
  commutator recursion. With meridian generation, abstract
  `G` has trivial finite-p-group quotients and
  `pro-p(G)=1` for all primes, even though its wild
  endpoint space is nontrivial `Z_2`.
- For the semidirect extension `H=G⋊C3_ext`,
  `pro-3(H)=C3_ext`, and `pro-p(H)=1` for other p.
  However bare Q3 lacks a primitive cube root, so
  scalar `Hom(H,Q3^×)=1`; nontrivial C3 matrices
  over Q3 and scalar phases after `Q3(zeta3)`
  remain available. Group quotient versus field-local
  eigenphase must not be confused.
- The **nonabelian** existing A5^3 quotient admits
  rational permutation matrices over EVERY Qp.
  Thus trivial pro-p completion does not preclude
  p-adic linear/finite-VOA actors. Finite images do not
  recover all of G or identify Monster 3B states.
- An independent exact-fraction and finite enumeration
  audit PASSED (quaternion C3 signed lifts, 2-adic
  binary prefixes through depth 7, 60/60 A5 commutators,
  60-dimensional nonabelian regular representation).
  Committed `scripts/alexander_horned_padic_hypercomplex_audit.py`.

Proof boundary remains unchanged: new Agda sources await
exact-head kernel receipts, and the actual three-copy horn
complement's collared van Kampen and limit pi1 identification
are not kernel-certified. Avoid overindexing on 369,
octonionic analogies or uninhabited spin/VOA interfaces.
