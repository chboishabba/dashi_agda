# Horned C3: Ore / residual finite / p-adic / binary-ternary impasse break
Date: 2026-10-24. PR #1244. Status: mathematical deduction and source-written exact local lemmas; compiler and geometry gates open.

## 0. Original mathematics, external authority, existing source owners

* Hatcher, *Algebraic Topology*, Example 2B.2, printed pp.171–172:
  https://pi.math.cornell.edu/~hatcher/AT/AT.pdf
  Derives the increasing free-stage exterior group and injections
  x_w |-> [x_w0,x_w1], and compactness to the exterior pi1.
  This is authority for the **one-root classical** horned ball,
  not the proposed three-copy geometric collar placement.
* Oystein Ore (1951), commutators in alternating groups;
  Martin W. Liebeck, E. A. O'Brien, Aner Shalev, Pham Huu Tiep,
  *The Ore conjecture*, JEMS 12 (2010), pp.939–1008,
  DOI 10.4171/JEMS/220:
  https://ems.press/journals/jems/articles/3979
  Every element of every nonabelian finite simple group is a
  commutator. This EXTERNAL theorem is not a new DASHI proof.
* Residual finiteness of free groups is classical; the stronger
  residual alternating-group property is explicitly cited
  as Theorem 1.3.7 in *Separability within alternating groups
  and randomness* (Cambridge repository, thesis):
  https://api.repository.cam.ac.uk/server/api/core/bitstreams/9ee5efac-dcd7-46c4-800d-7c4a1a78dd29/content .
* Existing DASHI:
  - `DASHI/Foundations/PolyhedralRegularRepresentationShiftExact.agda`
    A5 regular dimension 60 and icosahedral characters;
  - `DASHI/Mathematics/Topology/AlexanderHornedC3FiniteVOAActorExact.agda`
    THE SAME finite quotient regular-coordinate action;
  - `DASHI/Mathematics/Topology/AlexanderHornedC3VOAModeLiftExact.agda`
    all pointwise rational vertex modes under that action;
  - `DASHI/Mathematics/Topology/AlexanderHornedProPSolvableBlindExact.agda`
    derived-series meridian vanishing in solvable targets;
  - `DASHI/Physics/QFT/NonAbelianFusionFromSpin.agda`
    existing CONDITIONAL CM abelian + Rep(SU2) spin-sector
    nonabelian fusion; not an automatic group map from horns;
  - `DASHI/Physics/SFGC/NonAbelian/CliffordToM2Iso.agda`
    concrete **basis bijection**, not a product-preserving
    algebra isomorphism merely by its name;
  - `DASHI/Physics/SFGC/NonAbelian/DepthQuotientIso.agda`
    composed proof carrier but no new group representation;
  - `DASHI/Foundations/Base369BinaryTernaryRefinement.agda`
    commuting independent 2^a and 3^b refinement axes;
  - `DASHI/ComputerScience/BinaryBalancedTernarySubcarrierExact.agda`
    exact two-point antipodal bit embedding in balanced trits;
  - `DASHI/Codec/VerifiedFiniteTritCoder.agda`
    lossless three-trit-symbol -> two-bit code with fourth
    invalid codeword;
  - `DASHI/ComputerScience/BalancedTernaryC2C3DihedralCodecBridgeExact.agda`
    two different C2 and C3 actions on a three-point basis,
    not an additive group equivalence;
  - the extensive rational quaternion/Cayley-Dickson/Hopf/
    Clifford work surveyed in
    `Docs/topology/AlexanderHornedPadicHypercomplexMaxCut20261024.md`.
  New implementation should CONSUME these, not mint replacements.

## 1. Strongest new mathematics: abstract horn G is residually finite

Write

    G_r = colim_n F_(r * 2^n),  r=1 (Hatcher) or r=3 (our abstract model),
    x_(c,w) |-> [x_(c,w0), x_(c,w1)].

All bonding maps are injective. Take any g != 1 in G_r.
Choose a stage n and a nontrivial free word w in F_(r*2^n)
representing g. Its nontriviality is preserved in the colimit.

Step A -- FINITE STAGE SEPARATION:
Free groups are residually finite. Choose a finite group Q
and a homomorphism f_n:F_(r*2^n)->Q with f_n(w)!=1.
Embed Q in an alternating group A_m (m>=5):
use its Cayley left-regular action Q<=S_|Q|, then duplicate
the permutation on two disjoint copies. The sign squares
to +1, so the diagonal map is a faithful embedding
Q -> A_(2|Q|); adjoin fixed points if needed. Compose f_n
with this embedding. This proof avoids presuming the
selected source word is visible in a fixed A5.

Step B -- FINITE TARGET COMMUTATOR LIFT:
Every element of A_m is a commutator by Ore. For every
generator x_(c,w) at stage k>=n with image a, choose
u(a),v(a) in A_m with [u(a),v(a)]=a; assign the new
children x_(c,w0)->u(a), x_(c,w1)->v(a).
Because the stage k+1 group is FREE, this defines an
actual homomorphism f_(k+1) with

    f_(k+1) o phi_k = f_k.

For k<n use f_k = f_n o (phi_(n-1) ... phi_k).
These compatible maps give, by the colimit universal
property, q_g:G_r->A_m with q_g(g)!=1.

**THEOREM**: G_r is residually finite, and even
residually in finite alternating groups (no bound on m).
The only external group-theoretic inputs are residual
finiteness of free groups, embedding finite groups in
alternating groups and the Ore commutator theorem.
The result also holds for the actual classical exterior
G_1 via Hatcher's established SAME-OBJECT pi1 theorem.
For the proposed 3-copy GEOMETRIC exterior, the
G_3-is-pi1 bridge is not yet proven.

Mathematical implication:
    G_r -> profiniteCompletion(G_r) is INJECTIVE.
This STRONGLY sharpens the previous merely
"nontrivial full profinite completion" statement.

**Formal source contribution**:
`DASHI/Mathematics/Topology/AlexanderHornedOreFiniteTargetExtensionExact.agda`
reuses the LITERAL previous HornAddress, Word and expandWord.
Given a group-like finite target with a chosen commutator
section, it constructs explicit child assignments and proves
by structural recursion, for EVERY source formal word,

    evaluate(nextAssignment(f), expandWord(w)) = evaluate(f,w).

It also iterates this equality through every chosen finite
depth. This is a REAL local proof, not a claimed colimit
kernel receipt or an axiom that target residual finiteness
has already been shown. Full Agda A_m/Ore witnesses,
free-group quotient package, universal colimit and
exact-head compiler receipt remain formalisation tasks.

## 2. Perfectness and nonabelian observations coexist

G_r is perfect because every horn meridian eventually
becomes a commutator and the meridians generate.
Hence:
    Hom(G_r, finite solvable group)=1,
    prosolvable(G_r)=1,
    pro-p(G_r)=1 for EVERY prime p.

The same group is residually alternating/profinite:
    intersection_(finite alternating q) ker(q) = {1}.

This is no contradiction: a finite alternating group
A_m (m>=5) is nonabelian and nonsolvable. Scalar
characters and finite p-group holonomies are blind,
but finite NONABELIAN group representations can
detect every source element with a chosen sufficiently
large finite target.

For H_r = G_r rtimes C3_ext, all finite solvable
quotients factor through C3_ext. Thus:
    pro-3(H_r)=C3_ext,
    pro-p(H_r)=1 for p != 3.
The source G_r and its extension have genuine
torsion distinctions (G_r torsion-free, H_r has
external order three). In general H_r is residually
finite because the C3 rotation action can be
symmetrized across finite quotients.

## 3. Faithful FAMILY of p-adic regular actors, not one finite VOA

Any finite quotient q_g:G_r->A_m has a faithful
regular permutation representation of A_m on m!/2
basis states over Z, hence over Q_p for EVERY p:

    G_r -> A_m -> GL_(m!/2)(Z) -> GL_(m!/2)(Q_p).

Our already-proved finite A5 example has order
|A5|=60 and a regular representation of dimension 60.
The selected three-root/outer-C3 actor has 3*60=180
state coordinates, reusing the existing finite
`AlexanderHornedC3FiniteVOAActorExact` as the
canonical owner.

The new
`AlexanderHornedNonabelianRegularPadicReuseExact.agda`
proves on THE SAME actor's regular slots that a
group factor is detected by applying its coordinate
action to the identity basis address. Its same-state
vertex-mode equivariance is imported directly from
`AlexanderHornedC3VOAModeLiftExact.agda`.

Varying q_g with g gives a **jointly faithful family**
of finite-dimensional integral and hence p-adic
permutation representations. There is no assertion
that ONE A5^3 representation is faithful on G, nor
that ONE fixed-dimensional GL_n(Q_p) action does so.

For the outer-C3 semidirect:
 - choose three C3-conjugate finite quotients of
   the independent sectors;
 - collect them in A_m^3, rotating the three factors;
 - extend to A_m^3 rtimes C3;
 - its regular-coordinate permutation actor provides
   a finite-dimensional commutative c=0 vertex
   algebra over Q (and coefficient extension to Q_p).
This gives a jointly faithful FAMILY of finite
quotient VOA automorphism actions of H_r.

DO NOT silently call an infinite product of these
finite state algebras a standard VOA: conventional
VOA finiteness/weight-space conditions may fail
(e.g. an infinite-dimensional weight-zero space).
A faithful family is not a faithful single VOA
without an additional graded construction.

No Monster V-natural or Griess/Albert same-object
identification follows from these representations.

## 4. Binary in ternary AND ternary in binary: precise reusable layers

The actual classical horn prefix space is `{0,1}^N`,
topologically Z2, with C3_ext as the independent
three-root sector count. Our existing
`AlexanderHornedBinaryPadicCylinderExact.agda`
keeps its finite binary projection distinct from
the already existing TERNARY p-adic cylinder.

Our new
`AlexanderHornedBinaryTernaryExistingCodecWeldExact.agda`
reuses BOTH already kernel-oriented codecs:
 - `Horn.left/Horn.right` -> Boolean -> existing
   balanced trit {-1,+1}, with centre 0 EXCLUDED,
   and exact roundtrip;
 - a general trit {-1,0,+1} -> two machine bits via
   the existing 00/01/10 code, 11 rejected, exact
   reverse roundtrip;
 - the existing independent binary/ternary
   `Resolution23` refinement diamond, with
   3 sector states refined by one binary horn digit
   to 6 sector/address states;
 - the existing C2/C3 dihedral owner. The ternary
   Weyl C3 shift is NOT closed on the embedded
   nonzero binary pair.

**NONCOLLAPSE**:
These are finite injective SYMBOL encodings and
commuting product resolutions. They are not additive
group isomorphisms Z2 -> Z3 or vice versa.

As topological SPACES, Z2 and Z3 are homeomorphic
Cantor spaces, but as topological GROUPS there is
no nontrivial continuous homomorphism in EITHER
direction. Proof: any continuous map from a pro-2
group to a pro-3 group has image simultaneously
pro-2 and pro-3, hence trivial. Equivalently all
finite images would have both power-of-two and
power-of-three order. The Agda codec weld proves
finite C2 vs C3 generator-order obstructions, not
the inverse-limit topological theorem.

External independent reference for Cantor but not
group equivalence:
`Tilings of the Infinite p-ary Tree and Cantor
Homeomorphisms`, Mediterranean J. Math. 2022:
https://link.springer.com/article/10.1007/s00009-021-01854-x .

## 5. Verification status

Finite A5 computational regression:
`scripts/alexander_horned_ore_residual_alternating_probe.py`
verifies 60/60 commutator witnesses, tests nested
4-stage actual word-evaluation compatibility,
checks faithfulness of 60-coordinate regular
permutation action, and checks both digit codec
directions. An equivalent independent local test
returned: 60 of 60 A5 commutator witnesses,
336 complete finite word-refinement comparisons,
96 descendants and 1024-letter longest reduced
test word, all PASS. This is not an infinite theorem.

New Agda owners are source-written; no exact-head
Agda kernel typecheck receipt yet. Parent workflow
remains draft. Strict attribution separates
external theorem (Hatcher; Ore; free-group
residual finiteness), source-written proof, finite
algorithmic regression, Agda kernel receipt,
geometry identification and physical validation.

## 6. Pareto proof/geometry cuts

P0 Geometry: construct actual symmetric three-arm
wild-ball collars, verify simply connected central
overlap, stage inclusion, and compactness/limit
transport into actual pi1. Classical one-root case
has Hatcher's published proof; do NOT re-prove it
from scratch.

P1 Kernel: run Agda with the actual standard library
and fix compiler errors in the Ore/codec/regular
consumer modules and the original horn owners.
Merge only after exact-head receipts and verified
outside-branch dependencies. DHR nonabelian fusion
and SFGC Clifford-to-M2 basis are donor RESULTS,
not hidden completions of this Pi1 group problem.

P2 Strong exact mathematical theorem: instantiate
general A_m commutator-section from Ore, combine
finite-stage separation and the colimit universal
property to certify residual finiteness in a true
group/topology formalisation library. The exact
compositional step is already in the new module.

P3 If wanted, find a compatible G_r->GL_n(Q_p)
with infinite image and specified operator/VOA
state consumer. The present family has only finite
images individually. Before selected Monster 3B,
supply actual group hom/intertwiner rather than
order-3 resemblance or dimensional matching.

No further independent quaternion, Cayley-Dickson,
Hopf or 369 carrier should be added merely to
repeat already established same-map rotation laws.
