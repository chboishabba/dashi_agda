# ABC six-permutation max-cut: oriented meridian orbit and three-class quotient

Date: 2026-10-30. **Source-owner branch:** draft PR #1244
\`alexander-horned-c3-equivariant-20261024\`.
**Proof posture:** finite Agda source-written, GitHub source readback pending final check,
independently reproduced 6-word and 36-action calculations. Agda/Lean
kernel checking and CI not run; 3D G2–G6 remain open.

## 1. First reuse the ACTUAL six-permutation owners

- \`DASHI/Core/TernaryRoleCarrierExact.agda\` owns the six typed permutations
  of a generic three-role carrier.
- \`DASHI/Foundations/TernaryEndomorphismConjugacyExact.agda\` owns
  \`TriPermutation\` and its six reversible ternary coordinate maps.
- \`DASHI/Foundations/TernaryPermutationS3LawsExact.agda\` owns
  the exact nonabelian S3 multiplication table, inverse and action.
- \`DASHI/Computation/SSSPThreeFrontierLinearExtensionQuotientBidiExact.agda\`
  owns six ABC/ACB/BAC/BCA/CAB/CBA linear orderings, which are an
  ORDERING application, not automatically a meridian peripheral action.
- \`DASHI/Mathematics/Topology/AlexanderHornedSectorDihedralS3EndExact.agda\`
  already extends the external C3 root-sector action to an abstract S3
  action commuting with end projections. This is **not** the internal
  child-generator action.
- \`DASHI/Mathematics/Topology/AlexanderHornedTernaryPantsMeridianBoundaryExact.agda\`
  is the existing canonical owner of the specific \`w=[a,b][b,c]\`
  source word. The new \`ABCSixPermutationPeripheralOrbit\` extension lives
  **in this same file**, not in a duplicated permutation group.
- \`proofs/horned_c3_lean/HornedC3/ThreeArmHatcherGroupTransport.lean\`
  is the existing conditional van Kampen consumer. There is no new
  geometric source certificate to mirror as if proved in Lean.
- Current PR reviews: #1438 Agda trialectic directed 3x3 graph
  and downstream dashi_lean4 #103 are independent weighted-graph
  non-equivariance examples, not sources of the Horn boundary.
  #1414's S3/polynomial and #1405's sonic sectors remain independently
  owned; do not silently import their unmerged branches.

## 2. Exact six-oriented orbit of the parent word

Write uppercase for inverse letters. The three-child **selected** bonding
word, from the original ternary tower, is \`w=abAcBC\`.

| permutation images of (a,b,c) | cyclic representative beginning at positive a |
|---|---|
| ABC = (a,b,c) | \`abAcBC\` |
| ACB = (a,c,b) | \`acAbCB\` |
| BAC = (b,a,c) | \`aBcACb\` |
| BCA = (b,c,a) | \`aCAbcB\` |
| CAB = (c,a,b) | \`aCbABc\` |
| CBA = (c,b,a) | \`aBAcbC\` |

Each image is cyclically reduced length six and contains positive
\`a\` exactly once. Rotating its letters until that particular occurrence
comes first is therefore a **unique** representative of its cyclic
conjugacy class. The six displayed normal forms are pairwise distinct;
hence the six words represent SIX different oriented conjugacy classes
by the standard free-group cyclically reduced conjugacy criterion.
The finite Agda \`sixOrientedNormalFormsDistinct\` computes no repeated
anchored representatives; a complete formalization of the general
cyclically reduced conjugacy criterion is not claimed.

Inversion identifies precisely these conjugacy pairs:

\`ABC <-> CBA\`; \`ACB <-> BCA\`; \`BAC <-> CAB\`.

These are the right cosets of the chosen **unsigned** parent peripheral
stabilizer \`{identity, swap(a,c)}\` in S3: the three unoriented classes
are represented by ABC, BCA, CAB. The previously audited signed
permutation stabilizer has four elements in the larger 48-element group;
this is consistent with its two-element unsigned intersection.

## 3. Strong constructive repair: S3-covariant FAMILY, not fixed word

Let \`W(p)\` be the reduced word obtained by applying the existing
\`TriPermutation p\` to the three labelled child meridians.
Then, for all 6x6 permutation pairs, finite Agda reduction establishes

\`W(p*q) = reduce(p(W(q)))\`.

The canonical boundary module's
\`ABCSixPermutationPeripheralOrbit.orbitFamilyEquivariant\`
checks all 36 cases by concrete \`refl\` (subject to exact-head kernel).
This is a genuine **six-word boundary family** stable under child S3,
whereas a **single chosen parent peripheral class** is not invariant
under local three-cycle. It does not produce a same-object 3D
homeomorphism, order-three action of the embedded complement,
geometric C3/S3-equivariant inclusion, or punctured-torus embedding.

\`orientationReversalPair\` checks the six cases for the
specific involution \`swap(a,c)\`, and
\`allSixMapToThreeUnorientedClasses\` checks the selected
orientation-forgetting family representation. No quotient
universal property or general infinite group orbit classification
has been kernel-proved here.

## 4. G2–G6 geometric acceptance gates, not optional source reinterpretations

- **G2:** selected cap-collar-disjoint PL slide supports, homeomorphism,
  inverse and action on actual complement.
- **G3:** actual properly embedded once-punctured-torus boundary in that
  three-child complement, not an abstract mapped surface.
- **G4:** based naturality of the *actual inclusion* on child meridians,
  including conjugating path for nonlinear Nielsen
  \`phi(w)=q*w*q^-1\` with \`q=c a^-1 c a^-1\`; either prove orbit-indexed
  geometric multi-boundary equivariance or retain a single selected
  word and its reduced stabilizer.
- **G5:** compatible nested stage embeddings with shrinking geometry,
  stable collars and genuine wildness; preserve the already existing
  **external** root-sector action independently.
- **G6:** identify the actual wild exterior fundamental group using
  the existing conditional van Kampen/open-exhaustion machinery.
  The three-sector *binary Hatcher* theorem is not automatically a
  single-root *ternary bonding* theorem.

## 5. Provenance and verification

Classical mathematical priority: permutations/S3 (Dixon–Mortimer),
free-group normal forms and Nielsen automorphisms, Alexander 1924
wild sphere and Hatcher *Algebraic Topology*, Example 2B.2
(https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), handlebody relative
mapping classes and van Kampen. Hatcher's original source constructs
binary rather than the presently proposed ternary parent meridian.

The contribution here is a **source-specific six-word action audit,
the orientation-forgetting three-class discriminator and the
source-written 36-case algebraic orbit-family law**. These reuse and
extend original DASHI owners; source text, actually executed
independent computations, and Agda kernel acceptance are different
evidence types. The finite 48-case script was extended rather than
duplicated; no exact-head checkout execution of that committed Python
file, no Agda/Lean kernel and no CI are claimed.

The SSSP ordering, polynomial root S3, weighted trialectic 3x3
non-invariant graph, synthetic five-orbit sonic operators and
Ibrahim/Monster 3B multiplicity work have separate object types,
proof ownership and attribution. A common S3 or 3/6/9 count
does not imply equivalent representations or physical interpretation.
No protected ESD surfaces were edited.


### 2026-10-30 genus-one transport across the six labels

The canonical Agda owner was further extended with
\`sixPuncturedTorusBoundary\`, a six-case source-written equality
transporting the ORIGINAL Nielsen commutator coordinates
\`u=b^-1\`, \`v=c^-1 a\`, \`p=a b a^-1 c\` through each S3
child-generator relabelling. For each sigma,

\`reduce(sigma(p)^-1 sigma(w) sigma(p)) = reduce([sigma(u),sigma(v)])\`.

The equality is a direct free-word computation for each of six
explicit existing S3 constructors. It establishes that **all six
algebraic boundary words admit a genus-one mapped-surface
presentation**, not that six properly embedded punctured tori
have been constructed in the selected three-dimensional complement.
The geometric G3/G4 acceptance gate still requires actual surfaces
and peripheral based paths in the SAME complement.

An independent executable JS finite model checked all six transported
commutator charts, all 36 S3 family transport equations, six
orientation-reversal pairs and the 6/3 orbit counts (PASS). This
independent calculation is NOT execution of the committed Python
script, and neither calculation is Agda kernel verification.


## 6. Stronger constructive collapse: middle-child S3 index (2026-10-30)

The 6→3 orbit reduction is not an arbitrary matching chosen
by sorting words. It admits the **existing S3-equivariant three-code
index**

\`middleChildIndex(p) = p(b)\`.

The three fibres, each of size two, are:

| middle-child image | oriented members, conjugacy/inversion pair |
|---|---|
| b | ABC / CBA |
| c | ACB / BCA |
| a | BAC / CAB |

The source-owned \`ABCSixPermutationPeripheralOrbit\` now proves by
36 literal finite cases \`middleChildClassCriterion\`:
\`p(b)=q(b)\` iff the selected parent images are conjugate **up to
inversion**. The existing theorem
\`TernaryPermutationS3LawsExact.applyComposition\` proves
\`middleChildIndexEquivariant\` without a new multiplication table:
\`middleChildIndex(p*q)=p(middleChildIndex(q))\`.
Six cases of \`middleChildOrientationFlip\` show right multiplication
by the orientation-reversing transposition \`swap(a,c)\` preserves
this class label.

This is an **equivariant classification of a three-element algebraic
peripheral-class orbit**, and a reusable abstract S3-set chart.
It is *not* an equality of internal child meridians with the external
root sectors or a geometrically realized local S3 homeomorphism.
This clarifies the G4 choice: build a geometric fibre of six
oriented boundary charts over the three middle-child class labels,
or retain one selected class with only its stabilizer. No new
three-dimensional supplier is constructed.

Independent Python finite verification passed all 36 pairwise
class-equivalence tests and 36 index-equivariance tests. These are
not exact-head Agda kernel receipts.


## 7. Ibrahim / polynomial non-promotion cross-check (actual Agda files read)

Read source on \`master\`:
\`DASHI/Wikimedia/IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact.agda\`
and \`DASHI/Moonshine/Monster3BHighestAlphaValidation.agda\`.
The former explicitly proves/records a crucial type distinction:
**six position labels are not a six-dimensional vector space**;
more generally 90 chosen multiplicity-basis labels are not by
themselves an inertia linear representation and a character
decomposition 12+78 does not give a permutation action on
\`Fin 90\`. Its mathematical priority credits Barraclough–Wilson
(2007), Serre (1977), prior Ibrahim models and the existing DASHI
linear-action and snowball attribution owners.

Also read actual independent polynomial PR #1414 files
\`PolynomialHornedPerfectGroupObserverExact.agda\` and
\`PolynomialHornedSpinSignNonDescentExact.agda\`.
These distinguish commutator-generated groups from a claim that
every element is a single commutator, and distinguish Q8/V4
sign loss from 2I/A5 or S5. Nothing there equates the six
ABC boundary classes with a Monster permutation or linear
representation. The new three-class quotient is only a
source-owned **S3-set**, not a representation of a Monster
3B normalizer, a faithful braid action, physical spin holonomy,
or a same-object wild-exterior computation.


## 8. Strict local periodic C3 cannot be rescued by basing (2026-10-30)

The six-word S3 orbit remains a valid **algebraic family**, and
the middle-child index remains S3-equivariant. However
\`phi²(q)phi(q)q=w^-1\`, so the based-normalised local
\`psi=Inn(q^-1)phi\` fixes \`w\` but
\`psi³=Inn(w)≠id\`. The classical free-group centralizer
theorem gives every alternative conjugator \`q w^k\`
and twists \`w^(3k-1)\`, never 1. The **single selected
based word** therefore cannot carry a strictly period-three
lift of this particular phi, despite unbased phi^3=id.

See [new periodic-cap/cocycle max-cut](AlexanderHornedPeriodicCapCocycleMaxCut20261030.md).
Newman's 1931 periodic-homeomorphism theorem independently
forbids any finite-order nontrivial Nielsen action fixing a
relatively open boundary disk pointwise in a connected
genus-three handlebody. Nonperiodic cap-supported handle slides
and external-sector S3 remain distinct open/available lanes.
Source-written exact Agda witnesses; paper classical theorems;
Agda/Lean kernel and actual 3D source-specific geometry pending.
