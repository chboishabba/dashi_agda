# Alexander horned sphere x C3: equivariant three-manifold cut

Status: **finite formal algebra source-written; finite A5 audit passed locally;
geometric realization and Agda kernel check open**.  2026-10-24.

## Sources, attribution, and scope

- **[S: classical topology]** J. W. Alexander's 1924 horned sphere,
  and A. Hatcher, *Algebraic Topology*, Example 2B.2, pp. 170--172:
  https://pi.math.cornell.edu/~hatcher/AT/AT.pdf
  Hatcher proves the binary-horn model with exterior group an injective
  direct limit of free groups, and trivial abelianization.
- **[S: related higher order]** N. W. Riebe (1968), *The Fundamental
  Groups of the Complements of Some Solid Horned Spheres*,
  https://digitalcommons.usu.edu/etd/6821/ .
  Riebe's higher-order models and A5 representations are prior art;
  **do not identify their groups with Hatcher's exterior group**.
- **[R: reused repository]** `DASHI/Core/FiniteC3OrbitStabilizerExact.agda`,
  `DASHI/Core/C3OrbitVerticalDynamicsExact.agda`,
  `DASHI/Mathematics/Topology/PoincareGeometrizationExactBoundary.agda`.
- **[N: new algebraic cut]** Three C3-labelled independent binary horn
  trees, braid permutation shadow, iterative equivariance, A5^3
  detector, and the conditional exterior-meridian interpretation.
- **[G: geometric gate]** There is currently no proved equivariant wild
  embedding, no geometrically certified van Kampen isomorphism, and no
  formal Out(pi1) result. This is NOT a proof about gravity, KK, Monster
  moonshine, three-dimensional spacetime, or the Poincare conjecture.

## 2026-10-24 maximal geometric consolidation (new)

The **highest-alpha construction** is now a boundary-connected sum of three
*existing* Hatcher horned balls, arranged by the ambient order-three rotation
`(x,y,z)->(z,x,y)`, connected via three unknotted tame tube collars and
a central round ball. See
`Docs/topology/AlexanderHornedC3ThreeCopyGeometricConstruction.md`
for the detailed local van Kampen cuts and the actual geometric proof plan.

The associated infinite group is explicitly
`G_A * G_A * G_A`, not an unrelated new group: filtered colimits
of the three independent binary towers agree with their free product.
The rotation cyclically permutes the three free factors. A projection
to the first factor immediately proves it is non-inner: a nontrivial
first-factor meridian remains nontrivial after conjugation and
projection, whereas its cyclic rotation projects to the identity.
This removes the need to make A5³ a logical dependency for
noninnerness. A5³ remains a finite independent detector.

NEW exact Agda modules:
- `AlexanderHornedC3ComplementActionExact.agda`: complement
  point-set invariance for any invariant subset of an order-three
  ambient map, with pointwise cubed identity.
- `AlexanderHornedC3FreeFactorDetectorExact.agda`: target-group
  conjugation cannot kill nonidentity elements and the complete
  conditional first-factor noninnerness theorem.

NEW executable independent finite regression:
`python3 scripts/alexander_horned_c3_free_factor_probe.py`:
937 reduced words through length 4, binary-horn substitution and
threefold rotation consistency, and first-sector retraction against
937 conjugators. **Passed locally in this session**.

**Certification remains precise:** concrete topological disk collars,
ambient horned-ball embedding and exact pi1 identification are
described as a mathematical construction/proof specification, not as
Agda kernel-certified geometric data. Agda typechecking is not
available here. No physical or moonshine promotion follows.

## Exact three-root algebraic model

Index meridians at stage n by (c,w) with c in C3 and w in {0,1}^n.
Let F_n = F_{3*2^n} be free on x_(c,w). Define

    phi_n : F_n -> F_(n+1)
    x_(c,w) |-> [x_(c,w0), x_(c,w1)].

This is the **three-root modification** of the binary-system
presented in Hatcher; it is not a claim that the standard one-root
Alexander sphere already has threefold rotational symmetry.

The maps phi_n are injective. Indeed F_(n+1) splits as the free
product of rank-two free groups indexed by (c,w). In each rank-two
factor the nontrivial commutator has infinite order, so the cyclic
group on x_(c,w) injects. Their free product is injective.

Set G = colim F_n. Each nontrivial generator at any finite stage
stays nontrivial by injectivity; each generator is also a commutator
at the next stage. Consequently

    G != 1,              G_ab = 0,

so every homomorphism G -> C3 is trivial (indeed the same holds for
every abelian target). This is a statement about G, not yet about
the fundamental group of a realised three-manifold.

The map r(x_(c,w)) = x_(c+1,w) commutes with every phi_n, so gives
an automorphism r of G of order dividing 3. It is nontrivial: it
moves distinct free generators already at stage 0.

The permutation quotient B3 -> S3 maps standard braid generators to
(01) and (12); their product acts as (012). The finite Agda module
checks these exact permutation identities. It does **not** realise a
faithful B3 action on an exterior or infer topology from a braid-word
coincidence.

## Nonabelian detector: A5^3

The audit `scripts/alexander_horned_c3_a5_probe.py` enumerates all
60 even permutations in A5 and checks, by exact finite arithmetic:

1. Every A5 element is a commutator of two A5 elements (60/60).
2. There exists a pair a,b generating A5 with g=[a,b] != 1.
3. Assign g to the root, and a,b to its two children. Recursively
   assign each later parent a commutator witness, at arbitrary depth.
4. Repeat this assignment independently in three direct factors
   A5 x A5 x A5, one factor per sector.
5. The threefold sector rotation intertwines with the cyclic
   permutation beta of factors, and beta^3=identity.
6. Since generators at depth 1 generate A5 in each factor, compatible
   meridian assignments generate A5^3 at every later level.

Algebraic consequence: the finite-compatible assignments define a
**surjective C3-equivariant homomorphism** Q : G -> A5^3. The cyclic
factor permutation beta is not inner: any inner automorphism of A5^3
preserves each direct factor, but beta moves the first to the second.

If r were inner on G, surjectivity and equivariance would force beta
to be inner on A5^3. Contradiction. Thus **the induced outer class of
r in Out(G) has exact order three**.

The preceding passage to the abstract direct limit follows from the
explicit compatible assignments and the universal property of a
colimit. The script is an exhaustive finite check, not a kernel-level
formalisation of that universal-property proof.

## Exact repo modules

- `DASHI/Mathematics/Topology/AlexanderHornedC3AmbientRotationExact.agda`:
  order-three coordinate permutation of an ambient triple, marked-axis
  C3 intertwining, and rotation fixing the infinity point of the
  compactified point-set carrier (topology still unproved).
- `DASHI/Mathematics/Topology/AlexanderHornedC3FiniteStageExact.agda`:
  C3-labelled binary addresses, degree-three rotation, braid relation
  in S3, word action, commuting iterated commutator substitution, and
  vanishing of C3 characters respecting each generator relation.
- `DASHI/Mathematics/Topology/AlexanderHornedC3ExteriorBridge.agda`:
  explicit group and action interface, conditional word interpretation,
  and preservation of every finite horn replacement.
- `DASHI/Mathematics/Topology/AlexanderHornedC3CharactersExact.agda`:
  C3 group-character structure; conditional theorem that any C3
  character is trivial if all loop classes admit meridian words.
- `DASHI/Mathematics/Topology/AlexanderHornedC3OuterDetectorExact.agda`:
  conditional theorem transporting a non-inner cyclic action from a
  surjective equivariant quotient back to the source loop group.
  The A5^3 quotient is not instantiated in Agda yet.
- `DASHI/Mathematics/Topology/AlexanderHornedAbelianHolonomyBIDIExact.agda`:
  same-group BIDI/consumer cross-check: all *abelian* characters kill
  recursive meridians, fail to recover an essential loop, and are blind
  to C3 rotation even when the separately supplied nonabelian quotient
  proves that rotation outer. This is restricted to flat holonomy,
  not nonflat Wilson loops or physical KK field equations.
  Details: `Docs/physics/AlexanderHornedKKFlatHolonomyBIDISteelman20261024.md`.

These are **conditional type-theoretic results**, not instances for
the real three-manifold. In particular a finite word moving under C3
does not by itself prove that the corresponding geometric outer
automorphism is nontrivial.

## Geometric bridge: exact missing obligations

Choose a standard 120-degree rotation of S3 (the one-point
compactification of R3). The exact coordinate action can be chosen
as (x,y,z) -> (z,x,y), with determinant +1 and diagonal fixed axis;
its order-three point-level equations are implemented in
`AlexanderHornedC3AmbientRotationExact.agda`. This does not yet
prove continuity or that the horned-ball subset is invariant. Begin with a round 3-ball and attach three
pairwise disjoint, unknotted, rotationally permuted initial handles.
Perform Hatcher's two-interlocking-horn replacement on every handle,
in rotationally symmetric disjoint neighborhoods, with rapidly
shrinking widths.

- **G1, construction:** specify PL/smooth X_n with X_(n+1) subset X_n
  and r(X_n)=X_n; verify disjoint handles and uniform diameter bounds.
- **G2, limiting embedding:** construct homeomorphisms h_n on the
  central balls; prove uniform convergence, injectivity at the
  Cantor-set limit, and the limit H is homeomorphic to D3. Deduce
  boundary H is an embedded S2, invariant under r.
- **G3, group identification:** for Y_n=S3 minus X_n, prove by van
  Kampen pi1(Y_n) = F_(3*2^n) with inclusions exactly phi_n.
  Prove pi1(S3 minus H) = colim pi1(Y_n) by compactness of loops
  **and homotopies**, with compatible basepoints.
- **G4, symmetry and detector:** prove the geometric rotation acts on
  meridians by (c,w)->(c+1,w), including coherent basepoint paths
  where needed. Transport the abstract outer-order-three result
  through the group identification. Then the complement has perfect,
  nontrivial pi1 and a nontrivial C3 outer action.

The target exterior S3 minus H is an **open noncompact 3-manifold**;
closed simply-connected three-manifold classification does not apply.
Do not equate the horned sphere S2 with the ambient S3 or confuse an
action C3 -> Out(pi1) with a character pi1 -> C3.

## Acceptance and audit

Run from the repo root:

    python3 scripts/alexander_horned_c3_a5_probe.py
    python3 scripts/alexander_horned_c3_free_factor_probe.py
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3AmbientRotationExact.agda
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3ComplementActionExact.agda
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3FreeFactorDetectorExact.agda
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3FiniteStageExact.agda
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3ExteriorBridge.agda
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3CharactersExact.agda
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3OuterDetectorExact.agda
    python3 scripts/check_alexander_horned_abelian_bidi.py
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedAbelianHolonomyBIDIExact.agda

The A5 finite probe passed in a local Python run (depth 5, 32
meridians per sector). There is **no Agda compiler in this execution
environment** and thus no kernel receipt. Do not mark Agda checks
passed until independently run.

## Highest alpha next

First certify G1-G3 with an explicitly equivariant Hatcher handle
replacement. The nontrivial Out(G) obstruction is already available
as a concrete, falsifiable algebraic target. On the algebra side,
implement the free-group coproduct/commutator injection, direct
limit, and A5 finite permutation certificates in an available
group-theoretic formal library rather than adding another ad hoc
three-manifold or physics abstraction.


## 2026-10-24 formal topology library import and tested geometry placement

The three-piece van Kampen calculation now has a **real Lean topology
library consumer**, rather than only an Agda record of presumed group
laws. See
`proofs/horned_c3_lean/HornedC3/ThreeArmVanKampen.lean`.
It imports the externally authored, kernel-proved
`Hatcher.VanKampen.freeProductEquivFundamentalGroupOfRelationsTrivial`
and
`relationSubgroup_eq_bot_of_overlap_subsingleton`
from Deicyde/hatcher-at, pinned at
`fb20d71b6a7561c80f66350c14af118f3962377a`.
That source's mathematics, authorship and published formal proof are
NOT original to DASHI. The DASHI consumer assembles their theorem for
three actual open sets `U : Fin 3 -> Set X`, requiring open cover,
path-connected members and intersections, a common basepoint and
trivial off-diagonal overlap fundamental groups. When given those
particular certificates it returns a group isomorphism from the real
cover free product to the real `FundamentalGroup X x0`, preserving
the inclusion-induced map.

**Critical limitation:** no inhabitant of that `ThreeArmCollarCover`
has yet been constructed for the actual Hatcher three-copy complement.
The source-written Lean consumer is not itself locally typechecked.
It therefore does NOT close the wild-embedding, collar
contractibility, finite-stage compatibility or limiting pi1 theorem.

The independently executed Python exact-fraction audit
`scripts/alexander_horned_c3_collars_audit.py` confirms the following
concrete placement: central center (0,0,0), satellite centers 9e1,
9e2, 9e3, radius-one envelopes, three radial tube *candidate boxes*
with longitudinal coordinates [3/4,17/2] and transverse bounds
[-1/8,1/8]. Exact inequalities establish pairwise separation of
satellite envelopes, disjointness of the three tube boxes, avoidance
of foreign satellite envelopes, and intended overlap with each
tube's own satellite envelope and the central ball. The squares
of satellite--central and satellite--satellite center distances are
respectively 81 and 162, source-written as exact Agda identities in
`AlexanderHornedC3SatellitePlacementExact.agda`. Neither calculation
constructs a tubular collar attaching to the *wild ball* along a
specific tame disk, nor proves its intersection is contractible.

The focused kernel acceptance commands are:

    bash scripts/check_alexander_horned_c3_exact_head.sh
    cd proofs/horned_c3_lean && lake update && lake build

The GitHub Actions attempt is in
`.github/workflows/horned-c3-focused.yml`. Never report a check as
kernel-verified unless exact-head log receipts from the relevant
compiler have been returned. This session's runtime has neither an
Agda nor a Lean executable and the newly requested workflow runs
had not returned a successful job receipt at the time of writing.

## Jordan and VOA scope

`AlexanderHornedC3JordanActionExact.agda` proves that on any
commutative magma satisfying the Jordan identity, the componentwise
threefold product again satisfies that identity and cyclic coordinate
permutation preserves the product. It does NOT establish full Jordan
vector-space axioms or any physical/Monster/Albert identification.
This is an auxiliary representation of the same abstract C3, not a
geometric source map.

The existing
`DASHI/Moonshine/VertexOperatorAlgebraCore.agda`,
`DASHI/Moonshine/VertexOperatorAlgebraLinearActionReceiptExact.agda`,
`DASHI/Moonshine/Base369Monster3BVOAActionPhaseAdapterBidiExact.agda`
and
`DASHI/Biology/MoonshineWeightTwoGriessProductSchemaExact.agda`
are candidate consumers. To connect the actual geometric automorphism
to their state actions, a **specified group representation**
`pi1(E) semidirect C3 -> Aut(V)` is required. An order-three
symmetry, Jordan shape, character coincidence or Griess dimension
alone does not supply that representation. A VOA tensor cube might
admit permutation symmetry once tensor-product and grading axioms
are supplied, but it is not used in the fundamental-group proof.


### Additional point-set collar lemma (Lean)

`proofs/horned_c3_lean/HornedC3/ThreeArmCollarIntersections.lean`
now defines actual subsets `U_i = C union S_i` and proves:

    for i != j, if S_i ∩ S_j = empty, then U_i ∩ U_j = C;
    for i != j, (U_i ∩ U_j) ∩ U_k = C for any k.

It also proves openness of each `U_i` from open `C` and `S_i`,
and common-basepoint membership when the point lies in `C`.
This discharges the **set-theoretic incidence step** for any three-arm
cover satisfying its separation hypothesis. The exact rational
tube-envelope audit supports how to arrange the sectors, but does
not itself furnish the open sets of the *wild complement* or a
contractibility proof for `C`.

Remaining geometric certificates, stated without inventing proof:
(1) actual `E_n` cover `C_n union S_(0,n) union S_(1,n) union S_(2,n)`;
(2) `C_n` open, contractible and containing the fixed basepoint;
(3) each `S_(i,n)` open, pairwise disjoint and with the expected
local-stage fundamental group; (4) van Kampen generator and stage-map
compatibility; (5) nested-limit homeomorphism and compactness
transport. After (1)–(3), the external kernel-proved van Kampen
consumer gives the stage free-product isomorphism.


## 2026-10-24 actual finite VOA representation max-cut

The specific source group and cyclic action now have a concrete
nonabelian finite quotient and a mathematically genuine, if
non-CFT-type, **180-dimensional c=0 VOA** representation.
The detailed theorem, constructive proof, source audit and exact
kernel are in
`Docs/topology/AlexanderHornedC3VOARealizationMaxCut.md`.

Let `G=G_A*G_A*G_A` (the **abstract** three-root commutator direct
limit) and `K=G semidirect C3`.
The exact finite A5 commutator section from the existing script
constructs a compatible surjection `G_A -> A5` at every stage,
thus `K -> A5^3 semidirect C3`.
On `V=Fun(C3 x A5,C)`, the latter finite group acts by
permuting coordinate idempotents, preserving the pointwise
commutative product, vacuum, modes and zero conformal vector.
By the classical finite-dimensional commutative VOA construction,
this yields a genuine nontrivial action of the abstract `K`
on a specified VOA, **without** asserting that this VOA is
`V-natural`.

The action is faithful on the finite quotient and retains all
`A5^3 semidirect C3` labels. Its exact kernel on `K` is
`ker(q) x {0}`, so it necessarily loses some infinite-group
information: `m^5 != 1` in the injective source free-group
tower, but the selected root meridian has finite image order
five. `m^5` therefore acts trivially on the whole VOA.
This supplies a concrete no-descent instance of the existing BIDI
consumer pattern, distinct from the earlier abelian-character
no-go. The quotient and VOA construction are mathematically
explicit; their corresponding full Agda kernel-level objects
are not yet built.

New exact algebraic Agda source:
`AlexanderHornedC3FiniteVOAActorExact.agda`,
`AlexanderHornedC3VOAModeLiftExact.agda`, and
`AlexanderHornedC3VOAKernelBidiExact.agda`.
The second reuses the repository's pre-existing exact rational
trivial-VOA mode theorems, not a newly asserted `preservesModes`
flag. Their proof statements distinguish pointwise equality from
equality of functions. The finite permutation audit is
`scripts/alexander_horned_c3_voa_a5_action_probe.py`.

This **resolves the abstract same-group existence question** but
does NOT supply (1) an actual geometric `pi1(S3\H)` identification
or (2) a map into the Monster or any selected 3B action on
`V-natural`. The geometric Lean collar proof and exact-head
Agda/Lean compiler receipts remain independent highest-alpha
tasks. See the full source/consumer matrix in the new document.


## 2026-10-24 reuse: existing A5 to C3 (j=0..35) restriction

A literal repository search found no theorem named `A35`; the likely
existing mathematical owner is
`Foundations/PolyhedralFiniteRestrictionInstancesExact.agda`
with its `icosahedralC3` probe, built from
`IcosahedralSO3RestrictionJ0To35Exact.agda` and
`PolyhedralFixedSpaceSpectrumJ0To35Exact.agda`.
Those are **existing** Serre/Fulton–Harris finite-group restriction
calculations, not original horned-VOA discoveries.

The arrow is `C3 ↪ A5` with representation restriction from A5
to C3. There is no nontrivial homomorphism `A5 -> C3`.
The horn-sector C3 remains another, independent action. Selecting
one order-three element s of A5, its diagonal action
`((s,s,s),0)` commutes with the outer horn-sector rotation
`((1,1,1),1)` in `A5^3 ⋊ C3`. Together they generate
`C3_internal × C3_external` on the **same** finite VOA
coordinate algebra `Q^{C3 × A5}`.

The exact A5 3-cycle action on 180 points is free for all nine
subgroup elements except the identity: there are **20 orbits of 9**.
The complexified permutation representation is therefore twenty
regular representations of `C3×C3`, with each of the nine
cyclotomic eigenspaces of dimension 20. The A5 character table
computes the same internal fixed dimension
`1·1 + 3·1 + 3·1 + 4·2 + 5·1=20`; the j=0..35 third-turn
character average is imported, not recomputed.

Exact new owner modules:
`AlexanderHornedA5C3RestrictionWeldExact.agda` proves internal
versus external C3 commutation on the same finite actor's slots
and pointwise rational vertex modes, internal period three,
nonidentity, and exact reuse of the prior j-scan character average;
`AlexanderHornedA5C3CharacterRestrictionExact.agda` reuses
the actual A5 third-turn irrep table and fixed-space formula.
Finite audit: `scripts/alexander_horned_a5_c3_restriction_weld.py`.
Independent local finite reproduction PASSED for all 180
coordinates, all nine subgroup phases, 20 orbits, 60/60 A5
commutators and 36 j values.

**Still unproved**: identifying the existing abstract icosahedral
representation with the particular finite Q[A5] regular-VOA
carrier by a same-object intertwiner; an Agda 60-element
permutation-group instance of the generic factor actor; an
explicit ambient SO3 axis-alignment transporter; geometric
horned exterior pi1, and all exact-head Agda kernel receipts.
Do not promote identical C3 phase counts to Monster 3B identity.

Canonical detailed proof/source ledger:
`Docs/topology/AlexanderHornedA5C3RestrictionVOAWeld20261024.md`.


## Torsion versus twisted horns, primary-source audit

Hatcher's printed pages 171–172 explicitly verify that the
**standard** Alexander horned-ball exterior has a free-group
injective tower `F_(2^n) -> F_(2^(n+1))` and is their compactness
limit. Thus the classical exterior group is **torsion-free**:
every element belongs to some free stage; nonzero powers of a
nontrivial free-stage word remain nontrivial by injectivity.
Its simultaneously trivial abelianization makes it perfect,
not trivial. Perfectness alone does NOT establish torsion-free
(for example A5 itself is perfect and has order-three elements).

The **three-root abstract group** has the same property because
its tower is three independent copies of these injective free
maps. That is an abstract mathematical fact, distinct from
certifying the proposed three-copy wild embedding and its pi1.

The phrase 'twisting horn' denotes geometry, not a relation
`m^3=1` in the fundamental group. The analogous braid
`b=sigma1 sigma2` maps to an order-three permutation, but
`b^3` is a nontrivial full twist: its B3 exponent sum is 6,
not 0. Likewise a 120-degree ambient rotation is an element
of an AUTOMORPHISM group, not a loop class in the complement.
Other 3-manifolds can have torsion fundamental groups:
`pi1(RP3)=C2` or `pi1(L(3,1))=C3`. None of these imply a
new relation in the Alexander exterior.

An independent finite A5 audit chooses the root meridian image
to be an actual order-three 3-cycle `s=(0 1 2)`. It finds A5
generating children whose commutator is s. Therefore
`q(m)^3=1=q(m^3)`, yet `m^3 != 1` in the abstract source.
This sharpens the earlier order-five kernel witness. An actual
geometric source interpretation still requires the collar
van Kampen stage maps.

New exact owner:
`AlexanderHornedTorsionFreeStageTransportExact.agda` proves
torsion-free transport given power-preserving injective stage
embeddings covering the target, plus the impossibility of an
order-three source lift of a nontrivial C3 quotient image.
The target's torsion-freeness is NOT a premise of that lemma.
`scripts/alexander_horned_torsion_steelman_probe.py` provides
a finite reduced-word and A5 quotient check; the standalone
independent local equivalent check passed.

**Riebe source warning:** Riebe (1968), `The Fundamental
Groups of the Complements of Some Solid Horned Spheres`,
abstract describes groups G^k that are free of countably
infinite rank. Such a group cannot be identified with the
NONTRIVIAL PERFECT classical Hatcher exterior group, as a
nontrivial free group has nonzero abelianization. Access to
the primary thesis PDF failed (403), so this is an unresolved
source/object-identification issue; do not promote it as a
contradiction in either author's mathematical proof or as a
direct justification of this specific G. Detailed analysis:
`Docs/topology/AlexanderHornedTorsionTwistSteelman20261024.md`.

Kernel typechecks and actual three-copy geometric van Kampen
are still independently required. This finding changes no
Monster or Jordan/VOA promotion status.


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


## 2026-10-24 impasse break: finite alternating separation and existing codec/actor reuse

Canonical source ledger:
`Docs/topology/AlexanderHornedOreResidualFiniteImpassBreak20261024.md`.

The earlier theorem `pro-p(G)=1` for all p is CONSISTENT
with a much stronger **positive** result: the abstract
Hatcher-type injective free-group/commutator direct limit
is RESIDUALLY FINITE (indeed finite-alternating separated).
For any nontrivial finite-stage word, residual finiteness
of free groups detects it in a finite quotient embedded
faithfully in an alternating group A_m. Ore's 2010
commutator-surjectivity theorem for simple finite groups
lets that quotient assignment extend through EVERY
subsequent binary horn subdivision, since
`x_w -> [x_w0,x_w1]`. Backward stage maps come by
precomposition; their directed colimit yields a
whole-source finite quotient detecting the selected word.
Therefore the canonical map from abstract G to its
FULL profinite completion is INJECTIVE, despite every
pro-p and prosolvable completion being trivial.

The new `AlexanderHornedOreFiniteTargetExtensionExact.agda`
proves that precise word-evaluation invariance through
one and arbitrary finite horn refinements, for a
target with genuine group laws and a chosen Ore
commutator section. The actual finite A_m proof and
colimit homomorphism remains an external mathematical
theorem/formal-import obligation, NOT kernel-certified
by that local source alone.

The existing `PolyhedralRegularRepresentationShiftExact`,
`AlexanderHornedC3FiniteVOAActorExact` and
`AlexanderHornedC3VOAModeLiftExact` now have a
same-actor consumer
`AlexanderHornedNonabelianRegularPadicReuseExact.agda`
proving faithfulness of a selected group-factor
regular action by observing its identity coordinate,
plus equivariance of the EXISTING rational vertex modes.
Every finite A_m quotient embeds in GL_|A_m|(Z),
hence in GL_|A_m|(Q_p) for every p. The collection of
such finite-dimensional actors is JOINTLY faithful,
but no ONE finite A5 or fixed-dimensional VOA is
claimed faithful on G. The infinite product of these
weight-zero state algebras is not automatically a VOA.

The existing
`BinaryBalancedTernarySubcarrierExact`,
`VerifiedFiniteTritCoder`,
`Base369BinaryTernaryRefinement` and
`BalancedTernaryC2C3DihedralCodecBridgeExact`
are now consumed by
`AlexanderHornedBinaryTernaryExistingCodecWeldExact.agda`:
  - actual Horn Bit -> existing strict nonzero balanced trit;
  - arbitrary trit -> two machine bits (11 rejected);
  - existing commuting 2^a*3^b resolution diamond;
  - exact finite C2 versus C3 order obstacles.
These digit maps do NOT give a continuous additive
isomorphism `Z2 =~ Z3`. Both are Cantor spaces,
but Hom_cont(Z2,Z3)=Hom_cont(Z3,Z2)=0 as
topological GROUPS, via coprime pro-p images.

The existing `Physics.QFT.NonAbelianFusionFromSpin`
is a CONDITIONAL Rep(SU2)-fusion upgrade from an
abelian CM source, NOT an automatic A5/3D-horn
representation. Existing SFGC `CliffordToM2Iso`
provides a genuine BASIS bijection, not multiplication
compatibility of entire algebras. No redundant
quaternion/Cayley-Dickson/Hopf or 369 owner was created.

Independent local finite computation PASSED 60 A5
commutator-section witnesses and 336 free-word
naturality comparisons across four stages. The
committed finite script, the focused workflow and
the exact-head Agda runner now include the new owners.
No successful exact-head Agda kernel/Lean geometry
receipt has been returned; the actual three-copy
wild-complement identification remains open and
PR #1244 must stay draft.


## 2026-10-24 max-cut: true spin-icosahedral / CRT / integral p-adic congruence bridges

Consolidated technical report, with exact primary source attribution:
`Docs/topology/AlexanderHornedCRTSpinPAdicVOAMaxCut20261024.md`.

**Previously built donor owners** include the genuine
`SixWheelCRTExact`, `Base369BinaryTernaryRefinement`,
`BinaryBalancedTernarySubcarrierExact`,
`U1AsSU2AbelianRestrictionExact`,
`NonAbelianFusionFromSpin` (conditional!),
literal quaternion/Hopf/Q8, and
`BinaryPolyhedralMcKayDimensionExact` (E8-dimensional
skeleton ONLY). These were inspected and reused, not reinvented.

**New literal 2I (spin) finite quotient**:
`scripts/alexander_horned_spin_icosahedral_bridge.py`
enumerates SL2(F5) (120), its FIVE Q8 subgroups and their
normalizer order 24, their conjugation action on five
subgroups (all 60 A5 elements, exact kernel +/-I),
non-splitting by the unique involution, and actual
order-six rotor whose cube is -I. It also enumerates a
commutator pair for EVERY 2I element (120/120) and a
root pair generating the full 120. Thus a compatible
three-root Hatcher abstract group -> 2I^3 quotient can
be explicitly defined stage-by-stage. The root cube
remains nontrivial central -I in 2I and is erased in
the old 180-dimensional A5 quotient.

**Concrete strict VOA improvement**:
functions on C3×A5 (180 coordinates) embed via pullback
into functions on C3×2I (360 coordinates). Old rational
pointwise vertex modes, action and the observer now live
on compatible SAME coordinate charts. New
`AlexanderHornedSpinVOAFactorFunctorExact.agda` proves
the nine actual sector/phase naturality cases, mode
equivariance, and injectivity pointwise from a proven
surjective group factor. New
`AlexanderHornedBinaryIcosahedralSpinSignBidiExact.agda`
proves the central sign cannot be recovered from the
projective A5 observer; the exact finite group supplier is
currently a Python receipt, not an Agda 120-element group
instance. Neither actor equals the Monster VOA.

**Mixed binary/ternary**:
`AlexanderHornedMixedPrimeCRTWeldExact.agda` reuses
the genuine old 2×3 CRT, 2^a3^b resolution lattice,
and bit-in-balanced-trit subcarrier. Adds the *reverse*
fixed 2-bit encoding of three balanced trits with
11 explicitly unused, proves roundtrip on image,
and proves sector-rotation commutes with binary horn
cylinder forgetting. The whole inverse-limit CRT
`C3×Z2 = lim Z/(3·2^n)` is a classical math
consequence, not asserted as an already kernel-proved
Agda ring equivalence. Independent finite CRT audit
`alexander_horned_mixedprime_congruence_audit.py`
passed 6,141 finite states n0..10, general 2^a3^b
for a,b=1..4.

**Real low-rank p-adic restriction**:
classical congruence kernel GL_n(Zp)->GL_n(Fp)
is pro-p. A perfect horned G maps trivially to any
solvable group and any pro-p group. Since GL2(F2)
derived series is 6→3→1 and GL2(F3) is
48→24→8→2→1 (exhaustively computed), ANY integral
G->GL2(Z2) or G->GL2(Z3) is trivial.
The source-level
`AlexanderHornedPadicCongruenceNoGoExact.agda`
uses the old finite-solvable meridian theorem and
separating congruence reductions. This does NOT
block higher-rank/noncompact Qp representations or
ordinary nonabelian A5/2I finite quotient matrices.
SL2(F5) is NOT automatically a 2D Z5 integral lift.

**Still open:** exact-head Agda kernel receipts and
the particular three-copy geometric exterior pi1
identification. No faithfulness of G or equivalence to
Monster 3B is promoted.


## 2026-10-24 strict Spin(3) 360/720 cover audit

The precise standard theorem is **Spin(3)=SU(2) -> SO(3) TWO-to-ONE**.
SO(3) rotations themselves close at **360deg/2pi**. The
identity-starting path lift of a full 360deg rotation ends at
the central quaternion `-1` (not `+1`), so spin-half
amplitudes close at **720deg/4pi**. This is why a 360deg
SO(3) *loop* is noncontractible even though its endpoint
is the identity rotation; the doubled 720deg loop is
contractible. `pi1(SO3)=C2` is NOT `pi1(horn exterior)`.

Previously established owners:
- `Foundations/SU2SO3IrrepDimensionExact.agda` proves the
  spin-half highest-weight-one representation does not
  descend to SO3 and integer-spin even-weight lane does.
- `Algebra/FiniteQuaternionDoubleCover.agda` has exact
  kernel/fibres for FINITE `Q8->V4`, not the full continuous
  SU2->SO3 cover.
- `Algebra/CliffordSpinLift.agda`, `Physics/SpinAssumptions.agda`,
  `Algebra/ContinuousSpin31LorentzCover.agda` carry
  conditional/status/other-signature interfaces; these
  are not completed topological double-cover proofs.
- `AlexanderHornedQuaternionC3SpinExact.agda` already
  proves q=(1+i+j+k)/2 has `q^3=-1` and
  `(-q)^3=+1`, with both inducing the *same actual*
  120deg spatial map.

NEW exact finite witness owner
`AlexanderHornedSpin360720Exact.agda`
reuses Q8->V4, proves `rho(-1)=rho(+1)`,
`-1!=+1`, `(-1)^2=+1`, `i^2=-1`,
and imports the pre-existing spin-half descent and
threefold horn rotor theorems. Reproducible exact
Fraction audit: `scripts/alexander_horned_spin_360_720_audit.py`.
It does NOT construct the universal-cover path-lift
theorem or the geometric horned pi1.

Full source/proof boundary:
`Docs/topology/AlexanderHornedSpin360720CoverAudit20261024.md`.

**Number trap**: the 360-coordinate finite spin VOA
`Fun(C3×2I,Q)` has vector-space dimension 360,
which has NOTHING to do with the 360-degree SO3
period. Its 180-coordinate A5 quotient likewise
is NOT a half-turn interpretation.


## 2026-10-24 C3 steelman: strict spin action versus 720-degree angular path

See canonical attributions, exact data and proof-status ledger:
`Docs/topology/AlexanderHornedC3SpinLiftSteelman20261024.md`.

**P0 mathematical break:** restricting Spin3->SO3 to the
actual 120deg C3 subgroup gives a SPLIT central extension
`C6 ≅ C3×C2`, since `H²(C3,C2)=0`. The old rational
quaternion `q=(1+i+j+k)/2` (order 6, q³=-1) is the
identity-started +120deg PATH lift, NOT a homomorphic C3
generator. The same rotation's other lift `-q` has
order 3, giving a genuine spin-equivariant C3 action.
Neither lift changes the torsion-free source exterior G.

**Agda exact source:** `AlexanderHornedC3SpinLiftSplitExact.agda`
reuses EXISTING `FiniteC3OrbitStabilizerExact`, Q8 signs
and ambient horn C3. It constructs the six-element spin
preimage, a strict homomorphic C3 section, unique
order-three generator lift, a nonhomomorphic path-section,
and proves by all nine cases that the path's central
carry cocycle is an EXPLICIT coboundary.
No continuous covering-space Agda kernel certificate
has been created.

**A same-coordinate Dirac field consumer exists** on ANY
C3-invariant open subset E of R3:
`Tψ(x)=U(-q)ψ(R^-1 x)`,
`T³=1` and `DT=TD` on
compactly supported two-component spinors.
The Gaussian-rational `spin_dirac_probe.py` checked
all three Pauli/Dirac coefficient identities and
125 exact finite position/spinor samples.
This requires `R(E)=E` for the *actual* wild
embedding, not a completed fundamental-group theorem,
nor any spectral domain/self-adjointness statement.

**Fixed-axis and characteristic-3 discriminator:**
`tr(U(-q))=-1`, `det(U(-q)-I)=3`; fixed-axis
C3-invariant spinor values vanish in characteristic
zero. On each free 3-position orbit with two spin
components, the exact averaging projector
`P0=(I+T+T²)/3` is idempotent of rank 2.
The Q3 2D cyclotomic block has zero fixed dimension,
whereas reducing it modulo 3 yields a unipotent
representation with a 1D fixed subspace. This is
Maschke failure, not a new characteristic-zero zero
mode or Monster eigenspace. The existing C3Fourier/
C3CyclotomicRealDescent/3B projector owners are
literature/technique donors, NOT the same spinor operator.

**Spinor MODULE over SAME finite scalar VOA:**
`V=Fun(C3×A5,Q)` has 180 scalar sites;
`M=Fun(C3×A5,H_Q)` has 720 rational coordinates.
It admits a right-Q(i) spinor complex structure,
yielding 360 dimensions over Q(i), which is NOT
`Fun(C3×2I,Q)`, the distinct old 360-site spin
charge algebra. For `g=(a,k)`, spinor right pullback
is `r^k ψ(g.x)` with r=-q, and preserves scalar
pointwise vertex-module multiplication. The existing
finite semidirect actor is reused. The finite
`spin_voa_module_probe.py` checked 18 sampled
actors, 18x18 group pairs, 180 sites and sign
periodicity. No Monster-VOA module is identified.

**Full A5 global obstruction still non-split:**
`2I->A5` remains globally non-split even though
its restriction to any C3 subgroup splits. Hence
C3 alone is NOT a test of the global spin Schur
class. Continue using an actual 2I/A5 same-object
map for this, not an order-three phase analogy.

Independent local finite probes PASS, CI files updated,
but no successful exact-head Agda/Lean workflow
receipt returned. The geometric `R(B)=B` and
van Kampen identification remain open.


## 2026-10-24 decisive follow-on: SAME quaternion spin matrix and full F7 actor

**Stronger actual same-object representation owner**
`DASHI/Mathematics/Topology/AlexanderHornedC3SpinCyclotomicIntertwinerExact.agda`
reuses the LITERAL Cayley-Dickson rational Gaussian-complex
and rational quaternion carriers. Let q=(1+i+j+k)/2,
V=U(-q) in the standard Gaussian 2x2 quaternion realization,
and A=[[0,-1],[1,-1]]. The explicit invertible change-of-basis
matrix and its inverse are

    T    = [[1, -(1+i)/2], [0, (1-i)/2]],
    T^-1 = [[1, i],       [0, 1+i]].

The new owner proves V*T = T*A and both inverse laws
by componentwise rational polynomial identities.
An independent local exact Gaussian-rational probe
also passed modulo 3, 5 and 7 (over the corresponding
Gaussian quotient algebras). Since det(T)=(1-i)/2
and its norm is 1/2, T remains invertible modulo
every odd prime. This **pays** the former same-carrier
gap between the actual Horn coherent quaternion rotor
and the cyclotomic companion field-comparison matrix
at odd characteristic. p=2 is deliberately excluded.
Script:
`scripts/alexander_horned_c3_spin_cyclotomic_intertwiner_audit.py`.

**Full finite-group Maschke break** is stronger than
the C3-only character calculation:

    Gprojective=A5^3 rtimes C3, |Gprojective|=648000
    Gspin=2I^3 rtimes C3,      |Gspin|=5184000.

Both orders are 3 modulo 7. Therefore **Maschke applies
to every linear representation of BOTH full actors over F7**.
In characteristic 5, C3 alone is semisimple, but the
full A5 and 2I actors are modular. In characteristic
2 the central spin sign collapses. Characteristic 7
is thus the smallest prime simultaneously avoiding
2,3,5, preserving +/- spin, and allowing full finite
spin/projective-actor semisimplicity.

NEW exact arithmetic owner
`AlexanderHornedC3F7FullActorMaschkeExact.agda`
proves both group orders and their division-with-remainder
formulas, the 180/360 coordinate double-fibre identity
and its rational normalized mean coefficient.
Maschke's theorem itself is attributed to the pre-existing
pinned mathlib/classical source; not falsely reconstructed
as a new Agda theorem.

**Same finite module / projector diagram:**
with pi:OmegaS=C3x2I -> OmegaA=C3xA5 (2:1),
the uniform average on either function space over F7
is the projection to constant invariant functions.
Each finite group acts transitively on its coordinate set.
Since 180 mod7=5 and 360 mod7=3,

    180^-1 = 3 mod7, 360^-1 = 5 mod7,
    2 * 360^-1 = 180^-1 mod7.

Therefore for EVERY f on OmegaA,

    P_S(pi^* f) = pi^* (P_A f).

The full finite SL2(F5) quotient, five Q8 subgroups,
360->180 fibre counts, normalized averages and
group translations were checked independently with
exact finite arithmetic:
`scripts/alexander_horned_c3_f7_full_actor_reynolds.py`.
This is a genuine equivariant, mode-compatible finite
algebraic result, not a claim that the actual selected
Monster VOA or physical Dirac spectrum is realized.

Proof levels: these three new Agda modules are SOURCE
WRITTEN, not exact-head kernel checked. The scripts
were independently reproduced locally and committed.
Geometric horned R(B)=B, analytic Dirac domains,
and 3-copy exterior pi1 are still independent gates.


## 2026-10-24 actual Maschke-where-it-applies cut

Do NOT treat the split C3 cover as a 'negative result' we ever
sought. It is already paid by
`AlexanderHornedC3SpinLiftSplitExact.agda`.
The productive question is whether the SAME horn rotation
action admits Maschke projectors and nontrivial semisimple
spin/sign observations under a controlled change of field.

Actual previous donors reviewed:
`C3CyclotomicRealDescentExact`,
`C3FourierConjugationExact`,
`R3HodgeCrossExact`,
`SpinorRepresentationReceipt`,
`IbrahimMonster3BWholeCharacterIsotypicBypassExact`
and `BinaryPolyhedralMcKayDimensionExact`.

NEW source-written term-level rational owner:
`AlexanderHornedC3MaschkeR3Exact.agda` uses the existing
`Ambient.rotateXYZ` on the SAME triple coordinates,
constructs and proves the Reynolds idempotent
`P=(I+R+R²)/3`, proves vector = invariant diagonal +
sum-zero transverse residual and identifies the literal
transverse companion matrix `[[0,-1],[1,-1]]`.
It bridges the old symbolic 1+2 cyclotomic record without
assuming a nonexistent general ℚ-to-ℝ equivalence.

Finite exact modular comparison:
`scripts/alexander_horned_c3_maschke_field_comparison.py`.
Over F3 the transverse cyclotomic polynomial becomes
`(X-1)^2`; `(A-I)²=0`, invariant line is NOT a
direct summand, and the 3-site Reynolds sum is nonzero
nilpotent. Over F5 the module is irreducible semisimple;
over F7 it splits into 1D eigencharacters 2 and 4,
with **explicit orthogonal rank-one projectors**.
Over F2 it is also semisimple but spin -1=+1 disappears.
This is a representation-theoretic phenomenon, NOT a
physical Dirac zero mode.

**Stronger entire-actor answer:** char 7 divides neither
`|A5³⋊C3|=648000` nor `|2I³⋊C3|=5184000`,
so Maschke applies to EVERY finite module for BOTH complete
groups. `scripts/alexander_horned_c3_full_actor_maschke_f7.py`
reuses the 120->60 literal SL2(F5)->A5 map and tests the
180/360 coordinate pullback and 2-to-1 central-sign
averaging `(f(x)+f(-x))/2`, which yields an invariant
even/odd 180+180 splitting over F7. The older independent
full-actor local equivalent test PASSED. Exact new script
will run in the focused CI; no successful Agda receipt.

McKay nuance: binary 2T/2O/2I give affine E6/E7/E8
representation graphs, not a direct group map
`C3->E8`, not the separate `3^n` En-hyperfabric
and not a Monster VOA physical realization. Original
source: Kostant 1984 PNAS; classical McKay 1979/1980.
See full attribution and proof-gate roadmap at
`Docs/topology/AlexanderHornedC3MaschkeR3E8CrossCut20261024.md`.

Remaining high-value cut is an executable Agda kernel
receipt and genuine same-object geometric R(B)=B for
the exact embedded horned ball, NOT another abstract
C3 split-obstruction proof.
