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


## 2026-10-24 completion: MINIMAL F7 spin4, faithful wreath spin12, scope of C3 projectors

The constructive bottleneck beyond ordinary Maschke has now been
paid in the exact finite witness library:
`Docs/topology/AlexanderHornedMinimalSpinF7C3E8MaxCut20261024.md`.

- `scripts/alexander_horned_icosian_f49_minimal_spin.py`
  constructs F49=F7(sqrt5), 120 golden-ratio unit icosians
  (8+16+96), their 2x2 determinant-one matrix algebra,
  scalar-restricts to faithful GL4(F7), and builds the
  *ACTUAL SAME GROUP* bijective map to existing SL2(F5)
  using (2,3,5) generators and all 14400 products.
  Central -1 acts as -I4. No rank <=3 representation
  of 2I over F7 can be nontrivial, because order-5
  elements generate 2I and 5 divides none of
  |GL1(F7)|, |GL2(F7)|, |GL3(F7)|.
  Thus 4 is the MINIMAL nontrivial F7 degree.
- The 2D spin actor exists over F49 and its Frobenius
  conjugate has a genuinely different order-5 trace;
  restricting scalars gives the 4D F7 module.
  Do NOT claim a 2D full-2I spin representation over
  bare F7 from the earlier C3/2T rotor example.
- `scripts/alexander_horned_full_actor_f7_spin12.py`
  builds a faithful GL12(F7) block-monomial representation
  of (2I)^3 rtimes C3: the C3 block permutation reveals
  the phase, each faithful GL4 block reveals one factor.
  The diagonal central (-1,-1,-1) maps to -I12.
  Faithful 12D is proved; **minimal 12D is NOT asserted**.
- `scripts/alexander_horned_f7_spin12_horn_meridian_bidi.py`
  welds the PREVIOUS actual commutator root q of the
  binary Hatcher source to the new SAME 2I quotient:
  m^3 maps to diag(-I4,I4,I4) != I12, but to identity
  in its A5 projectivization. The group-quotient
  statement is finite/abstract, not a wild pi1 theorem.
- `scripts/alexander_horned_f7_spin_c3_projector_scope.py`
  corrects a crucial FULL-group invariant trap.
  The central sign ± splits 360 sites into full-actor
  invariant 180+180 even/odd spaces.
  The further six rank-60 C3×C2 joint Fourier spaces
  are subgroup eigensectors ONLY: the C3 Fourier
  projectors do NOT commute with arbitrary nonuniform
  2I^3 factors. A literal counterexample was locally
  computed. The 180± subspaces may further decompose;
  no irreducibility claim is made.

Independent LOCAL Python arithmetic passed: 120 finite
icosians, exact 120-element SL2F5 isomorphism, 14400
quaternion and matrix products, determinant-one, F49/F7
Galois trace descent, degree obstruction, 18x18 selected
full-actor 12x12 products, six projector idempotents
and explicit noncentral counterexample, same root cube
in spin12 vs A5. No typecheck/CI status promoted.

Attribution: unit icosians and binary group sources
precede DASHI; see Choi & Lee 2018, DOI
10.3390/sym10080326, and the classical McKay
correspondence. Our finite F49/F7 scalar restriction
and exact group-map calculation is a new computational
derivation on these prior mathematical roots.

PRIORITY now moves to the GEOMETRIC SAME-OBJECT task:
concrete C3-invariant three-copy wild-ball embedding
with attaching collars and van Kampen stage identification.
The earlier `C3OrbitSolidExact` already makes arbitrary
seed-orbit set invariance exact, but it does not construct
the actual Hatcher wild seed or its gluing. Do not spend
more cycles proving an abstract C3 extension splits.


## 2026-10-24 clopen-ball / real 3D gluing Pareto correction

We found significant prior art:
`Geometry/SSP369ClopenBallBridge`,
`Foundations/InverseLimitClopenRefinement`,
`Foundations/Base369PrefixUltrametricExact`,
`Foundations/CantorFiniteClopenPremeasureExact`,
`Foundations/CantorProjectiveCylinderMeasureExact`,
`Geometry/ProObjectSemantics`,
`Analysis/NonArchimedeanPadicCylinderBorelSourceExact`.

The real binary Cantor measure/finite clopen algebra owners
are more relevant than the ternary 3/6/9 authority tags.
In particular the old
`SSP369ClopenBallBridge.canonicalClopenAuthority`
uses label constructors, not a topological openness proof;
the old `InverseLimitClopenRefinement` stores
`intersectionSingleton : Set` and
`ultrametricComplete : Set` obligation fields, not
automatically inhabited certificates.

New `AlexanderHornedC3ClopenCylinderMassExact.agda`
welds the ACTUAL three-sector binary horn addresses with
the EXISTING Cantor cylinder mass, with exact
`1/(3*2^n)` normalization, child mass consistency,
rotation invariance, decidable finite prefix-cylinder
membership and complement, and cylinder nesting.
This is intrinsic wild-END topology, not an ambient
R3 ball or global decomposition of the CONNECTED exterior.
Indeed any continuous map from connected exterior
to totally disconnected K=C3×Z2 must be constant.

New local exact witness
`scripts/alexander_horned_clopen_linking_impasse_probe.py`
uses the same clopen address system for two different
3D link configurations with signed intersection-linking
numbers -1 and 0; the same oriented Hopf clasp can be
rotated into all 3 disjoint sectors with rational margin
proofs. The local linking witness is NOT Hatcher's
global perfect commutator tower/van Kampen receipt.

New local rational scaffold
`scripts/alexander_horned_clopen_tree_handle_scaffold.py`
uses the already source-defined 0 and 9e_i ball centres,
three axis-aligned radius-1/4 disjoint spoke cores and
a 4-vertex/3-edge C3-invariant TREE. Under genuine
collared topological B3 seed + tame attachments,
standard boundary connected sum yields a B3.
The wild satellite embeddings, attaching collars and
pi1 transition maps are still NOT constructed.

The old `AlexanderHornedC3OrbitSolidExact` ALREADY
makes any 3-phase seed orbit's set union R-invariant.
Hence the priority is no longer a standalone `R(B)=B`
conditional lemma, but constructing an actual embedded
wild topological 3-ball under that orbit and verifying
the complement Hatcher group via genuine geometric
van Kampen. Full audit/provenance/acceptance:
`Docs/topology/AlexanderHornedClopenBallGeometryMaxCut20261024.md`.

No Agda kernel/CI receipt claimed at user request.


## 2026-10-24 concrete geometry and OUTER-sector C3 improvement

Primary Hatcher Example 2B.2 pp171–172 inspected directly, with
the actual punctured-torus meridian commutator and injective
van Kampen stage maps. New source/technical roadmap:
`Docs/topology/AlexanderHornedThreeSectorGeometricVanKampenMaxCut20261024.md`.

**Source group identity now sharpened**:
`G_three = G_A * G_A * G_A` (free product), as an
independent three-copy filtered colimit of the Hatcher
free-stage commutator towers, NOT the direct product
`G_A^3`. `(2I)^3⋊C3` is its finite direct-product
QUOTIENT actor, consistent with the old 12D spin
representation. All-stage injectivity follows from
literal reduced-word fourfold expansion, as each
parent's two child letters occupy a disjoint alphabet.
Independent local audit checked 18,112 reduced words,
including exact sector-rotation commutation.

**ABSTRACT outer-action CLOSED**:
the C3 permuting the three free factors has exact
order 3 in `Out(G_three)`. Proof: retract onto
factor zero; rotated nontrivial factor-zero meridian
becomes identity, whereas the retraction of ANY inner
conjugate remains a nontrivial conjugate.
The SL2(F5) meridian witness and 120/120 conjugate
check are in
`scripts/alexander_horned_three_sector_outer_c3_witness.py`.
Only its geometric `Out(pi1(exterior))` incarnation
awaits an equivariant pi1 same-object isomorphism.
This is POSITIVE outer symmetry progress, not an
asserted nonsplit central spin cover of C3.

**Concrete geometric bug corrected**:
previous radial thin-spoke cores t∈[1,8] merely
TOUCHED the central and satellite unit spheres;
they did not define an attached 1-handle!
Patched original
`scripts/alexander_horned_clopen_tree_handle_scaffold.py`
to cores t∈[1/2,17/2], radius 1/4.
Each full endpoint disk is inside the relevant unit ball,
with radius² 5/16 <1; exposed tube components remain
disjoint. Scaled outward Hopf/unlinked loop pairs
fit INSIDE unit satellites without meeting spokes.

**Genuine Euclidean clopen control, not tags**:
`scripts/alexander_horned_tame_cantor_ball_cylinders.py`
constructs strictly nested actual 3D balls for every
binary cylinder with child containment margin >0 and
positive sibling separation at all depths, as a
TAME comparator. 511 finite cylinders checked. Its
identical symbolic `C3×Z2` ends do NOT force wildness
or exterior π1, a key topological discriminator.

NEXT P0: source-specific Hatcher wild satellite B3
with its actual tame attachment disk/collar. Distinct
from the standard unit satellite BALL geometric overlap
now checked. Then splitting spheres and an actual
simply-connected-overlap van Kampen for the full
threefold exterior. User requested local Python rather
than Agda/CI, so no new kernel claim.


## 2026-10-25 source-supported inward cap + literal separator sphere breakthrough

**Primary-source progress:** Franca Lippert, *The Alexander Horned
Sphere and Bing's Hooked Rug*, §2.1–§2.2 (Figure 2, pp. 2–4),
https://www.maths.gla.ac.uk/~mpowell/WriteUp_Franca.pdf,
describes horn-stage homeomorphisms becoming the identity
away from shrinking attachment support; the wild sphere is
locally flat off its Cantor ends. Hatcher, *Algebraic Topology*,
Example 2B.2, pp. 170–172 gives the genuine individual
exterior meridian/commutator van Kampen group.

Consequently we can choose a classical supported Alexander
construction that leaves an initial round B0 inward cap
unchanged. New
`scripts/alexander_horned_supported_stable_cap_certificate.py`
checks explicit coordinates for B0 radius 3/4 in a unit
reference satellite:
  Phi(u,v,s)=(-sqrt((3/4)^2-u²-v²)+s,u,v),
  u²+v²<=1/16, |s|<=1/8.
It is a genuine local TWO-SIDED collar with an inverse
chart, not a symbolic `ClopenWitness` label.
The corrected spoke endpoint t=8.5 with disk radius
1/4 has squared satellite-centred norm 5/16<9/16,
so overlaps the ACTUAL cap-preserved wild B0, not
merely the outer reference unit container.
The local exact script passed 797 rational chart tests.
The source-supported infinite horn attachments still
have to be instantiated to declare an executable
infinite-coordinate embedding.

A much sharper geometric van Kampen separator is now
available: three literal disjoint spheres
  S_i={|x-9e_i|=4}.
Their *only* contact with the constructed solid is the
respective straight spoke, and on each sphere the
intersection is the single transverse disk GRAPH
  t=9-sqrt(16-u²-v²),   u²+v²<=1/16.
Its near axial range is 5<=t<8.5. The far root
is outside the tube; all other reference balls/tubes
lie beyond the sphere. Radius-1/4 collars around the
three S_i are disjoint. New
`scripts/alexander_horned_three_sector_separator_spheres.py`
and an independent exact-Fraction local equivalent
passed 197 rational cross-sectional checks; all-radius
claims follow from exact monotone square-root bounds.

Thus `S_i∩E=S²\closed(D²)`, an OPEN DISK, so the
exterior open-cover overlap is simply connected.
This is the proper geometric van Kampen cut; a PLANE
minus disk would instead have pi1=Z and must not
be used as though it were simply connected.

New comprehensive source-attributed proof note:
`Docs/topology/AlexanderHornedSupportedCapSeparatorVanKampen20261025.md`.
It spells out how a threefold collared boundary
connected sum can yield B3 and, using the standard
unknotted-tree-neighbourhood/side-cap equivalences,
`pi1(E)=G_A*G_A*G_A` with outer C3.
This is a **paper-level source-supported geometric
proof scheme** with exact local geometry; the native
infinite horn support map and all ambient deformation
retractions are NOT machine-proved or explicitly
coordinate-constructed in the repo.

This discharges the earlier vague *existence of a tame
cap as an unexplained input* by pointing to and using the
actual supported original horn construction. The
remaining max-cut is no longer 'find separating spheres',
but instantiate its *supported infinite attachment*
and the complement-piece homeomorphisms as concrete
same-object maps. No Agda/CI work per user request.


## 2026-10-25 completed orbifold C3 semantic bridge

The genuinely EXTERNAL order-three subgroup has an
actual topological interpretation once the wild
exterior E is realized as R-invariant. The point
x0=(20,20,20) is fixed by the ambient R and lies
outside the compact C3-symmetric scaffold.
For the global quotient orbifold `[E/C3]`,
the Borel fibre sequence `E->E_hC3->BC3`
has a section induced by x0. Hence
  pi1^orb([E/C3]) ~= pi1(E) rtimes C3.
Under the supported Hatcher triple-gluing
identification this becomes
  (G_A*G_A*G_A) rtimes C3.
The source `pi1(E)` remains torsion-free;
external finite C3 is ORBIFOLD STABILIZER data.
This is NOT generally the ordinary fundamental
group of the coarse quotient space `E/C3`.
This also clarifies the discrete spin3 lift versus
continuous 360°/720° rotation-path distinction.
Primary expository root: Caramello,
*Introduction to Orbifolds*, arXiv:1909.08699.
`scripts/alexander_horned_orbifold_split_c3.py`
locally checks the fixed-point and semidirect group
law in the exact 2I finite quotient.

Other NEW source-grounded geometric commitments:
Lippert §2.2 supplies supported horn homeomorphisms,
preserving an inward tame cap of B0; a real radius-3/4
cap chart and positive-volume collar overlap were
locally certified, as were three radius-4 separating
spheres with ONE transverse disk each. They yield
simply connected van Kampen overlaps
`(S²\\closed D²)×I`, rather than the non-simply
connected PLANE-minus-disk overlaps.
Complete report:
`Docs/topology/AlexanderHornedSupportedCapSeparatorVanKampen20261025.md`.

The paper-level wild topology still depends on the
classical supported Hatcher construction and standard
tree/collar neighbourhood equivalences; local Python
does not turn these into Agda kernel proofs. No CI
or Agda typecheck was performed per user request.


## 2026-10-25 roadmap reset: FINITE vs INFINITE physical observables

New source-audited decision report:
`Docs/topology/AlexanderHornedRoadmapRealWorldImplications20261025.md`.

**Critical Hatcher object discriminator:** `B_n` is a
locally-flat/tame finite horned BALL with simply connected
exterior (Schoenflies), whereas Hatcher's stage enclosure
`X_n` is a genus-`2^n` handlebody with nontrivial
exterior `Y_n` and `pi1(Y_n)=F_(2^n)`.
For three independent sectors, stage group rank is
`3*2^n`. The ideal limit `B=intersection X_n` is
the source of the perfect but nontrivial exterior group.
Do NOT use a finite printed B_n and falsely advertise
the complement group of X_n or the ideal limit.
Original: Hatcher Example 2B.2 (printed pp171-172)
and locally-flat Schoenflies.

**Essential noncommutation of limit/abelianization:**
Each source meridian becomes a child commutator, so
H1(Y_n)->H1(Y_(n+1)) is the ZERO map despite each
H1(Y_n)=Z^(3*2^n). Thus H1(E)=0 while
pi1(E) is nontrivial. In R3 the exterior also has
H2(E)=Z from the sphere at infinity; in S3 the
complement of the compact contractible ball is
reduced-acyclic. Do not call R3 exterior fully acyclic.

**Flat U1 vs nonabelian holonomy**:
Hom(perfect G,U1)=1; each isolated finite free stage
has nontrivial U1 characters that cannot be carried
compatibly through all commutator refinements.
In contrast existing 2I=SL2(F5) perfect quotient
has an order-six root q with q^3=-I, recursively
compatible child commutators and spin-character
Wilson trace -2. Nonflat Maxwell connections can
still have Wilson loops on contractible paths.
A one-level Q8 commutator [i,j]=-I works, but
Q8 cannot extend recursively: [Q8,Q8]=C2.
The perfect 2I target is essential for ALL scales.
Executable finite audit:
`scripts/alexander_horned_scale_holonomy_maxcut.py`.

**Actual experiment/control roadmap:** finite sculpture,
finite X_n handlebody, and unlinked/tame controls must be
labelled DIFFERENT specimens. A synthetic SU2/optical
control circuit may implement recursive commutator
identities and observe relative Wilson phases; this is
not direct observation of the infinite wild pi1.
Prior published physical feasibility roots: Lucien
Grillet's FOUR-level 20cm PLA/PVA horned sculpture,
Bridges 2022; Q. Liang et al. Nature Physics
(2024), DOI 10.1038/s41567-024-02644-4
synthetic SU2 nonabelian AB in a 1D ladder, and
Sugawa et al. npj Quantum Information (2021)
nonabelian Wilson-loop measurements.
No original DASHI experiment currently exists.

**Quantitative synthetic signature:**
`scripts/alexander_horned_su2_controls_noise_probe.py`
verifies exact quaternion algebra
`tr([A,B]) = 2-4 sin²(alpha) sin²(beta)` for
orthogonal-axis SU2 controls; at alpha=beta=pi/2
this is -2 versus commuting U1 +2. Angular control
errors change the trace; a lone global -1 spinor sign
must be measured against a reference. One SU2
commutator does not prove the whole tower's perfectness.

**Hard acceptance gates:** actual supported Hatcher
infinite horn coordinates and cap, the three piecewise
open-cover/van Kampen homotopy maps, CAD models with
known finite stage group, calibration/flatness controls,
specified Maxwell/Dirac operator and boundary data.
No implication of gravity anomalies, free energy,
superluminal communication, quantum consciousness or
new physical zero modes.

The work priority is a dual track: geometry source
same-object closure plus practical finite nonabelian
control experiment; defer Agda typecheck/CI by request.


## 2026-10-25 dual-track implementation max-cut — GEOMETRIC PAPER THEOREM + EXECUTED GAUGE SIMULATOR

**GEOMETRY:** New `Docs/topology/AlexanderHornedC3SameObjectGluingTheorem20261025.md` supplies the full source-attributed paper-level existence argument for a 3-sector equivariant wild B3: choose the Hatcher/Lippert horn seed with an unchanged inward tame disk, attach three rotated supported copies to the central unit ball with actual tame radius-1/4 collars, cut by three radius-4 spheres and use classical boundary-connected sum and van Kampen. The NEW explicit stereographic coordinates
  sigma(t,u,v)=(u/(t-5),v/(t-5))
map each geometric cut-sphere exterior overlap homeomorphically to the OPEN disk `|y|<16+sqrt(255)`; inverse
  t=(13+5|y|²)/(1+|y|²), u=8y1/(1+|y|²), v=8y2/(1+|y|²).
It contracts by `H_s(y)=(1-s)y`, so a collar overlap is simply connected. That removes a vague topological-overlap assumption and uses actual source-defined tubes/caps. The usual tame-collar replacement argument identifies satellite-side pi1 with original Hatcher `G_A`; the round-star control establishes central-side pi1 trivial. The cut-and-paste theorem then yields `pi1(E)=G_A*G_A*G_A` and outer C3 at a fixed basepoint. Original wild embedding / its stage theorem and standard 3-manifold lemmas remain EXTERNAL CLASSICAL theorem inputs, and an indexed infinite coordinate map / kernel proof is STILL NOT coded. Code: `scripts/alexander_horned_C3_same_object_separator_atlas.py`. Locally validated 2601 stereographic and 797 cap-chart samples, with exact rational identities and explicit inverse.

**EXECUTED SYNTHETIC SU2 GAUGE MODEL:** New `scripts/alexander_horned_c3_finite_SU2_gauge_simulator.py` constructs all 120 binary-icosahedral unit quaternions over Q(phi), checks all group products, finds exact commutator witnesses for ALL 120, selects `q=(1+i+j+k)/2` whose cube is `-1`, and assigns Hatcher child meridians compatibly through selectable finite depth. Ideal selected root-cube Wilson halftrace is `-1` for all depths; matched commuting U1 halftrace `+1`; Q8 yields central `-1` at ONE level but cannot maintain full recursion. Model applies independent gate-axis-angle noise and Bernoulli controlled-U readout shots. A locally executed source-equivalent 50-trial/300-shot/1.5deg simulation returned depth-0..5 observed halftraces `[-0.9999,-0.9995,-0.9955,-0.9828,-0.9437,-0.8032]` with gate costs `3*4^n`. They are **synthetic** predicted readouts, not laboratory measurements. Added six `test_alexander_horned_C3_gauge_simulator.py` tests for C3 factors, commutator compatibility, gauge conjugacy invariance, Wilson orientation limitation and reproducibility; equivalent local test suite PASS 6/6.

**TRUE C3-UNITARY LAB ACTOR:** New `scripts/alexander_horned_C3_three_channel_SU2_actor.py` realizes `(2I)^3 rtimes C3` faithfully on THREE complex SU2 spin doublets, so `(2I)^3 rtimes C3 -> U(6)` by 2x2 quaternion matrices and C3 block permutation. It carries the selected cube as `diag(-I2,I2,I2)`, which disappears in A5 quotient. Independent equivalent local test PASS all 120 SU2 matrices, 300 products and sampled actor associativity. This complements the earlier minimal GL4(F7)/full GL12(F7) arithmetic actors but is more experimentally actionable.

**TRUE PHYSICAL BRIDGE, NOT AUTOMATIC SPIN CURVATURE:** a homomorphism `rho:pi1(E)->2I->SU2` supplies an AUXILIARY flat SU2 local system `(E_tilde x SU2)/pi1(E)`, by standard flat-bundle/holonomy reconstruction (Goldman-Millson 1988; standard Riemann–Hilbert). This proves mathematical existence of a specified flat nonabelian connection on the ideal wild exterior, but NOT a physically realized connection or an effect of the Euclidean Levi-Civita spin connection. Wilson trace alone is invariant under conjugation and cannot distinguish q from q^-1; additional matrix tomography is gauge-frame-dependent. A graph circuit has its OWN finite free-group topology and must not be advertised as a measurement of the infinite horned complement.

**PHASE GATES NOW:** (0) source/provenance — done; (1) abstract free group/C3/2I/spin — mathematical and finite done; (2) geometric existence — classical paper-level gluing proof supplied, entire infinite ambient map code still open; (3) geometric van Kampen — explicit cut atlas complete, standard source collar/round-star homeomorphism invoked rather than kernel-certified; (4) runnable finite synthetic gauge emulator — DONE / locally executed; (5) full three-channel C3 complex actor — DONE / finite locally verified; (6) physical apparatus/actual gauge measurement — NOT DONE; (7) specified PDE spectral experiment — NOT DONE. No Agda or CI work by user request. Full technical protocol `Docs/topology/AlexanderHornedC3GaugeSimulatorExperimentProtocol20261025.md`.
