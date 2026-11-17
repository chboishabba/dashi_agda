# Horned C3 exterior group -> finite nonabelian quotient -> an actual VOA

**Date:** 2026-10-24. **Status:** mathematically explicit finite quotient/VOA
construction and exact Agda source-level coordinate action; an Agda kernel
receipt and the physical/geometric complement identification remain open.

## Source/attribution ledger

* Alexander (1924), classical horned sphere; Hatcher, *Algebraic Topology*,
  Example 2B.2, <https://pi.math.cornell.edu/~hatcher/AT/AT.pdf>.
  Owns the classical commutator tower and injectivity reasoning.
* Standard commutative vertex-algebra construction: Kac,
  *Vertex Algebras for Beginners* (2nd ed, 1998), and
  Reimundo Heluani, *Vertex Algebras*, Example 10.4,
  <https://w3.impa.br/~heluani/files/lect.pdf>.
  A finite-dimensional unital commutative associative C-algebra
  with zero derivation yields a conformal VOA of central charge zero,
  with all weight concentrated in zero. See also George Andrews,
  *Vertex Operator Algebras* (2021),
  <https://megl.science.gmu.edu/wp-content/uploads/2022/01/George_Vertex_Operator_Algebras_12_03_2021.pdf>.
* DASHI inherited sources:
  `DASHI/Moonshine/VertexOperatorAlgebraCore.agda`,
  `DASHI/Moonshine/VertexOperatorAlgebraLinearActionReceiptExact.agda`,
  `DASHI/Moonshine/Base369Monster3BVOAActionPhaseAdapterBidiExact.agda`,
  `DASHI/Moonshine/Monster3BLiteralThreePhaseRegularResidualBidiExact.agda`,
  `DASHI/Moonshine/RankOneHeisenbergFockWindowExact.agda`,
  `DASHI/Moonshine/TrivialRationalGradedVertexAlgebraExact.agda`,
  `DASHI/Moonshine/FiniteDifferentialVertexAlgebraExact.agda`,
  `DASHI/Moonshine/SquareZeroDifferentialVertexAlgebraExact.agda`,
  `DASHI/Mathematics/Topology/AlexanderHornedC3FiniteStageExact.agda`,
  `AlexanderHornedC3FreeFactorDetectorExact.agda`,
  `scripts/alexander_horned_c3_a5_probe.py`.
* New contribution in this cut: a concrete non-CFT-type finite VOA,
  an explicit semidirect product representation with precise kernel,
  an exact pointwise coordinate-algebra group-action proof skeleton
  using the existing C3 carrier, and a finite executable audit.

**This is NOT a Monster/3B or V-natural action, nor a physical
identification of the complement.** VOA group action, VOA algebra and
exterior fundamental group are three different objects until mapped.

## Same mathematical object: source group and its C3 action

The three-root Hatcher-type algebraic direct-limit group:

    F_n = free group on (i,w), i in C3, |w|=n,
    phi_n: x_(i,w) |-> [x_(i,w0), x_(i,w1)],
    G = colim_n F_n.

Hatcher's injection argument gives G_A = colim F_(2^n) nontrivial and
locally free, hence G = G_A * G_A * G_A. The automorphism r permutes
factors, r(x_(i,w))=x_(i+1,w), and r^3=1.
Therefore define K=G ⋊_r C3, with

    (g,k)(h,l)=(g r^k(h),k+l).

The previous work proves algebraic noninnerness of r using a
free-factor retraction, and it separately describes the geometric
boundary-connected-sum model needed to recognize
K as pi1(S3\H) ⋊ C3.

## Full compatible A5 quotient, not only a bounded calculation

Let A5 be the alternating group on five letters (order 60).
The previous finite exact audit enumerates every A5 element as a
commutator: choose, once and for all, explicit `a_t,b_t` with
`[a_t,b_t]=t` for each t in A5. It also exhibits a chosen
nontrivial root t=[a,b] with <a,b>=A5, order(t)=5.

Define compatible homomorphisms on Hatcher's binary stages by
q_0(x_empty)=t; at stage 1 let
q_1(x_0)=a, q_1(x_1)=b; at later stages choose
q_(n+1)(x_(w0))=a_(q_n(x_w)) and
q_(n+1)(x_(w1))=b_(q_n(x_w)).
Then

    q_(n+1)(phi_n(x_w))
       = [a_(q_n(x_w)), b_(q_n(x_w))] = q_n(x_w).

The maps therefore induce q_A:G_A->A5. Because a,b already generate A5
at stage 1, q_A is surjective. Repeat independently for all three
free factors:

    q:G -> A5^3.

This map is surjective and C3-equivariant:
q(r g) = beta(q(g)), beta(u)_i=u_(i-1).

Consequently the genuine group homomorphism

    Q : K=G⋊C3 -> B=A5^3⋊C3
    Q(g,k)=(q(g),k)

is surjective. The definition of Q is mathematical; the exact
group-colimit and q as an Agda object are not kernel-certified.

## SPECIFIED genuine VOA: 180-dimensional commutative c=0 example

Let the coordinate set be

    Omega = C3 x A5, size 3 * 60 = 180.

Let V=Fun(Omega,C) with pointwise + and product, unit 1=(constant 1).
This is an explicitly specified finite-dimensional commutative
associative unital C-algebra; all structures are coordinatewise.

Give it the standard zero-derivation commutative vertex operator
algebra:

    Y(f,z)h = f*h (constant in z);
    f_(-1)h=f*h; f_n h=0 for n != -1;
    vacuum=1, translation T=0;
    conformal vector omega=0, Virasoro L_n=0, central charge c=0;
    V_0=V, V_n=0 for n != 0.

The vertex Jacobi identity reduces to associativity and
commutativity; vacuum, translation, locality and conformal grading
follow immediately. The VOA is NOT simple, NOT of CFT type
(V_0 is 180-dimensional, not C), and has no Monster interpretation.
It is nevertheless a genuine finite-dimensional VOA under the
standard unrestricted VOA definition, as in the cited sources.

## Explicit group action and strong retention result

For B=A5^3⋊C3, write (u,k) with u=(u0,u1,u2).
The **left** coordinate permutation on Omega is

    (u,k)·(i,a)=(i+k, u_(i+k) a).

The semidirect multiplication is

    (u,k)(v,l)=(u*beta^k(v),k+l),
    (beta^k(v))_i=v_(i-k).

Direct substitution shows
(g h)·x = g·(h·x) for all g,h in B and x in Omega.

To get a left action on V, use pullback by INVERSE permutations:

    (rho(g)f)(x)=f(g^(-1)·x).

It preserves the pointwise product, vacuum and conformal vector,
and hence every Y-mode (only mode -1 is nonzero); rho is a
group homomorphism B -> Aut_VOA(V).

It is FAITHFUL. If g=(u,k) acts trivially on all of V, then
in particular every coordinate delta function is invariant,
so g fixes all x in Omega. Apply this to the three x=(i,e).
Their first coordinates force k=0. Their second coordinates
then force u_i=e for each i. Thus g=1.

Compose with Q to obtain a **genuine nontrivial** action

    R : G⋊C3 -> Aut_VOA(V),
    R = rho ∘ Q.

The exact information retained is

    ker(R) = ker(q) × {0}.

Thus R separately detects the cyclic sector and the whole A5^3
quotient of G; it detects noncommutativity within each A5 factor.
It is **NOT faithful on the infinite G**: the root meridian
m=x_(0,empty) maps to t of order five, so
R(m^5)=identity while m^5≠1 by Hatcher's free-group injection.
This is an explicit BIDI/no-descent witness: the selected VOA
does not recover the entire horned exterior fundamental group.

The C3 generator acts by genuine permutation of THREE sectors;
it does NOT identify spatial C3 with a Monster 3B eigenspace or
change abelian character no-go results. Because G is perfect,
every homomorphism G->abelian target is trivial, while R
detects nonabelian quotient information.

## Why not directly V-natural?

The repo's `VertexOperatorAlgebraCore` group-action record has
`preservesModes : Set`, `actionIdentity : Set`, and
`actionComposition : Set`: these are opaque proof *slots*, not
full VOA axioms automatically verified for a concrete group.
The selected-3B/Monster adapters are strong source-labelled
normalizer, phase and linearity donors, but no map
G->Aut(V-natural) or same-state intertwiner for a chosen horn
meridian was found in this audit. Substituting the 3B central
element for our geometric rotation would be a **new scientific
recognition assumption**, not a theorem.

A nontrivial action on V-natural would require a concrete
quotient q_M:G->Monster, an explicit selected element and its
normalizer under the C3 automorphism, and proof that their action
on the SAME literal VOA carrier respects q_M and all VOA modes.
Neither coincidence of dimensions nor existence of a cyclic
character establishes these obligations.

## Validation and verification scope

* Executable:
  `python3 scripts/alexander_horned_c3_voa_a5_action_probe.py`
  checks all 60 commutator images, five binary stages, 4000
  deterministic exact semidirect/action/algebra samples, the
  180-address carrier, root order five and kernel witness.
* Agda source:
  `AlexanderHornedC3FiniteVOAActorExact.agda` proves for an
  arbitrary actor-factor group the 27 exact C3 coordinate cases,
  group composition on coordinates, right pullback algebra
  preservation and the nontrivial phase movement.
  A right action is converted to a left VOA action by inversion,
  as shown algebraically above; the finite A5 instantiation and
  VOA axioms are established mathematically, not as a certified
  Agda `VertexOperatorAlgebra` value.
* Exact-head kernel checking:
  `bash scripts/check_alexander_horned_c3_exact_head.sh`
  and focused Hatcher Lean build. NO successful kernel receipt
  has been returned. The existing geometric collar/van Kampen
  and direct-limit identification with an actual 3-manifold are
  independently open.

Highest alpha next: obtain exact-head Agda compile diagnostics,
finish the geometric C3 horned-ball realization in Lean,
and if a Monster-specific consumer is demanded, identify an
actual source-to-VOA action map rather than creating another
phase-label interface.


## Repo-native vertex mode proof reuse (additional exact cut)

The first repo search surfaced the Moonshine/3B interfaces, but a
second search found stronger *already implemented* local algebra:

* `DASHI/Moonshine/TrivialRationalGradedVertexAlgebraExact.agda`
  owns proof-bearing `vacuumMinusOneIdentity`, `creationMinusOne`,
  `minusOneProductCommutative`, `minusOneProductAssociative`,
  `translationActsAsDerivationOnMinusOneProduct`, and
  `conformalModesVanish`. We do not re-prove these scalar identities.
* `DASHI/Moonshine/FiniteDifferentialVertexAlgebraExact.agda`
  and `SquareZeroDifferentialVertexAlgebraExact.agda` are
  the genuine nonzero-derivation generalisations, but are not
  needed for this zero-derivation finite-dimensional VOA.
* NEW `DASHI/Mathematics/Topology/AlexanderHornedC3VOAModeLiftExact.agda`
  literally imports the trivial rational seed, defines every
  integer mode at each coordinate using `Seed.trivialMode`,
  inherits the seed's vacuum/creation/product/translation/
  conformal proofs coordinatewise, and proves that the *same*
  finite semidirect action commutes with every integer mode
  and preserves vacuum, conformal vector and translation.
  This is not an opaque `preservesModes : Set` label:
  `allVertexModesIntertwineRightAction` has an equality
  conclusion quantified over actor, states, integer mode and coordinate.
  The target is rational; standard extension of scalars to C
  constructs the complex finite-dimensional VOA discussed above.
* NEW `AlexanderHornedC3VOAKernelBidiExact.agda` reuses
  `FormalClaimTransportGeometryExact` and
  `ConsumerDescentMinimalObserverExact`: given the source
  nonidentity meridian power in the actor kernel, the finite
  actor cannot be inverted to recover all source group elements,
  and every observation factoring through that actor also
  identifies the kernel pair. The exact `m^5` certificate
  is supplied by the classical free group injectivity plus
  the explicit finite A5 quotient, not by the generic record.

The pointwise proofs do not implicitly use function extensionality:
they establish equality on all coordinates. Conversion to an
equality of entire functions would need suitable extensionality
or the appropriate observational equivalence.

### Exact-head commands

    python3 scripts/alexander_horned_c3_voa_a5_action_probe.py
    bash scripts/check_alexander_horned_c3_exact_head.sh

Status must remain source-written until successful exact-head
kernel receipts; the finite independent Python check in this chat
ran 2,000 deterministic action/product tests and the complete 60
A5-element commutator coverage, with root image order five.
The committed standalone script's 4,000-case regression and
five-stage recursion were added but have not been separately
executed in the remote CI environment.


## Jordan on exactly the same VOA states

There is a small but genuine positive cross-pollination, with
no exceptional-algebra inference: the coordinate product on
`Fun(C3×A5,C)` is associative and commutative, so it
automatically satisfies the Jordan identity

    (f*f) * (g*f) = ((f*f)*g)*f.

In `AlexanderHornedC3VOAModeLiftExact.agda`,
`sameStateJordanIdentity` is an exact rational polynomial
identity on the **same state carrier and same (-1) mode**
as the C3-equivariant VOA action. The earlier
`AlexanderHornedC3JordanActionExact.agda` is a more
abstract triple-of-Jordan-identities donor.

This uses the elementary *special Jordan* algebra coming
from an associative commutative algebra. It does NOT
identify that algebra with the exceptional 27-dimensional
Albert algebra, the full weight-two Griess algebra, a
Monster 3B eigenspace or the physical horned exterior.


## General finite-automorphism no-go: why V-natural cannot be faithful

Frenkel–Lepowsky–Meurman establish
`Aut_VOA(V-natural) = Monster`, a finite simple group.
See *Vertex Operator Algebras and the Monster* (1988),
and Scott Carnahan, *Why do the symmetries of the monster vertex
algebra form a finite simple group?*, arXiv:2206.15391.

The group `G` above contains an infinite cyclic subgroup generated
by a Hatcher meridian `m`, since `m` lies in a free group at
finite stage and the connecting maps are injective. Therefore
for **every** homomorphism `rho:G -> Aut(V-natural)`, its finite
image contains `rho(m)` of some finite order `d>=1`. Hence

    rho(m^d) = 1,      m^d != 1 in G.

So **NO faithful full-horned-group action exists on V-natural**,
irrespective of how clever the selected 3B/normalizer mapping is.
A nontrivial and structurally meaningful quotient action is still
possible in principle, but requires an actual Monster-targeted
homomorphism and VOA state-action intertwiner. The finite-c=0
construction above intentionally provides such a quotient
representation on a DIFFERENT, explicit VOA.

This no-go is a classical group-cardinality inference, not a
Monster embedding obstruction for a particular finite quotient:
we have NOT checked whether the proposed A5³ ⋊ C3 embeds in Monster
or realizes a selected 3B normalizer. It also does not rule out
faithful actions on a VOA with an infinite automorphism group,
where separate structural conditions apply.


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


## Torsion and non-lift boundary

The finite group `A5^3 ⋊ C3_ext` contains an internal *actual*
`C3_int` generated by the diagonal 3-cycle. **This subgroup generally
does NOT lift as a subgroup of the original horned exterior group G.**

Proof: G is the directed union of free groups with injective
commutator-substitution connecting maps. Every element of finite
order in the union has a representative in some finite-stage free
group, and injectivity would give finite order at that stage.
Free groups are torsion-free; hence G has no nontrivial element
of order three. Thus all elements of G mapping to a nontrivial
3-cycle under `q:G->A5^3` necessarily have infinite order.

In `G ⋊ C3_ext` the external order-three cyclic subgroup exists
genuinely as `(1, C3_ext)`, and is independent of the finite
quotient's diagonal C3_int. Do not claim `C3_int×C3_ext`
embeds into the source `G⋊C3_ext`: it is **a subgroup of the
finite quotient actor only**.

This makes the representation's information loss explicit:
the diagonal order-three VOA operator is the finite image
of an infinite-order exterior-group operator. The action is
genuine on the *specified finite quotient VOA*, but not faithful
on G. None of this gives a geometric Monster 3B embedding.


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

## 2026-10-24 cross-PR infinite-order and selected A5 witness correction

**Triggered by neutrino CP/PMNS PR #1247:**
https://github.com/chboishabba/dashi_agda/pull/1247

### Source audit: selected quotient meridian initially had the wrong order

The original `scripts/alexander_horned_c3_a5_probe.py`
and `scripts/alexander_horned_c3_voa_a5_action_probe.py`
selected their root as the **first** nonidentity commutator of a
pair generating A5.  Independent exact permutation enumeration
established that this initial root is

```
(2,1,3,0,4)    # order THREE, not five.
```

This contradicted the VOA script's subsequent `assert root_order==5`
and the prior illustrative kernel witness `m^5`.

**Owner-side correction:** Both scripts now select the FIRST
order-**five** commutator for which the selected pair generates A5.
Independent exhaustive lexicographic search found

```
root g = (2,0,3,4,1), order(g)=5
a      = (0,1,3,4,2)
b      = (2,3,0,1,4)
[a,b]  = g
<a,b>  = A5 (all 60 elements)
```

The 60/60 commutator section is unchanged in principle.  Selecting
the required root *before* constructing the compatible descendant
commutator section repairs the finite quotient data, not the
Hatcher free-group/directed-colimit mathematics.

Added `tests/test_alexander_horned_c3_a5_order_selection.py`
to prevent treating a generic generating-pair commutator as an
order-five witness, and to assert both probe selection rules agree.

**Execution grade:** Independent locally executed permutation
enumeration confirms the corrected root and the order-three
failure of the previous choice.  Both updated GitHub Python scripts
were source-read-back, but their full exact-head test commands
and the Agda/Lean kernel jobs have not been rerun following
the correction.  Superseded `order-five root PASS` claims made
without the selector condition should be regarded as **invalid
for the original code**, not inherited as fresh receipts.

### Relation to neutrino CP residual product

- The Hatcher source meridian `m` has **infinite order** in
  the abstract injective free-group colimit `G`; `m^5 !=1`.
- Its new selected **finite quotient** `q(m)=g` has
  `g^5=1`, hence the concrete c=0 VOA actor loses `m^5`.
- The geometric C3 rotation `r` has order three in
  `Aut(G)` and nontrivial class in `Out(G)` in the
  **three-copy** horned model.  It is NOT an order-three
  element of the torsion-free source group `G`.
  The semidirect extension `G ⋊ C3` DOES have an
  actual order-three rotation element.
- The neutrino toy uses complex 3×3 matrices:
  `T=diag(1,ζ,ζ²)` (order three),
  `S1=U diag(1,-1,-1) U†` (order two), and
  `TS1` is infinite-order by its computed nonintegral
  Galois trace.
- In an additional direct exact rational cyclotomic
  calculation, `(TS1)^5 != I`; specifically its
  `(0,0)` entry is approximately
  `0.3402566114 - 0.1159850079i`, not 1.
- Therefore any `A5^3`-quotient representation that tries
  to send **this selected** `q(m)` to `TS1` is
  impossible: fifth powers would have to agree.
  PR #1247 now encodes this as an abstract Agda
  homomorphism-transport no-go and a committed
  exact-`Fraction` Python regression.

This **does not prohibit** every representation of the infinite
horn group into a matrix group.  Nor does it prove that
`TS1` is itself a horned-complement loop or that the
VOA acts on physical lepton states.  A different infinite-image
representation requires the full compatible commutator tower,
same-space C3 equivariance and a source-specified physical
operator identification.  The horn group is perfect, so it
cannot support a nontrivial *abelian* character
`G → U(1)` or `G → C3`, even though nonabelian
A5 quotients and the outer C3 action exist.

### Attribution correction

The original classical horned sphere belongs to
**J. W. Alexander (1924)**; its commutator-tower
proof is in **A. Hatcher, Algebraic Topology**
Example 2B.2, pp. 170–172.  Norman W. Riebe's
1968 higher-order horn groups and finite
A5 representations are **related prior art, not the
same source group**; do not identify Riebe's
groups with Hatcher's group just because both
contain the word "horned."

Acceptance (postfix):

```sh
python3 scripts/alexander_horned_c3_a5_probe.py
python3 scripts/alexander_horned_c3_voa_a5_action_probe.py
python3 -m unittest discover -s tests -p 'test_alexander_horned_c3_a5_order_selection.py' -v
```

No merge, CI, Agda, Lean, actual geometric collar proof, or
physical neutrino/VOA equivalence is asserted from this update.

## 2026-10-24 max-cut: POSITIVE infinite-image SU(3) action on the abstract horned group

### Why the earlier finite A5 no-go does not block SU(3)

This is a materially stronger step than another analogy.
Sibling neutrino/CP PR **#1247** had the exact
**A5^3 finite quotient** fifth-power no-go: the selected
horn image `q(m)` has order 5, whereas selected CP
`A=T S1` has `A^5≠I`. This is a **factorization**
obstruction through that PARTICULAR finite actor—not an
obstruction to representations of the original infinite
horned direct-limit group.

Original first-hand Lie theorem:
**Morikuni Gotô**, "*A Theorem on compact semi-simple groups*,"
*Journal of the Mathematical Society of Japan*
**1**(3) 270–272 (1949),
https://doi.org/10.2969/jmsj/00130270 .
His original theorem says that **each element of a
connected compact semisimple group** is a commutator.
`SU(3)` is such a group.

Original topological algebra:
**Allen Hatcher**, *Algebraic Topology*,
Example 2B.2 pp.170–172,
https://pi.math.cornell.edu/~hatcher/AT/AT.pdf .
The Hatcher binary free-group tower has
`F_n=Free({0,1}^n)` and injective substitutions

```
phi_n(x_w) = [x_w0, x_w1],
G_A = colim_n(F_n,phi_n).
```

### An explicit finite-dimensional Gotô factorization

For ANY `A∈SU(3)`, take a unitary spectral
diagonalization `A=V diag(λ0,λ1,λ2) V†`, with
`λ0 λ1 λ2=1`. Let the cyclic permutation
matrix `P e_j=e_(j+1 mod 3)` (`det(P)=1`).
Set diagonal factors

```
d0=1; d1=1/λ1; d2=λ0.
D=det(diag(d0,d1,d2))^(-1/3) diag(d0,d1,d2).
```

The common unit complex cube-root scale makes
`D∈SU(3)` without changing the commutator.
Then

```
[P,D]=P D P^-1 D^-1
      =diag(d2/d0,d0/d1,d1/d2)
      =diag(λ0,λ1,λ2).
X=V P V†, Y=V D V†; X,Y∈SU(3);
[X,Y]=A.
```

This elementary matrix specialization is a constructive
proof of the SU(3) case of Gotô's classical general
theorem, not a newly discovered theorem credited to DASHI.
Repeated spectral factorizations need not be unique or
continuous as functions of `A`; **no such continuity**
is required for an abstract discrete group homomorphism.

### All-stage compatible horned representation

For **arbitrary chosen root** `A∈SU(3)`, recursively set
`A_empty=A` and choose the pair from the commutator
factorization `A_w=[A_w0,A_w1]`.
At stage `n`, the generator assignment
`x_w↦A_w` extends uniquely to `rho_n:F_n→SU(3)`.
By construction,
`rho_(n+1)∘phi_n=rho_n`. The **universal property**
of the group colimit gives

```
rho_A : G_A -> SU(3)
rho_A(m_empty) = A.
```

**This answers the former infinite-image existence
obligation affirmatively for the abstract group.**
If `A` has infinite order then `rho_A(G_A)`
is infinite. The group `G_A` is perfect, and a
homomorphic image of a perfect group is perfect.
Thus a nontrivial image is necessarily **nonabelian**;
there is no conflict with the obstruction
`Hom(G_A,U(1))=1`.

### Three-sector C3 equivariance, on the SAME target space

For the new DASHI three-copy model
`G=G_A*G_A*G_A`, with cyclic factor rotation `r`,
take the existing charged-lepton phase generator
`T=diag(1,ζ,ζ²)∈SU(3)`, `T³=I`.
Define on free factor `j∈{0,1,2}`

```
rho_j(g) = T^j rho_A(g) T^{-j}.
```

The free-product universal property supplies one
representation `rho:G→SU(3)` and immediately gives
`rho(r(g))=T rho(g) T^{-1}`.
Consequently the **semidirect extension**
`K=G⋊_r C3` has an ordinary homomorphism

```
R(g,j) = rho(g) T^j ∈ SU(3).
```

The target uses ONE specified 3D complex Hilbert space.
In particular `R(r)=T`, `R(m_(0,empty))=A`.
If `A=TS1` from PR #1247, its finite-group
Galois-trace obstruction already proves infinite
order, hence `R(K)` is an **infinite nonabelian**
SU(3) subgroup. Note `T^{-1}A=S1`;
the subgroup also contains both original residual
generators T and S1. This is a genuine abstract
equivariant **existence construction**, not merely
matching representation dimensions.

### Exact mathematical source and numerical receipts

New source-written owner:
`DASHI/Mathematics/Topology/AlexanderHornedC3CompactCommutatorRepresentationExact.agda`.

It **reuses** the actual native `HornAddress`,
`expandWord`, `rotateWord` and C3 type, accepts
the Gotô commutator section and automorphism as
explicit structure, recursively defines a value at
each horn, and proves:

- each address equals its two-children commutator;
- every source-word horn refinement preserves target value;
- every source-word C3 rotation corresponds to target twist;
- zero new postulates and no imaginary SU(3) group kernel.

The analytic instantiation (Gotô theorem / explicit
spectral diagonalization) and the infinite colimit's
universal property are **mathematical source inputs**,
not falsely claimed as Agda kernel results.

New real-matrix executable:
`scripts/alexander_horned_c3_su3_constructive_probe.py`.
Independent local Python/NumPy/SciPy calculation on the
actual selected CP-nonzero neutrino `TS1`:

```
SU(3) initial unitary defect: 3.18e-16
five binary refinements: 31 parent equations, 32 leaves
worst commutator defect: 4.99e-15
worst determinant defect: 2.56e-15
worst unitarity defect: 4.60e-15
three C3 arms: worst commutator defect < 4.8e-15
||A^5-I|| ≈ 1.98957907 (not a fifth root of identity)
```

An **independent extended 8-level** calculation
checked 255 parent commutator equations, 256 leaves
with worst commutator defect `7.84e-15`.
These are finite *numerical* residuals, not
an infinite-tree kernel or exact SU(3) spectral proof.
The exact Q(ζ3) determinant/unitality of the selected
target was separately verified in Python **Fractions**
and source-written in sibling PR #1247.

### The decisive anti-overpromotion insight

Since this theorem works for **EVERY A∈SU(3)**,
the mere existence of a horned-group-to-SU(3)
representation has **zero discriminating power**
for a proposed PMNS phase. There is no source-side
criterion selecting the phase `δ=120°`, the angle
triplet or the physical lepton mass operator.
The choices at each commutator split are enormous.
Hence an *actual* claimed geometric/QFT identification
must add strong constraints such as canonical geometric
holonomy, finite-energy/smoothness, compatible
charged-current and mass terms, same-object
operator intertwining, or predictive restrictions
which distinguish measured flavour parameters.

**Most important no-go corrected:** the old roadmap
entry "construct any infinite-image equivariant
horned `G→SU(3)` representation" is PAID in ordinary
mathematics for the **abstract direct-limit group**.
The open problem is a **physically selected / geometrically
grounded** representation, not its abstract existence.

### Acceptance and remaining certification

```sh
python3 scripts/alexander_horned_c3_su3_constructive_probe.py
agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3CompactCommutatorRepresentationExact.agda
```

New source file and probe have GitHub source read-back
but no exact-head Agda or committed-script runtime
receipt at this point. The independently locally
executed matching numerical construction did pass.
Wild three-copy geometric π₁, a continuous flat
SU(3) local system on that specific manifold, a
physical lepton/VOA same-object map and neutrino
likelihood fits are still independent obligations.

## 2026-10-24 follow-up: original DASHI compact-Lie group cross-pollination

We **already have** a full generic Yang–Mills group/Lie stack in
`SUNMatrixCarrier`, `SUNMatrixLieAlgebra`, `SUNMatrixLieGroup`,
`SU3MatrixInstance`, `CompactLieGroupCore` and
`CompactLieGroupDerived` (see `Docs/CompactLieYangMills.md`).
The positive Gotô/Hatcher horn representation MUST consume
those named original theorem owners, not invent an incompatible
`SU3` constructor or confuse `[X,Y]=XY-YX` in the Lie algebra
with `[x,y]=xyx^-1y^-1` in the group.

### New group-native source owners

1. `DASHI/Physics/YangMills/CompactLieInnerC3Exact.agda`:
   elementary identities **derived** from the existing
   certified `Group`: inversion of a product,
   composition of inner conjugations, and
   `T*T*T=I => Ad_T^3=id`.
   This replaces a source-written, separately assumed
   inner-automorphism cube with an actual group power law.
2. `DASHI/Mathematics/Topology/AlexanderHornedC3SUNLieGroupReuseExact.agda`:
   derives conjugation preservation of inversion and of
   the GROUP commutator, instantiates the pre-existing
   `AlexanderHornedC3CompactCommutatorRepresentationExact`
   on the literal `SU3.su3MatrixGroup` carrier, and
   exposes a *separately provided* `GotôGroupSection`.
   It does not create another subgroup or representation
   with a coincidentally similar name.
3. `tests/test_alexander_horned_c3_sun_reuse.py`:
   exact A5 permutation controls of the group-level laws,
   all group commutator roots, and five-level C3 horn refinement.

Independent exact local audit: A5 60 elements, commutator
section 60/60, **7,200** product/commutator
inner-conjugation identities, 32 five-level leaves with
C3-equivariant refinement, selected meridian order 5,
selected inner-rotation order 3 — **PASS**.
This is a finite nonabelian adversarial check and NOT a
proof of the analytic SU(3) Gotô theorem.

### The lepton target is now welded to that canonical interface

Sibling <https://github.com/chboishabba/dashi_agda/pull/1247>
added exact T³, unitarity and determinant source clauses to
`NeutrinoHornedSU3RootExact.agda`, then
`NeutrinoExistingSUN3CarrierWeldExact.agda`
transports them into the *existing* Yang–Mills
`SUNMatrixElement` subtype **given** a certified
concrete function-backed 3x3 matrix theory, operation
compatibilities and extensionality.  The source
DERIVES special-unitary membership of both
`A=TS1` and `T`, and derives T³ as an equality
in the original SU3 group, rather than accepting
those as independent witnesses.

Independent exact Fraction calculation verified
**45** matrix-entry equalities, determinant one
for A and T, T³=I and Ad_T³(A)=A.
The function extensionality, the concrete
`CertifiedSUNMatrixTheory 3` instance, the
analytic global Gotô section and exact-head Agda
compiler remain distinct UNPAID obligations.
The nine-cell `QutritMatrixGates.Matrix3` record
is viable prior art for a function-extensionality-free
presentation, but has not itself been equipped with
all the SU3 matrix axioms in this PR.

### Mathematical and physical promotion boundary

Original group commutator surjectivity belongs to
Morikuni Gotô, *J. Math. Soc. Japan* (1949),
DOI 10.2969/jmsj/00130270.
Lie-algebra bracket surjectivity, a DISTINCT fact,
is treated for example by Malkoun–Nahlus,
*Journal of Lie Theory* **27** (2017) 1027–1032,
DOI 10.5802/jolt.980.

The horn group's abstract infinite-image
C3-equivariant representation remains an existence
result. Since Gotô supplies factorizations for
**every** SU3 target, it does not select the physical
lepton mixing matrix; mathematical `SU3` also
does not mean physical QCD colour `SU3`.
A source-specific geometric holonomy/energy
selection, experimentally predictive mass mechanism,
kernel receipts and neutrino likelihoods remain open.

**Commands / not asserted as run:**
```sh
agda -i . DASHI/Physics/YangMills/CompactLieInnerC3Exact.agda
agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3SUNLieGroupReuseExact.agda
python3 -m unittest discover -s tests -p 'test_alexander_horned_c3_sun_reuse.py' -v
```


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

## 2026-10-24 max-cut execution receipt — local Python instead of CI

**A genuine execution upgrade, not another source-written claim.**
Both PRs' relevant GitHub Python files were reconstructed locally, and
their Git blob SHA-1 values recomputed over the exact bytes
(`sha1("blob "+size+"\\0"+bytes)`), then cross-checked by an
independent connector read-back at the target branch heads. All eight
blobs, including the newly committed SymPy verifier, matched.

Local Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0 and SymPy 1.14.0:

- **26/26 committed Python unittest cases PASS** (four owner files):
  horn A5 root 4/4, original compact-Lie group reuse 4/4,
  leptonic complex CP 11/11, and nontrivial SU3 root 7/7.
- **Original horn A5 stage probe PASS**: 60/60 commutators,
  corrected selected root of order five, binary depth 5.
- **Original horn finite VOA actor probe PASS**: 4,000
  deterministic semidirect-product/action tests and
  180-coordinate algebra invariance; c=0 commutative
  construction only, not a CFT-type Monster VOA.
- **Original Schur SU3 horn probe PASS**, depth 5 (31
  parents / 32 leaves), maximum commutator residual
  4.9850e-15, unitarity defect 4.5979e-15, determinant
  defect 2.5631e-15; an unmodified import run at depth
  8 passed 255/255 parent relations, 256 leaves, worst
  residual 7.8366e-15.
- **Symbolic Q(zeta3) matrix verifier PASS**:
  ten independent polynomial identities for arbitrary
  3x3 entries, including associativity, dagger
  anti-homomorphism, determinant product and conjugation.
  This is stronger than a numerical finite sample but
  **not** an Agda proof of `CertifiedSUNMatrixTheory`.

New reproducible owner receipt:
`logs/research/horned_local_python_exact_head_receipt_20261024.json`.
Sibling owner PR #1247 has a matching evidence receipt and the
executed SymPy script
`scripts/audit_neutrino_sun3_symbolic_matrix_laws.py`.

**Reconciled grade change**: Older `committed Python tests NOT RUN`
statements in previous chronological iterations refer to their
historical state and are superseded for these **specifically
blob-matched tests**. Agda/Lean kernel certification, fully
instantiated concrete `SUNMatrixTheory 3`, Gotô's theorem
formalization, geometric horn pi1 identity, QCD/PMNS physical
connection and original likelihood fits remain unverified.
No CI requirements have been introduced.

## 2026-10-24 cross-owner steelman correction: conjugation orbit vs physical character

Neutrino consumer PR #1247 now contains canonical
`Docs/physics/HornedLeptonC3SteelmanPhaseGate20261024.md`,
`NeutrinoHornedC3RephasingNoGoExact.agda` and two local
source-hash-matched Python regressions.

**Important new no-go:** The genuine nontrivial three-element
SU3 matrix orbit under `Ad_T` does NOT imply three physically
different measured horn holonomies: for ANY C3-equivariant
rho satisfying `rho(r(g))=T rho(g) T^-1`, the
gauge-invariant character/Wilson trace obeys
`tr rho(r(g))=tr rho(g)` for all horn words g.
Simultaneously rotated word products are likewise conjugate.
The selected PMNS implementation is additionally a charged-
lepton row rephasing; J, all vacuum transition probabilities,
source flavour ratios and covariantly rotated Hnu agree EXACTLY.

**Second source-grade boundary:** original Gotô 1949 theorem
provides single commutators in connected compact **SU3(C)**,
not automatically in the countable cyclotomic-rational
SU3(Q(zeta3)) group. Standard cyclic witness of diagonal T
already needs a primitive ninth root of unity not in Q(zeta3).
Keep abstract ambient SU3 existence PAID but exact-field
closure/Agda concrete bridge OPEN. Do not claim a general
nonexistence theorem for all Q(zeta3) commutator sections.

This is a physical *falsifier* of the naive three-orbit
interpretation, not a retraction of valid Hatcher/Gotô group
algebra, the finite A5 quotient, or the nontrivial C3 outer
source action. The strong physical steelman must exhibit
an independent, gauge-invariant relative geometry, source,
boundary condition or interaction with a measurable response.
The **three-copy actual wild-embedding pi1** and geometric
flat-bundle identification remain OPEN. New exact local
stand-ins PASS 36/36 selected cross-PR tests, 10/10 SymPy
universal matrix laws, no Agda kernel or CI promotion.

## 2026-10-24 maximal-return horn physical regularity gate

**Concrete novel mathematical question rather than more C3 encoding:**
Does the actual three-copy wild exterior admit a
compatible family of local geometric representative
loops for *every* Hatcher binary generator, with
\(\max_{|w|=n}\ell(\gamma_w)\to0\)?
The abstract source group and finite numerical
VOA/commutator probes DO NOT prove this metric condition.

If YES, a bounded SU3 connection in compatible local
frames on their accumulation neighborhood satisfies
\(\|Hol(\gamma_w)-I\|\le M\ell(\gamma_w)\to0\).
But unitary group commutator compression forces
\(\|Hol(m_{root})-I\|\le
 (2\epsilon_n)^{2^n}/2\); hence all such
nontrivial root holonomies are **excluded**.
For the selected CP toy W, δ=\(\|W-I\|_{op}\)≈
1.43818847527, and at every depth some descendant
must have gap at least \((2δ)^{1/2^n}/2\to1/2\).
So the representation constructed with Gotô cannot
automatically be realized by a bounded smoothly
extendible physical connection on an arbitrarily
shrinking horn geometry. That is a *conditional,
quantitative obstruction*, not a contradiction of
abstract group existence or a full finite-energy
no-go for singular boundary defects.

**Owner-side reproducible numeric stand-in:**
`scripts/alexander_horned_c3_su3_regularization_no_go_probe.py`,
independent of sibling unmerged branch imports.
The analytic proof should reuse existing
`DASHI/Geometry/FlatFormalDiskHolonomySurface.agda`
operator-norm/holonomy-limit targets rather than
importing a new normed analysis authority.

**Physics cross-cut:** Selected W has a conditional
gauge-invariant unpolarized two-path fringe
\(P_+(0)≈0.67048481558\), but one \(\pi_1(S^1)\)
loop suffices to reproduce it; a first-level
noncommuting pair can be reproduced by \(F_2\).
Distinguishing *horned* structure requires
compatible all-depth geometry or multiscale
regularity, not a single Wilson trace. New physical
decision-grade owner in sibling #1247:
`Docs/physics/HornedSU3ObservableRegularityParetoMaxCut20261024.md`.
No actual wild-embedding metric estimate or
Agda kernel result is claimed.
