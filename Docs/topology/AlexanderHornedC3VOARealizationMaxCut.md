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
