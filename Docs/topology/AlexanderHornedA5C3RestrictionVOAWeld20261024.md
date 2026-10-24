# A5 to C3 (j=0..35) reused in Alexander horned VOA actor

Date: 2026-10-24. Parent: PR #1244 / original three-copy Alexander
horned sphere programme.

## Found prior art — NOT a new A5-C3 discovery

This is the exact existing A5/C3 owner, not an inferred naming match:

1. `DASHI/Foundations/IcosahedralSO3RestrictionJ0To35Exact.agda`
   computes the five A5 irrep dimensions 1,3,3',4,5 and the
   exact character values on the third-turn class 1,0,0,1,-1,
   with SO3 j=0..35 decomposition. Original mathematics: Serre,
   Fulton/Harris, classical icosahedral representation theory.
2. `DASHI/Foundations/PolyhedralFiniteRestrictionInstancesExact.agda`
   exposes `icosahedralC3` with the existing
   `icosahedralFixedDimension` function.
3. `DASHI/Foundations/PolyhedralFixedSpaceSpectrumJ0To35Exact.agda`
   proves `fixedDimension(j,C3)=2 floor(j/3)+1` through exact
   recurrences, plus the C3 character-average identity for
   all 36 spins j=0,...,35.
4. `DASHI/Mathematics/Topology/AlexanderHornedC3FiniteVOAActorExact.agda`
   already owns the exact C3-sector-permuting action of the quotient
   actor `A^3 rtimes C3` on `C3 x A`.
5. `DASHI/Mathematics/Topology/AlexanderHornedC3VOAModeLiftExact.agda`
   already lifts that actor pointwise to the **same** rational
   commutative vertex-algebra state space, importing
   `TrivialRationalGradedVertexAlgebraExact` for genuine mode laws.

Crucial distinction: the pre-existing arrow is *restriction of
representations along* `C3 <= A5`; it is NOT a nontrivial group
homomorphism `A5 -> C3`, which would contradict simplicity and
perfectness of A5. The notation "A35" did not turn up as a literal
named theorem in these repositories; the closest documented existing
owner is A5 restricted to C3 over SO3 j=0..35.

## Mathematically sharp new joint actor

Let the group G be the three-root Hatcher free-group colimit,
with a C3_ext automorphism r cyclically permuting its three factors.
Use the existing nonabelian quotient construction (conditional on
the source-to-quotient proof) to obtain

    G rtimes C3_ext -> A5^3 rtimes C3_ext = Q.

Select s=(0 1 2) in A5, order three. Then

    u = ((s,s,s),0) in Q,    v=((e,e,e),1) in Q

satisfy u^3=v^3=1, uv=vu, with u,v independent. This realizes the
**internal** C3 subgroup of A5 and the **external** C3 of the
threefold horn construction, as a common C3xC3 subgroup of the SAME
actor Q. The equality uv=vu is not true for an arbitrary non-diagonal
internal A5^3 element. The diagonal choice is the source-specific
condition.

On the previously constructed finite VOA's 180 coordinates

    Omega = C3_ext x A5

the H=C3_int x C3_ext action is

    (k,l).(i,a) = (i+l, s^k a).

Every nonidentity (k,l) acts without fixed coordinates. Thus Omega
splits into exactly 180/9 = 20 H-orbits, each isomorphic to H.
The permutation module on Omega therefore has character

    chi(1)=180, chi(h)=0 (h != 1),
    C[Omega] = 20 Reg(H).

Over Q(zeta3), each of the nine H-characters occurs with
multiplicity 20. Over Q the nontrivial eigenspaces pair into
2-dimensional rational representations; DO NOT claim nine rational
one-dimensional characters.

Independent check by existing A5 class table:
for irreps of dimensions [1,3,3,4,5] and third-turn traces
[1,0,0,1,-1], the fixed dimensions are [1,1,1,2,1], so in the
A5 regular representation

    dim(C[A5]^C3) =
      1*1 + 3*1 + 3*1 + 4*2 + 5*1 = 20.

The three-sector VOA has internal C3-fixed dimension 60,
external C3-fixed dimension 60, and common C3xC3-fixed
dimension 20. None of this identifies the finite VOA with the
Monster moonshine module, nor the geometric outer automorphism with
a selected Monster 3B element.

## Exact implementation

- `DASHI/Mathematics/Topology/AlexanderHornedA5C3RestrictionWeldExact.agda`
  reuses the existing `icosahedralC3` spectrum and exact finite
  actor; it requires a genuine order-three element of the actual
  factor group rather than inferring one from representation
  dimension. It proves internal/external commute on the *same*
  coordinate carrier and rational VOA state functions, internal
  period three, nontriviality, and both actions' compatibility
  with all existing pointwise vertex modes.
- `DASHI/Mathematics/Topology/AlexanderHornedA5C3CharacterRestrictionExact.agda`
  directly reuses the prior A5 character table to verify each
  third-turn trace, regular dimension 60, internal fixed 20,
  and j=0..35 C3 probe agreement.
- `scripts/alexander_horned_a5_c3_restriction_weld.py`
  enumerates all 60 even permutations and 180 VOA positions,
  tests the two commuting order-three actions exhaustively,
  confirms 20 free orbits of 9, nine Fourier multiplicities 20,
  the regular A5 C3-fixed dimension 20 and every j=0..35 average.

An INDEPENDENT local Python reproduction of the finite equalities
passed for 60 A5 elements, 60/60 commutators, all 180 positions,
20 x 9 orbits and the 36 j character averages. The committed
script did not itself return a fetched/executed receipt in the
tool-accessible runtime; the equality is an independent reproduction
rather than a claim that GitHub Actions completed.

## Proof and attribution boundaries

The previous topology and VOA formalizations are source-written;
the new two modules are source-written, NOT exact-head Agda
kernel-certified. The runtime did not contain Agda or Lean and
no successful workflow receipt was available during this change.

The selected A5 3-cycle in Python is a concrete permutation,
but an Agda inhabitant of `InternalC3Element` for an actual
proof-bearing 60-element permutation group is still needed. The
prior SO3(j)-restriction object and the A5 regular-permutation
module have the same **abstract** C3 subgroup type; they are not
identical representations, and no same-carrier intertwiner between
them has been fabricated.

Actual geometric pi1 identification remains the separate van
Kampen/collar/nested-limit proof. The VOA regular actor need not
be faithful on G; `AlexanderHornedC3VOAKernelBidiExact.agda`
already records precisely this information-loss boundary.

Run (repo root):

    python3 scripts/alexander_horned_a5_c3_restriction_weld.py
    bash scripts/check_alexander_horned_c3_exact_head.sh

The existing focused GitHub workflow also includes the finite
A5/C3 audit. No need to reimplement generic cyclic groups,
another VOA carrier, or the icosahedral branching table.


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


**Stronger no-embedding consequence:** because the kernel of the
projection `G ⋊ C3_ext -> C3_ext` is torsion-free, its restriction
to ANY finite subgroup of the source semidirect product must be
injective. Consequently all finite subgroups of `G⋊C3_ext` have
order at most three, so `C3×C3` cannot embed there at all.
The 9-element faithful action is strictly a quotient phenomenon.
This is a stronger operational discriminator than contrasting
two abstract labels `C3`.


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
