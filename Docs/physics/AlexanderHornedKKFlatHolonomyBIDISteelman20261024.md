# Alexander horned C3 -> KK/EM U(1) BIDI max-cut (2026-10-24)

Source: Hatcher, Algebraic Topology, Example 2B.2, pp. 170–172, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf. Alexander (1924), original horned sphere. Classical result: the complement of the solid horned ball is an open noncompact three-manifold, with nontrivial perfect fundamental group. The sphere remains intrinsically S². Do not invoke the closed-manifold Poincaré theorem here.

## Actual existing implementation, not invented
The dedicated branch `alexander-horned-c3-equivariant-20261024` carries the three donors:
- `AlexanderHornedC3FiniteStageExact.agda`: THREE cyclic sectors, each with a BINARY horn address tree; B3 permutation-image identities; rotation commutes with every finite commutator replacement; target C3 commutators vanish. **Three marked copies are algebraic sectors, not an established C3-equivariant geometric horned embedding.**
- `AlexanderHornedC3ExteriorBridge.agda`: abstract C3-equivariant meridian group and semantic interpretation; geometric exterior pi1, essential meridian, and actual C3 action are still external witnesses.
- `AlexanderHornedC3CharactersExact.agda`: any C3-valued character kills every meridian; with a meridian-generation witness it is the trivial character. The finite C3 action itself can be nontrivial.

## Strong new theorem and BIDI consumer
`AlexanderHornedAbelianHolonomyBIDIExact.agda` strengthens C3-only characters to every ABELIAN target:
- exact abstract commutator neutralisation from commutative group identities;
- any homomorphism of the given recursively commutator-defined meridian group into an abelian group annihilates each meridian;
- given generation by meridians, the entire character is trivial;
- consequently every abelian character identifies C3-rotated loop classes;
- given an essential meridian, explicit `ClaimNonTransportWitness` for `character : LoopClass -> AbelianValue` against `id : LoopClass -> LoopClass` and a theorem prohibiting this information-losing BIDI transport.

This applies **only** to flat U(1) gauge holonomy as a homomorphism pi1(E)->U(1), not to general electromagnetic holonomies with nonzero curvature. It does not prove the KK gauge field or Earth source has a wild boundary, nor does it supply an actual principal bundle, connection, smooth gluing, or electromagnetic field equations.

By classical Alexander duality, the horned-ball exterior is homologically acyclic even though pi1 is nontrivial. Assuming usual paracompact-manifold bundle classification, H²=0 means principal U(1) bundles on that exterior are topologically trivial. Do NOT mistake global triviality for flatness, vanishing curvature or unique connection. Higher nonabelian/twisted representations or explicit ambient complement topology are the consumers capable of distinguishing some of this information.

## Same-consumer cross-PR integration
The independent gravity PR #1241 already contains `KKSteelmanBidirectionalConsumerExact.agda` and existing `FormalClaimTransportGeometryExact` no-descent infrastructure. It can consume the horned-sphere donor as a **topological countermodel** for a stronger global/gluing/holonomy consumer, without assuming the full KK-Earth physical steelman is satisfied.

Candidate comparison:
- **C_local**: local metric circle block and U(1) gauge-shift identity; previously proved on its own surface.
- **C_flat**: flat U(1) holonomy characters. For the horned model, all meridian images vanish; C_flat cannot recover the ambient pi1.
- **C_global**: complement pi1, local flatness, global bundle topology and admissible junction/smooth structures. Needs external geometric realization; cannot factor through C_local or C_flat.
- **C_earth**: source-compatible 5D field equations, smooth metric/gluing and terrestrial observables. No horned sphere evidence makes C_earth true.

Nonabelian detection caveat: the separate finite-stage `F2 -> S3` test has nonzero commutator, but it does NOT extend automatically to the PERFECT direct-limit horned exterior group (indeed a perfect group's map to S3 must be trivial because S3 is solvable). Do not promote finite-stage S3 computation to a full exterior representation.

## Pay the actual mathematical deficits, not another R-number series
1. Source the full geometric nested horn construction, prove C3-equivariant embedding of D³ (if one exists with claimed symmetry), and prove loop group is the exterior pi1 with injections/direct limit.
2. For actual KK geometry specify admissible manifold, boundary, smoothness, connection, matter action; prove the restricted consumer factorisation/obstruction, and distinguish flat from nonflat holonomy.
3. If physical application needed, derive a candidate 5D source action and junction conditions; horned topology alone has no LARES-2 implication.

## Acceptance/receipts
`python3 scripts/check_alexander_horned_abelian_bidi.py`: finite-stage checks, not an infinite-topology proof.
`agda -i . -i /path/to/agda-stdlib DASHI/Mathematics/Topology/AlexanderHornedAbelianHolonomyBIDIExact.agda`: intended exact-head kernel target, not executed here.
Attribution: Alexander and Hatcher own geometric/exterior topology; canonical DASHI BIDI/consumer modules own general factorisation; this branch proves the conditional algebraic no-descent and documents the physical KK boundary. No claims of proof of wild equivariant embedding, actual fundamental group or experimental physics.


## Paired detector theorem: exact shared-actor BIDI

`AlexanderHornedAbelianHolonomyBIDIExact.pairedFlatHolonomyBlindAndOuterActionDetectable` now *consumes the actual* `AlexanderHornedC3OuterDetectorExact.EquivariantQuotientDetector` owner together with the generic Abelian-character theorem. For ONE group G and its ONE `rotateLoop` operator, it produces both:

1. every Abelian character assigns equal values to a loop and its C3-rotated loop, PROVIDED every group element is represented by meridian words;
2. that same rotation is NOT inner, PROVIDED the source has the supplied equivariant surjective quotient with an externally witnessed non-inner target rotation.

This is a conditional SAME-OBJECT result and does not conflate a nontrivial order-three action on formal addresses with an actually realised geometric wild embedding.

**Topology precision**: acyclicity / H²(E)=0 applies to E=S³ minus the closed embedded horned BALL. The exterior R³ minus that closed ball differs by removing the point at infinity; its H² may be nonzero. The horned sphere K=boundary ball is itself different from the solid ball; never switch among these three base spaces when transporting cohomology or circle-bundle classifications.
