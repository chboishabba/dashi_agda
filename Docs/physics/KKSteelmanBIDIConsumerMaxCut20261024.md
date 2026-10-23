# KK × EM × Higgs × torque: BIDI against the strongest admissible steelman

2026-10-24 — PR #1241. Physics project only, no PNF, W3, or SensibLaw dependency.

## Two independent consumers

**Observable consumer**: a precise gauge invariant, physical metric, local frame-dragging, or orbital nodal rate, with specified source parameters and units.

**Steelman consumer**: the strongest physically justified interpretation of the model. Require all eight separately witnessed obligations: a consistent five-dimensional action for THAT candidate; global compact-circle assumptions and boundary conditions; matter coupling derived from the action; conserved physical Earth source; regular interior/exterior matching; radion and gauge stability; consistency with independent gravity tests; and a physical orbital observable.

BIDI backward-pulls a consumer's minimum required information. Its forward leg tries each existing donor. Only an inhabited factorisation/preservation witness licenses claim transport. A physical model need not be identical to another theory; different candidates can answer the same observable consumer while differing on their full steelman consumers. Numerical approximation requires its own norm, error bound, validity domain and provenance, not propositional equality.

## Reused canonical DASHI owners

- DASHI/Core/FormalClaimTransportGeometryExact.agda: ClaimTransport and non-descent contradiction.
- DASHI/Core/ConsumerDescentMinimalObserverExact.agda: consumer-indexed fibre equivalence.
- DASHI/Core/ConsumerFibreRepairExact.agda: repaired observer must distinguish collisions.
- DASHI/Core/AdmissibleConsumerFutureAdequacyExact.agda: static adequacy, future safety, and realizability remain distinct.
- DASHI/Core/AdmissibleConsumerMDLHyperfabricExact.agda: MDL/Pareto ranking comes AFTER admissibility and consumer adequacy.

## Donors, narrower consumers and strongest residuals

- GR × S1 product: product source compatibility including T55=trace(T4)/2; still needs a physically generated internal tension and viable stable compactification.
- Boosted Kerr black string (PRs #1238, #1239, #1241): KK stationary metric and conditional circular/eccentric orbital calculations; does not provide ordinary rotating Earth interior, matter coupling or calibrated scalar/gauge charge.
- Null electromagnetic KK pp wave (PR #1239): exact nontrivial 5D Ricci-flat fixture; no isolated rotating Earth or LARES nodal prediction.
- Linear sourced massive radion (PR #1241): exact scalar Helmholtz matching; mass/source not yet derived from the same 5D action or fed back into full Einstein equations.
- KK U1 gauge shift and Hopf circle bundle (PRs #1239/#1235): gauge/topological consumers only until smooth global metric, conserved sources and connection dynamics are supplied.
- Spatial SO3 torque and right-hand rule (PR #1164): orientation and angular momentum; not a direct homomorphism to physical U1 charge.
- Higgs/electroweak boundary (master): possible additional model-building inputs; no Higgs=radion identity and no justified Earth stabilisation mechanism.

## Exact finite probes and real theorem obligations

DASHI/Physics/Gravity/KKSteelmanBidirectionalConsumerExact.agda uses the existing ClaimTransport/ConsumerNonDescentWitness. Its proofs show:
1. A gauge-sector-only observation cannot recover a varying radion.
2. An orbital-only observation cannot recover the physical source compatibility flag.
3. Every adequate observer refinement must separate the witnessed colliding states.
4. A repaired finite observation can answer both limited observable and a small two-bit steelman proxy. It does NOT inhabit the separate eight-condition Earth steelman eligibility interface.
5. The original limited observable still factors through its own observation despite failure of the stronger consumer.

The executable 32-state audit checks eight factorisation/non-descent relationships including the insufficiency of a lone metric component for a two-component metric consumer. An auxiliary SymPy calculation checks the classical Lie algebra fact: so(3) is bracket-generated whereas u(1) is Abelian, hence a continuous infinitesimal homomorphism so(3) to u(1) must vanish. This does not forbid coupled physical representations, finite C3/U1 characters or gauge charges carried by matter.

## Backward steelman requirements for the next physical round

1. For each candidate, fix one action, global circle topology, source and its matter frame.
2. Derive or prove regular interior/exterior matching and scalar/gauge stability, not just a borrowed rotating vacuum geometry.
3. Check weak-field gravity, equivalence principle and fifth-force limits in the SAME physical coupling.
4. Derive slow-rotation and orbital observables at fixed physical source data, not just coordinate-dependent metric ratios.
5. Ask for an exact or bounded physical commuting diagram from its equations to the selected observable.
6. Rank Pareto/MDL only after the candidate satisfies the declared physical steelman and observable consumer, or transparently rank partial candidates only as research leads.

## Verification and attribution

Local Python finite consumer audit and Lie algebra constraints: PASS. Agda module: source-written, NOT kernel-certified here; verify with:

    python3 scripts/check_kk_bidi_steelman.py
    agda -i . -i /path/to/agda-stdlib DASHI/Physics/Gravity/KKSteelmanBidirectionalConsumerExact.agda

The latter is an acceptance command, not a certification receipt. No real 5D Earth model or empirical LARES bound is claimed. Standard physics remains attributed to the original KK, GR, and Lie-algebra literature; DASHI core owners are reused instead of claimed as new foundational theorems.


## Verified cross-PR donor: Alexander horned C3 and flat U(1) holonomy (PR #1244)

Donor: https://github.com/chboishabba/dashi_agda/pull/1244, branch `alexander-horned-c3-equivariant-20261024`.

The actual source files include:
- `DASHI/Mathematics/Topology/AlexanderHornedC3FiniteStageExact.agda`: three C3-labelled copies of a binary horn tree; finite-stage braid-permutation symmetry.
- `AlexanderHornedC3ExteriorBridge.agda` and `AlexanderHornedC3CharactersExact.agda`: conditional recursive meridian-group interpretation and C3-character no-go.
- `AlexanderHornedC3OuterDetectorExact.agda`: a surjective equivariant non-inner quotient detector, with Python A5^3 calculations separately attached.
- `AlexanderHornedAbelianHolonomyBIDIExact.agda`: generalized theorem for ALL Abelian character targets, essential-meridian non-descent, and a **paired same-group** proof: Abelian holonomy is blind to the cyclic rotation while an independently supplied non-Abelian outer-action detector witnesses its noninner character.

This is a stronger, consumer-dependent obstruction than simply saying wild and smooth topology differ. For the abstract recursively commutator-related group, flat U(1) holonomy (a representation pi1 -> U(1)) has zero character on its meridians; if they generate, the character is trivial. Non-flat U(1) Wilson loops are NOT fundamental-group characters and can be curvature-sensitive. A5^3 action detection is conditional on a specified quotient and a matched group, not a derivation of an Earth electromagnetic field. The three-root cyclic group is not yet the geometric pi1 of an equivariantly horned sphere: real nested embedding, van Kampen/direct limit and C3 geometric action remain open.

**Important ambient-space distinction:** for the open exterior E=S³ minus the closed embedded horned *ball*, Alexander duality gives acyclic reduced homology and H²(E;Z)=0. The punctured R³ exterior R³ minus that ball (infinity removed) can have different H²; do not import the S³ complement bundle classification without verifying which base is chosen. Likewise ordinary spatial Earth exterior has different H² and smooth-source conditions. No horned-sphere geometry is asserted for Earth.

BIDI consumer cases:
- local KK metric/gauge-shift: can pass independently of ambient pi1;
- global flat-U1-holonomy: cannot recover perfect-group meridians;
- non-Abelian outer action: may pass with a same-object A5^3 detector;
- physically admissible Earth KK: still requires same-action stress-energy, smooth boundary matching, physical matter coupling and observables. Horned-sphere results do NOT discharge these physical obligations.

This is a **cross-branch donor reference**, not a typed import into PR #1241: an actual merge or identical verified source ancestry is required before a typechecked KK module can use PR #1244 directly. Avoid duplicate topology definitions; retain the reusable theorem in the owning PR #1244. Existing BIDI/consumer owners remain the canonical transport theory.
