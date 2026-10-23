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

These are **conditional type-theoretic results**, not instances for
the real three-manifold. In particular a finite word moving under C3
does not by itself prove that the corresponding geometric outer
automorphism is nontrivial.

## Geometric bridge: exact missing obligations

Choose a standard 120-degree rotation of S3 (the one-point
compactification of R3). Begin with a round 3-ball and attach three
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
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3FiniteStageExact.agda
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3ExteriorBridge.agda
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3CharactersExact.agda

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
