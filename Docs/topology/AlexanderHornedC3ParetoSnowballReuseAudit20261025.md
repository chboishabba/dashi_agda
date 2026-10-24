# Alexander horned C3 — Pareto / snowball / Ibrahim cross-reuse audit (2026-10-25)

## Context and rule of evidence

This audit inspects the **actual PR #1244 branch** in
`chboishabba/dashi_agda`, and preserves author/proof provenance:
Alexander (1924) first wild-sphere construction; Hatcher
*Algebraic Topology* Example 2B.2 establishes the punctured-torus
stage group maps; Lippert's supported horned-ball exposition provides
the relative support strategy. None of these classical results is new
work in DASHI. Distinguish repository source-written theorem, tested
script, formal kernel result, conditional theorem interface, and
laboratory measurements.

## Existing machinery that should be re-used, not recreated

| Existing repository file | Relevant interface | Honest proof boundary |
|---|---|---|
| `proofs/horned_c3_lean/HornedC3/ThreeArmVanKampen.lean` | `ThreeArmCollarCover`, `threeArmCoverPi1FreeProduct` | conditional on actual open sets, path-connectedness and trivial overlap groups; imported Hatcher van Kampen theorem |
| `proofs/horned_c3_lean/HornedC3/ThreeArmCollarIntersections.lean` | `collarPairIntersectionEq`, `collarTripleIntersectionEq` | disjoint satellite-only set regions required; does not instantiate Euclidean wild satellite |
| `DASHI/Mathematics/Topology/AlexanderHornedC3ExteriorBridge.agda` | `EquivariantMeridianGroup`, `interpretExpansionAtEveryStage` | abstract relations and equivariance; actual exterior identification not supplied |
| `DASHI/Mathematics/Topology/AlexanderHornedC3ComplementActionExact.agda` | `InvariantSubsetC3`, `rotateExterior` | invariant points, not automatic continuity or induced pi1 isomorphism |
| `DASHI/Mathematics/Topology/AlexanderHornedC3CompactCommutatorRepresentationExact.agda` | `CommutatorSectionGroup`, `everyHornExpansionPreservesValue`, `wordRotationEquivariant` | conditional group section; SU3 instantiation and direct-limit universal property not machine certified |
| `scripts/alexander_horned_c3_finite_SU2_gauge_simulator.py` | `build`, `tower`, `expand`, `simulate` | exact finite 2I labels, noisy synthetic readout, not flat experimental geometry |
| `scripts/alexander_horned_c3_independent_noise_envelope.py` | `expected_halftrace`, `max_sigma_degrees` | exact iid isotropic gate-noise expectation, NOT general correlated errors |

Cross-cut principle: reuse **actual typed consumers** before adding novel representations. The mathematical dependency graph is
real supported infinite embedding -> relative collar maps -> open cover
and path connectedness certificates -> Lean van Kampen consumer ->
topological pi1 -> inherited C3 permutation on factors -> flat
SU2 representation (auxiliary gauge choice).
A finite actor or software simulator does not reverse any of these arrows.

## This cut: link the actual compiler to the analytic result

`scripts/test_alexander_horned_C3_noise_compiler_integration.py`
runs the repository's actual stage generator and fully expanded
commutator word, checks its gate count `3*4^n` and noiseless -I
target, and compares ensemble means for both pre-shot and post-shot
signals with the iid expectation from the envelope script. This
catches mistaken transfer of the envelope from a toy identity
product to the actual noncommuting horn-word compiler.
The test is committed but *was not executed in the local runtime
in this cut* (GitHub-only connector access). No pass is claimed.

## Pareto gaps, sorted by impact and exactness

**P0 topology:** instantiate actual Euclidean exterior open sets
satisfying `ThreeArmCollarCover`, especially all pair and triple
path-connectivity requirements and the overlap pi1 triviality.
Do not confuse a spherical cross-sectional open disk with a complete
open-cover deformation-retract certificate. Use the extant pair/triple
set identities and the explicit separator atlas; demand actual
set inclusion maps and a collar-based homotopy equivalence of each
satellite piece with Hatcher's exterior. Source-backed paper argument
and kernel-checked global theorem are different statuses.

**P0 formal proof boundary:** review whether the branch's Lean imports
and Hatcher-at pinned dependency compile *unchanged*. The present
file text shows a proof-bearing conditional theorem; without
typechecking this exact head, record status as source-written.

**P1 gate strategy:** bound practical physical resource scaling.
The same-element substitution `[a,b] -> q` is a valid group-equality
optimisation if the control system can implement `q` as a calibrated
gate, but is **not** automatically the same physical homotopy loop.
Provide two separate certificates:
(A) algebraic matrix equivalence and (B) preservation of the
specified spatial/graph path or experimentally implemented
connection. Without B, a short logical gate sequence is an
emulator of the same holonomy value but not a compressed execution
of the original geometric traversal.

**P1 controls:** phase calibration, deliberately correlated errors,
independent plaquette flatness measurement, Q8 recursion-failure
and commuting-U1 contrasts. Falsifiers must be independent of
the signal used to fit the model.

**P2 physics:** specified domain, boundary condition and
self-adjoint Maxwell/Dirac operator on finite geometries, matched
controls and experimentally resolvable spectral shift; no spectral
effect follows just from an abstract fundamental group.

## Snowball / attribution decisions

Expand citations **outward only from a precise unresolved theorem
or discriminator**: relative collar equivalence, finite-depth gauge
compilation, or self-adjoint spectral boundary conditions. First look
for the original theorem, then applications and independent
replications. Repeated secondary descriptions of the Alexander
horned sphere are not independent proof roots. Cross-reference
already-present Hatcher / Lippert / Brown / Grillet / Sugawa /
Liang / flat holonomy references rather than adding names to the
roadmap without a corresponding new mathematical obligation.

## Phase acceptance

* Algebraic stage relations: existing exact finite scripts and
  conditional theorem sources — done in their stated senses.
* Analytic iid gate error budget: derived, implemented.
* Real-word compiler integration: test source committed; execution
  outstanding.
* Geometric same-object identification: classical paper proof sketch
  with explicit geometry; kernel-level topology maps still open.
* Physical platform: design only; no measurement or claim about
  wild geometric quantum phenomena.
