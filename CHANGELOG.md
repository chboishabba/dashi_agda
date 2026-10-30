# Changelog


## 2026-10-30 — S3-equivariant three-class middle-child index

- Added 36-case \`middleChildClassCriterion\` to the existing canonical
  ternary boundary Agda module: two ABC relabellings have the same
  unoriented peripheral conjugacy class precisely when they have
  the same middle-generator image \`p(b)\`.
- Reused the pre-existing S3 composition theorem to prove
  \`middleChildIndexEquivariant\` and six orientation-flip facts.
- Independently checked 36 index/class comparisons and 36
  transport cases. Exact-head Agda kernel/CI still unrun.
  The three-class chart is algebraic, not the wild complement.



## 2026-10-30 — ABC orbit follow-on: six genus-one algebraic charts

- Added \`sixPuncturedTorusBoundary\` to the existing Agda ABC
  orbit module, transporting the source-owned Nielsen
  punctured-torus commutator coordinates across all six
  existing S3 permutations.
- Independently executed 6 genus-one, 6 inversion and 36
  group-transport finite cases. GitHub source readback passed;
  the committed Python regression itself, exact-head Agda/Lean
  kernels and CI were not run. G3 embedded-surface geometry
  remains open.



## 2026-10-30 — Alexander horned ABC six-permutation peripheral orbit (PR #1244)

- Reused \`TernaryEndomorphismConjugacyExact\`,
  \`TernaryPermutationS3LawsExact\` and the original meridian source.
  Existing SSSP six linear orders and the external-sector S3 were
  source-inspected, not duplicated or confused with child relabelling.
- Extended the canonical
  \`AlexanderHornedTernaryPantsMeridianBoundaryExact.agda\` owner
  with \`ABCSixPermutationPeripheralOrbit\`: all six anchored
  free-word computations, six distinct oriented normal forms,
  three unoriented conjugacy pairs, and 36 finite S3
  algebraic boundary-family transport cases.
- Extended the existing
  \`scripts/alexander_horned_signed_meridian_stabilizer.py\`
  rather than adding a competing enumerator.
- Documented strict G4 alternatives:
  one selected meridian/stabilizer/based path versus an actually
  geometric orbit-indexed six-boundary construction. G2–G6 open;
  no exact-head Agda/Lean kernel, no CI, no completed embedded
  wild exterior or physical/Monster same-object claim.
- Read the current #1414/#1438 Agda and #103 Lean contexts;
  their theorem ownership remains independent. No ESD edits.


This changelog is append-only. Older mentions of `false` are historical wave
records unless the entry explicitly states it is describing the current live
monitor surface.

## 2026-07-19 — Wetsuit seam optimisation boundary

- Added `DASHI.Geometry.WetsuitSeamOptimisationBoundary`, a fail-closed typed
  carrier for body-zone design priors, material/panel budgets,
  manufacturability evidence, weighted seam cost, admissibility, relative
  optimality, validation gates, and split advice.
- Added `DASHI.Geometry.WetsuitSeamOptimisationRegression` with canonical
  underarm/inner-leg preference and shoulder/spine avoidance prior receipts,
  while keeping continuum optimality and manufacturing authority explicitly
  unpromoted.
- Added the compact aggregate `DASHI.Geometry.WetsuitSeamOptimisation`.
- The module formalises the optimisation and obligation surface only; it does
  not claim universal biomechanics, continuum-mechanics closure, or certified
  manufacture. `DASHI.Everything` was not run in this connector-backed pass.

## 2026-07-13 — P06 duplicate-free valid-walk enumeration

- Added and focused-checked `P06GeneratedWalkUniqueness.agda`.  Under the
  canonical neighbour adapter it proves extension-block `NoDuplicates`,
  recursive block disjointness, and
  `generatedWalkVertexListsNoDuplicates` without postulates or proof-heavy
  `WalkObject` equality.
- Added `GeneratedWalkVertexListSemantics`, packaging generated valid-walk
  lists, extensional completeness, duplicate-freedom, and the single
  `countWalks ≡ length` bridge.
- Added focused-checked additive `P06ConcreteEnumerationEndpoint.agda` and
  `P06SkeletonEnumerationSurface.agda`.  The former makes DFS membership an
  explicit field of a membership-indexed map; neither module touches the
  legacy total-index API.
- Added focused-checked `P06ConcreteSkeletonWitness.agda`, which proves all
  individual-candidate chooseN facts and packages the remaining skeleton list
  obligations (`complete`, vertex-list uniqueness, and count agreement)
  without pretending they are derivable from an arbitrary list.
- Added focused-checked `P06DFSValidWalkSurface.agda`.  It packages the
  minimal per-skeleton `WalkObject` plus equality to `dfsWalkRange`, derives
  generated-list membership and soundness, and adapts map witnesses to the
  membership-indexed endpoint.  It deliberately does not infer path validity
  from `DFSCover` coverage alone.
- `Everything.agda` was not run.  The remaining P06 mathematical blocker is
  now the genuine DFS-valid-walk membership witness; the legacy total-index
  record remains compatibility-only.

## 2026-07-13 — Corrected P06 walk status

- Corrected the P06 record: recursive walk completeness has landed through
  `walkObjectsCompleteByVertices`, and successor-membership inversion has
  landed through `walkObjectsSucMemberByVertices` and
  `walkObjectExtendMemberByVertices` in
  `DASHI/Physics/YangMills/GraphCombinatorics.agda`.
