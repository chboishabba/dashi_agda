# Changelog

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

## 2026-10-30 — Pickover real-phase versus graph orbit-sum collision

- Added a stronger exact Machin-rational regression to `scripts/check_pickover_exact_interval_certificate.py`: the entire (99^k\bmod 9999) chart is identical (=297) for (k=120,720), yet actual `sin(99^k)` signs are rigorously opposite. Prior mod-101 witness and exact sign source owners reused.
- Crosswalked PR #1438 graph C3 orbit-sum and `Physics.WaveAlgorithmLift`: compatible, symmetrized graph structure is not a real signed circle-phase certificate. The terminal `k=9999!` sign remains open; existing naive pi-interval width obstruction remains method-specific. No ESD modification, no CI, Golden kernel pending.

## 2026-10-30 — Analytical j-invariant Bishop trigonometric phase to actual Pickover consumer

- Added `PickoverAnalyticJHistoricalPhaseConsumerExact.agda`, reusing original `JInvariantBishopTrigUnitPhaseExact`, `JInvariantBishopQFromUnitPhaseExact`, analytical j-fibre and non-descent owners rather than a new abstract phase ontology.
- Source-written exact equality `Im(bishopTrigPhase dataSet theta)=bishopSin dataSet theta`, consumer recovery from a retained three-time analytic phase and a separately required true-angle terminal producer certificate. No false identification of modular q/j finite values or their phase with the actual terminal sine. All three golden TOE roots import new owner; kernel pending, no ESD edit or CI.

## 2026-10-31 — rigorous large-precision Pickover sign controls

- Added `scripts/check_pickover_large_exponent_complex_phase_certificate.py`, independent dynamically scaled fixed-point complex powering with rigorous seed/rounding/product-error bounds. Locally executed equivalent implementation: signs (-,-,+,+,-,+) for k=(1,2,6,24,120,720), 1465 decimal precision and 7088 multiplications for the largest control. The 9999! terminal phase remains open and requires a source-specific compressed certified real-phase witness, not only a finite cyclic orbit. Original Bishop/Machin/Pickover authorship and attribution preserved. No ESD edits or CI.
