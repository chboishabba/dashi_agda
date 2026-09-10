# Changelog

## 2026-09-11 — Yang–Mills Path-13 elaboration profiling and RingSolver analysis

- Completed directional energy contraction profiling (`ym-path13-directional`)
  for `BalabanPath13DirectionalEnergyContractionExact.agda` with Exit 0 in
  261.8s, max residency 5.72 GB (down from OOM >32 GB), 425 metas, and max open
  constraints 2. Replaced 12 distinct-axis reflection solvers with the structural
  lemma `scaleSumSubtractCommutes` and `OpaqueAlgebra.scaleSubFactor`.
- Documented the two long-running Poincare-13 elaboration profiling jobs in
  `docs/ym_path13_elaboration_residency_records.md`:
  * Job 1 (2026-09-09 21:47 to 2026-09-10 10:45): ran for 12h 58m 20s before
    terminating on `path13LDLDecompositionRaw = ℚRing.solve-∀` in
    `BalabanPath13GeneratedLDLCertificate.agda`.
  * Job 2 (2026-09-10 11:30 to present): actively running at 20h 20m elapsed
    (20h 05m CPU time, 98.7% CPU, 1.71 GB RSS), having cleared all upstream
    averaging and martingale modules and currently progressing through the
    same 12-variable rational polynomial reflection step.
- Established that memory exhaustion (OOM) is completely eliminated across the
  entire upstream pipeline (held under 1.7 GB RSS), leaving single-core Horner
  polynomial reflection on 12 variables with large rational denominators as the
  sole CPU bottleneck.

## 2026-09-10 — NS literal outer signed-cross decomposition

- Added R590's deep-FL/complement decomposition on R545's literal spectator
  forcing half. Preserves its single resolvent factor and fixed spectator,
  avoiding an unsupported identification with R440's two weighted aggregates.
  Integrated the draft into R569; no analytic payment or Agda check claimed.

- Constructed the conditional R589→R588 producer and its common-cross bound.
  The exact scalar identity is now derived internally from literal masses;
  physical inequalities, quantity identification, and uniformity remain inputs.

- Extended R589 with actual dyadic deep/shoulder masks, complementary finite
  fold recombination, and the exact signed critical-cone decomposition. HH
  uses the minimum input shell conservatively. Physical estimates on these
  masks and Agda elaboration remain outstanding.

- Continued the fetched NS R588 checkpoint `6cd63dcd7` on the isolated branch
  `agent/ns-bidi-r588-continuation`.
- Added R589's literal R440 outer signed-cross decomposition using R581 finite
  routing and R291 additivity, retaining the full amplitude in each class.
  Integrated the draft into the focused R569 frontier.
- Static dependency and whitespace checks pass. No Agda was run. Physical
  uniform payments, R588's full weld, and Clay remain open.

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
