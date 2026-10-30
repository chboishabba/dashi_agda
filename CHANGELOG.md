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


## 2026-10-30 — OpenAI Math finite-supported Tseitin proof transport (PR #1212)

- Added `DASHI/Research/OpenAIMath/OpenAIMathFiniteSupportedTseitinModelsExact.agda` and routed it through the existing focused OpenAI Research `Everything.agda`. On original DAG/circuit owners it defines finite input and auxiliary vectors, canonical accepted-input encoding, exact per-coordinate round trips, and a reuse-only bridge to the original shared SAT formula. No new SAT compiler or arbitrary-tail uniqueness.
- Reused the pre-existing `PNotEqualsNPQ1TruthTableRepairGeneratorExact.vecExtensionality` instead of a second finite vector proof. Original PR #1040's executable circuit semantics and compiler ownership unchanged.
- An independently executed local finite enumeration passed 59,293 small circuit/output cases and a negative control for one-way auxiliary implications. Existing checked-in finite regression extended in place to include zero-gate circuit outputs and an exact 59,293-case assertion (commit `cb96df6e`); this amended script is source-written and has no exact-checkout execution receipt. Source-written Agda module, not kernel-checked; numeric cardinality, bounded-width bit encoding and ETH machine cost all remain explicit open gates.
- Updated both OpenAI Agda and Lean planning documents; tracked Jizhou Guo's October 29 **conditional**, externally owned sparse TSP/tensor-contraction follow-up, distinct from OpenAI Lean's fixed-width counting theorem. No ESD, Monster/Ibrahim ownership, or CI changes.


## 2026-10-30 — Numeric finite #SAT equality via existing concrete DAG evaluator

- Extended original `OpenAIMathFiniteSupportedTseitinModelsExact.agda` rather than creating another compiler or theorem owner. Added literal recursively computed Nat counts `countAcceptedCircuitInputs` and `countFiniteSupportedTseitin`, proven equal in **source-written** `finiteSupportedTseitinCountExact` using `sumExactlyOneEqualVector` and existing circuit gate evaluation. Added soundness/constructibility of the counted finite-model Boolean predicate via `equalBoolVectorsSound`, `finiteSupportedModelIsCounted`, `countedPairGivesFiniteSupportedModel`.
- Exact independent Python enumeration executed successfully for 59,293 finite circuits/output choices plus a non-parsimonious one-way-gate control. This is computational evidence, not an Agda kernel proof. Agda still lacks an exact-head compiler receipt; keep the new proof labelled source-written.
- Updated the Agda and Lean OpenAI roadmaps. Original #1040 compiler and Q1 vector proof owners, historical Cook/Tseitin, later OpenAI ETH and Max-Cut sources, and Ibrahim Monster 3B remain separately attributed. Next frontier is truly parsimonious bounded-width CNF and encoded machine time/space transfer; no theorem of P=NP or faster general TSP/Max-Cut has been added.
