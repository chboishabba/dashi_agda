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


## 2026-10-30 — Reused Cook–Levin fixed-width CNF and source-numbered global gate placement

- Located and actually source-inspected pre-existing `FixedWidthTruthTableCNFExact`, `FixedWidthCNFToCookFormulaExact`, `CNFVariableRenamingExact`, `CNFPlacedConstraintConjunctionExact`, `CookLevinGridReplicationExact`, and original P-vs-NP numbered-gate compiler bounds. Unlike a whole-circuit truth-table CNF, these allow **constant-width local** gate constraints.
- Added `OpenAIMathSharedTseitinGateCNFExact.agda` to focused Research rollup. On original DAG gate constructors it imports the existing three-bit truth-table CNF constructor, original CNF renaming/placement soundness-completeness, and existing numbered gate variable bounds. It source-writes exact local/placed three-bit semantics and **four clauses per gate**, with a proved structural `renameCNFClauseCountExact` rather than assuming size preservation definitionally.
- Extended existing single finite regression with 40 local gate truth/CNF cases and 2,164 global placed-gate/CNF cases, including repeated wires and actual output/gate indices; independently executed equivalent Python exact checks passed. Source Agda and exact committed GitHub script remain kernel/checkout-execution pending respectively.
- New exact numeric `finiteSupportedTseitinCountExact` belongs to the existing OpenAI Research finite-model module and remains SOURCE-WRITTEN/KERNEL PENDING. Global placed `GateProgram` assembly, (n+g) variable count, (4g+1) total clause bound, numeric encoded-CNF parsimony, canonical binary input length, and primitive-machine costs remain separate proof obligations. Both Agda and Lean plans updated. No CI/ESD edits; historical Cook/Tseitin, original DASHI owners, OpenAI source, and Ibrahim Monster custody kept distinct.


## 2026-10-30 — Whole original Boolean DAG assembled as fixed-width placed CNF

- Continued reuse of original P-vs-NP DAG/numbered-gate owner, prior local fixed-width Cook–Levin CNF, original CNF variable renaming/conjunction/length proofs. `programPlacedCNF` now accumulates exact four-clause gate templates as new gate variables are appended, and `circuitPlacedCNF` adds a literal final output-unit clause on the original wire. Source-written `programPlacedCNFClauseCount` and `circuitPlacedCNFClauseCount` give **four clauses/gate and (4g+1) total clauses** in a finite `inputs+gates` carrier, not merely a complexity assertion. Corrected the append-length proof to cover original `Placed.append` specifically, not a different previously developed `Grid.append`.
- Independently executed Python regression PASSED **59,293 exhaustive full-program circuit-to-CNF model-count equalities**, including variable reference order, repeated wires and the literal (4g+1) clause count. Updated the existing GitHub test script in place to check this third count as part of its existing cases; exact-head GitHub script execution not performed.
- **Status distinction:** Agda declarations remain SOURCE-WRITTEN / KERNEL-PENDING. Whole-program CNF *syntax and clause-count* are source-proven, but whole-program CNF *semantic correctness and global parsimonious counting* have only executable finite checks, NOT a source-level Agda theorem. Actual canonical OpenAI Finset CNF encoding length and machine time/space also unpaid. Both Agda and Lean roadmaps synchronized; protected ESD, original Ibrahim Monster 3B custody and CI unchanged.


## 2026-10-30 — Whole-CNF exact gate-relation semantics and local Python Finset audits

- Reused existing P-vs-NP original DAG, numbered gate compiler, fixed-width truth-table CNF, placement/renaming, and prior global tableau CNF proof pattern. Extended **the already existing** `OpenAIMathSharedTseitinGateCNFExact.agda` with `ProgramPlacedGatesValid`, `programPlacedCNFSound/Complete`, `WholeCircuitPlacedMeaning`, and `wholeCircuitPlacedCNFSound/Complete`: source-written both directions between the actual recursively compiled global CNF and all placed original gate relations plus the true output wire. New source **not kernel-verified**. A further gate-bit-to-original `evaluateProgram` identification is still needed before global numeric #SAT source proof is paid.
- Strengthened the existing GitHub regression script in-place (commit `bb51f1450f1cce9b9e718cf32922cbe2177cca58`) to test the compiled CNF and original DAG semantics for **every finite assignment**, not just equality of aggregated counts. Independently executed local Python: **59,293 exhaustive source DAGs** plus **3,200 additional seeded source DAGs**, all corresponding finite assignments; **59,293** exhaustive Agda-list-vs-OpenAI-Finset semantic and actual unary/framed bit-length model cases; all PASS. The exact checked-out GitHub script and Agda kernel were not run in the container.
- Actual OpenAI `SAT.lean` and `Encoding.lean` show that a `CNF` is a **Finset of Finset literals**; converting from ordered Agda clauses can eliminate duplicates while preserving evaluations. Of 59,293 exhaustive fixtures, **45,932** had distinct ordered clauses which collapsed together only after literal-Finset conversion; **zero** had literally duplicate ordered source clauses. **53,326** had repeated literals and tautological opposite-polarity pairs in a source clause. The exact Agda (4g+1) **list** clause count is not the upstream Finset count; the deduplicated m obeys (m≤4g+1). The upstream width-three bit-bound is (L≤v+2+(4+(8v+8)·3)m), (v=inputs+gates); this is source-audited and computationally checked, **not a kernel-verified DASHI cross-system encoding theorem**.
- Also inspected newer **Agda #1438** actual `GraphColouring369PantsWeightedMaxCutExact`, `GraphColouring369PantsSymmetryCutInvariantExact`, `GraphColouring369PantsQidParetoSnowballExact`, and Lean #103. Those already own the native finite 27-vertex / 54-edge weighted bipartite cut and typed QID navigation (maximum cut Q942557, bipartite graph Q174733), distinct from the 27 ternary **endomorphism function** orbit and from unrestricted OpenAI Max-Cut hardness. Independent Python verified native graph connectivity, six S3 coordinate actions, 750 weight families and 150,000 competing cuts. Continued on original graph PR rather than duplicate the QID owner.
- Roadmaps in Agda/Lean and #1438 graph branch kept in step. Protected ESD untouched; no CI edits; classical mathematicians and original DASHI/Ibrahim Monster3B source ownership preserved.


## 2026-10-31 — Optional same-DAG reduced-clause CNF (source-written; kernel pending)

- Source-inspected existing P-vs-NP #1040 ConcreteBooleanCircuitDAGExact and the older #1212 four-clause/three-bit whole-program CNF before change. Added OPTIONAL OpenAIMathSharedTseitinOptimizedCNFExact.agda rather than replacing core owners. Standard Tseitin clause templates cost 1 constant / 2 NOT / 3 AND or OR, with exactly one additional output unit clause. Source-wrote 24 effective local Boolean cases, global recursive CNF assembly, pointwise equality with original whole-CNF evaluations, inherited whole-CNF soundness/completeness and an at-most 3g+1 source-List clause budget. New source is not yet imported through Everything because Agda kernel/stdlib verification is outstanding; no postulates/holes were intentionally used.
- Extended the original in-repo check_openai_shared_tseitin_parsimonious.py IN PLACE for optional semantic equivalence on every tested finite assignment, not just model counts. Independently executed Python PASS: 62,493 DAG/output fixtures, 3,135,224 assignments, 257,012 source ordered clauses saved across fixtures, zero semantic mismatches. Upstream unary-framed encoding length mirrored numerically: 49,838,961 bits original vs 29,634,737 optimized across fixtures, 20,204,224 bits saved. No universal bit-length/complexity theorem claimed; updated exact Github script not executed from checkout.
- Conditional upstream encoding bound on translated width-three Finset CNF with v=inputs+gates and m<=3g+1: L<=v+2+(24v+28)*(3g+1). A List-to-Finset semantic transport and upstream machine-cost composition are not kernel-paid. Previous finite-model numeric proof is not the global compiled CNF #SAT equality without further finite gate-value reification.
- Original #1438 27-grid/54-edge native weighted max-cut/QID and #1414 different 27-function C3 quotient inspected, not duplicated. Classical Cook/Levin/Tseitin, prior DASHI proof authors, independent OpenAI ETH family 378 and Ibrahim Monster3B attribution retained. No ESD/CI edit.

