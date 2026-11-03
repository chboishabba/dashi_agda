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


## 2026-11-03 — Karp-21 E20 canonical graph-word source refinements (PR #1445)

- Refactored `Karp21EncodedGraphSparseBitBoundExact.agda` to prove the original sparse `2m ≤ encoded graph word length` inequality using structural append bounds on the existing signed graph serializer.
- Added `Karp21ScaledCompleteGraphEndpointOrderExact.agda` and instantiated its `u < v < n` endpoint validity theorem on the original nonzero-total signed PARTITION graph.
- Added `Karp21UpperPairStructuralLexOrderExact.agda`, `Karp21ScaledCompleteGraphStrictLexExact.agda`, and `Karp21ScaledCompleteGraphStrictAfterExact.agda` to source-write strict global upper-triangle ordering and its reflection into the actual graph parser's `strictAfter` Boolean comparator; specialized the results to E20's source-generated scaled graph.
- Imported the modules in `Karp21Everything.agda` and updated the exact-lemma roadmap and attribution ledger. Python upper-pair recursion smoke checked n=0 through n=39; this is not an Agda check.
- **Not promoted:** the dependent `Fin.fromℕ<` graph reconstruction, original signed-weight threshold/same-object transport, concrete SAT/N21/E20 polynomial machine clocks, universal Cook–Levin, E01–E19 encoded reductions and 21 NP-membership results, and instantiated `CertifiedKarpNetwork` are still open. No Agda kernel acceptance occurred. Certified 0/20 reductions and 0/21 terminal NP-complete conclusions are unchanged.

## 2026-11-03 — Karp-21 E20 raw graph validator and gamma word field proof cut

- Source-wrote a pure `Fin.fromℕ<` reconstruction BIDI (`Karp21FinDecoderIndexBidiExact.agda`) that reuses original stdlib index injectivity and does not equate irrelevant off-diagonal proof functions.
- Added source-owned fieldwise weighted edge/list observations, exact signed cut-score preservation and Max-Cut YES transport (`Karp21DecodedWeightedCutSemanticBidiExact.agda`).
- Added raw graph validator success-soundness, canonical execution-order premises, and a source-written validator-completeness theorem on the actual signed scaled complete graph (`Karp21RawGraphValidatorObservationExact.agda`, `Karp21CanonicalRawValidatorPremisesExact.agda`, `Karp21CanonicalRawValidatorCompleteExact.agda`).
- Specialized `validateRawEdgesEncodedUpperPairs` and `e20EncodedUpperPairsRawParserAndValidator` to the original source-indexed signed PARTITION graph, preserving its exact cut score for any Boolean labeling.
- Added full original vertex-count, edge-count, raw signed edge-triplet and target-magnitude gamma field replay; proved actual original edge serialization has at least three gamma bits per edge for the parser guard and two per edge for the sparse witness guard (`Karp21OriginalGammaGraphWordFieldsReplayExact.agda`, `Karp21EncodedGraphSparseBitBoundExact.agda`).
- Source-wrote the positive nonzero signed integer threshold-to-gamma-successor bridge (`Karp21PositiveThresholdGammaExact.agda`). Imported all source owners into `Karp21Everything.agda`; updated exact-lemma roadmap and attribution.
- Added `scripts/referee_karp21_maxcut.sh` to fail closed without Agda and to print the pinned Git SHA and Agda version before checking the focused Golden Cook/gamma roots and the original E20/N21 graph-validation root. The script is committed, not an executed acceptance receipt.
- **Not kernel-accepted:** No local Agda compiler/checkout or CI receipt. The full `decodeGraphWord ∘ encodeGraphWord` same-object theorem, `scaledCompleteWordFaithful`, actual bit-machine clocks, universal Cook–Levin, E01–E19 and 21 NP memberships and `CertifiedKarpNetwork` remain OPEN. No reduction/NP-completeness promotion is claimed (0/20 and 0/21).


## 2026-11-03 — Karp N21 binary-native cost discipline and Agda stdlib repair

- Corrected the actual Agda stdlib `Data.List.Properties.length-++` call arity in `Karp21GammaBinaryGoldenCoreExact.agda` and `Karp21EncodedGraphSparseBitBoundExact.agda`: the suffix `ys` is implicit, not positional. Added `scripts/check_karp21_agda_stdlib_arity.py` to catch this class of source-only typechecking blocker deterministically.
- Added `scripts/check_karp21_e20_bitlength_bound.py` to check the exact original signed gamma E20 input/output word lengths and a conservative `16*(L+1)^3` target-bit envelope, including malformed-source fixed-NO and 1024–4096-bit signed weights. An independent BigInt model executed 19,535 finite signed-source size checks, all within the envelope. Not an Agda or machine-clock receipt.
- Added Golden candidate `Karp21BinaryFinMaterializationCostExact.agda`, proving the explicit inductive `Fin.fromℕ<` endpoint of address `u` carries `u+1` constructors. This isolates why gamma-encoded large vertex IDs must not be blindly materialised as unary `Fin` objects in a claimed polynomial bit-tape verifier. Runtime compiler optimisations remain a separate question.
- Added `scripts/karp21_binary_native_sparse_verifier.py` to consume the **original** gamma/zigzag weighted graph word and sparse `2m`-bit witness directly, with canonical sorted-edge validation, signed score, positive threshold, deterministic pairwise endpoint-consistency and no `Fin n` or full `n`-label vector. The successful full scan performs `m(m-1)` prior-assignment loop iterations and at most `2m(m-1)` integer address equality comparisons, independent of the value of `n`. The original word requires `3m+3 ≤ L`. Individual address comparisons' bit costs still require a checked tape implementation.
- Added `scripts/check_karp21_binary_native_sparse_verifier.py` same-word regression against the **existing** `verifies_sparse_word`, including malformed words, negative signed weights, repeated vertices and `n=2^1024`, `m=1`. An independent BigInt comparison model executed 198,701 finite sparse checks without mismatches; it did not execute the committed repository Python.
- Added `Karp21FinFreeRawSparseWordVerifierExact.agda` using original Agda gamma/raw-edge/order/Boolean/signed-integer owners, and the focused, intentionally non-Golden `Karp21BinaryRuntimeEverything.agda` import root. The original `Karp21Everything.agda` imports both. These are fin-free source implementations; their universal same-word equivalence to `N21.LiteralN21` and actual polynomial bit-machine clock are **OPEN**.
- Extended `scripts/referee_karp21_maxcut.sh preflight` with real Python codec/bitbound/binary-native regression and an Agda-arity preflight. Golden and E20 modes now explicitly check the new typed roots, fail closed without Agda and print revision/compiler provenance. No Agda kernel run or CI acceptance was obtained in this environment.
- Updated the canonical exact-lemma roadmap and authorship ledger. **No promotion** to `PR.InNP`, `PR.NPComplete`, the universal Cook–Levin root, 20 complete polynomial maps or `CertifiedKarpNetwork`: certificates still 0/20 costed reductions and 0/21 terminal NP-completeness conclusions.


## 2026-11-03 — Karp E20 typed raw graph acceptance and binary-native N21 scan counting (PR #1445)

- Reused the original `validateRawEdges`, `WeightedCutGraph` and `sameWeightedGraphsAccept` to source-write `scaledRawParsedGraphAcceptanceBidi` and `e20ScaledCanonicalRawGraphAcceptsIff`, preserving original signed thresholds and signed cut objectives rather than comparing `offDiagonal` proof functions.
- Corrected a source-visible Agda stdlib `length-++` implicit-argument error in the canonical complete-graph generator.
- Instrumented the existing Fin-free N21 endpoint history scan and source-wrote equivalence of its Boolean output and exact count of address equality checks. Proved a quadratic deterministic comparison-count bound `2*m*(m∸1)` by recurrence; finite Python arithmetic regression passed 10,001 input counts.
- Imported the new theorem owners into the Karp and binary-runtime roots, synchronized roadmap and attribution.
- **Not complete or kernel accepted:** full original gamma `decodeGraphWord`/encoder same-object transport, E20 image `scaledCompleteWordFaithful`, SAT/N21/E20 bit-machine clocks, universal Cook–Levin, E01–E19 + all 21 `InNP` instances and final `CertifiedKarpNetwork` remain unfilled. A comparison count is not a Turing machine clock; no Agda binary or CI acceptance receipt was available. Certified reductions and NP-completeness results remain 0/20 and 0/21.

