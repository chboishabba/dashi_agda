# Karp 21 NP-completeness: full exact-lemma roadmap (2026-11-01)

**Authority:** DASHI Agda source is golden; `chboishabba/dashi_lean4` and `openai/math` supply independently attributed Lean donors.  
**Delivery PR:** [dashi_agda #1445](https://github.com/chboishabba/dashi_agda/pull/1445).  
**Scope:** all *21 historical problems*, all *20 historical direct reduction edges*, and the eight follow-up topics (some outside the 21).  
**Status principle:** code in a GitHub branch != Agda kernel-accepted theorem != source-paper result != same-object port. No general NP-completeness or P != NP is claimed by this roadmap.

## 2026-11-02 Leonid Levin (1973) search/decision proof-owner integration

**Original sources and attribution.** Stephen A. Cook's 1971 SAT theorem and concrete DASHI Cook–Levin tape/formula owners are separate from Leonid A. Levin's independent *Universal Sequential Search Problems*, *Problemy Peredachi Informatsii* 9(3) (1973), 115–116, English *Problems of Information Transmission* 9(3), 265–266, [Math-Net primary record ppi914](https://www.mathnet.ru/eng/ppi914). Richard Karp's 1972 historical 21-problem network is a third historical root. Michael Levin's biology corpus remains a fourth, unrelated owner. Repository searches for `Leonid`, `Levin 1973`, `Levin 1986`, `LevinSearch`, `LevinKt`, `universal search`, `Kt complexity`, and the linked P-v-NP PRs did not expose a distinct named executable Leonid Levin universal-search/Kt optimizer on the **default branch**; this does **not** establish absence on other historical branches or under different terms. The already existing Cook–Levin tableau and SAT language were confirmed and reused, not recreated.

**New source-written module, imported by `Karp21Everything.agda`:** `Karp21LeonidLevinSearchDecisionExact.agda` defines `StrictCookSearchWitness` on the *actual* `List Bool` strict-SAT encoding with an explicit parsed Cook AST and a satisfying assignment; `strictCookSearchDecisionIff` transports decision to search and back for every well-/malformed word. `concreteRunStrictCookSearchIff` composes this with the actual pre-existing concrete-tape exact-budget Cook–Levin accepting-run equivalence on the same serialized word. `n21SameGraphSearchDecisionIff` reuses N21's **actual signed sparse 2m-bit endpoint certificate and consistency** equivalence, not a new graph verifier. The proofs preserve source machine/input/budget or source signed graph, respectively.

**Remaining specific Levin/K00 cut:** `k00FiniteCookAssignmentCodec` (replace the unbounded `Nat → Bool` assignment witness with actual finitely bounded, same-AST satisfiability and encoded bits); `k00FiniteWitnessParseAndLength`; `k00StrictSATMachineVerifierClock`; `k00UniformConcreteTapeToSATWordPolynomialClock`; `k00AllNPMachineLanguagesToSATWord`; `k00StrictSATInNP`; `k00LevinSearchRelationCostedTransport`; optional **separate** `leonidLevinUniversalSearchSchedule`, `leonidLevinKtOptimality` only if a genuine target/solver is specified and mechanically costed. N21 still needs `n21GraphWordParserExact`, `n21GraphWordEdgeCountBitBound`, `n21SparseVerifierBitTapePolynomialClock`, `n21InNP`. None is paid by the new search/decision equivalence.

**Verification:** source committed; neither pinned Agda kernel, CI, nor exact-branch checker was run. This is not a proven NP-complete root or universal optimal-search algorithm; the complete-costed reduction count stays 0/20 and the new end-to-end NP-complete theorem count stays 0/21.

## 2026-11-02 explicit repo-wide K00/VOA/codec archaeology and actual SAT Word completion

**Search performed before writing new Agda:** `Karp21`, `CookLevin`, `K00`, `FiniteWordSize`, `PolynomialCostModel`, `binary codec`, `zigzag`, `gammaCode`, `bitLength`, `encodedSize`, `NP membership`, `PolynomialTimeVerifier`, `TuringMachine`, `VOA`, `Monster3B`, `gradedTrace`, `GradeAction`, `FockPartition`, `C3Fourier`, `SignedLaplacian`, `PNFSignedResidualDelta0`, `Cheeger`, `MaxCut`, `representation action`, `same-object`, `FiniteConfigurationEncoding`, `ConcreteTape`, `CostRefinement`, `CookFormulaBinaryCodec`, `Data.Nat.Binary`, `binaryDigits`, `natToBits`, `bitsToNat`, `encodeSignedBits`, `BinaryNat`, `Elias gamma`, `prefix-free`, and `self-delimiting`. This is explicit source archaeology across **existing `dashi_agda` default branch** plus PR #1445, not a claim of having kernel-checked every match. No extra repo was modified.

### Precise pre-existing K00 owners — stronger than the old roadmap's loose “Cook–Levin OPEN”

- `ConcreteTapeCookLevinExactBudgetIff.agda`: **actual** `GuardedCookLevinSAT` iff `ExactBudgetAcceptingRun` for a source-specified concrete tape machine, input and exact budget; this is more than an abstract SAT iff field.
- `ConcreteTapeCookLevinCookFormulaExact.agda`: **actual** `guardedCookFormula`, `cookSatisfiableToExactBudgetRun`, `exactBudgetRunToCookSatisfiable` on the source-owned `CookLevinCircuitGCTBoundary.BooleanFormula`. The single-machine concrete tableau→Cook formula semantics is already source-written, and must not be rebuilt or reported as wholly missing.
- `ConcreteTapeCookLevinPrizeFacingExact.agda`: `prizeFacingCookLevinCertificate` compiles exact-budget SAT/run semantics, variable count and closed clause bound. `PNotEqualsNPConcreteTapeProgramCookLevinSameObjectWeldExact.agda` connects literal static-machine program code with the same exact tableau owner.
- `ConcreteTapeStandardClockExact.agda`: projected concrete→conventional machine step clock equality and first-match dispatch work `≤ steps × ruleCount`, subject to existing model/compatibility preconditions; this is NOT a bound for the separate full Cook formula serialization. `PNotEqualsNPExecutablePolynomialCostRefinementExact.agda` supplies executable code witnesses on top of the abstract `PolynomialCostModel`, but explicitly withholds extraction from arbitrary extensional complexity predicates.
- `PNotEqualsNPCookFormulaPrefixCodecExact.agda`: actual suffix-preserving Cook syntax parser and prefix AST roundtrip; `PNotEqualsNPCookFormulaBinaryCodecExact.agda`: eight tokens serialized in **exactly 3 bits**, formula roundtrip and bitcount `3 × tokenCount`. **Existing decoder permissiveness:** `decodeTokenStream` silently drops dangling 1/2 bits, and `decodeCookFormula` returns a default on malformed syntax. These are unsound policies for claiming canonical all-word SAT decision without a separately defined strict language.

### New precise K00 source-written results in this PR (imported by `Karp21Everything.agda`)

1. **`Karp21CookStrictTripleBitBoundaryExact.agda`:** total `strictDecodeThreeTokens` returns `Maybe (List CookSyntaxToken)`, never drops malformed tails. `strictDecodeThreeTokensAfterEncode` proves its exact roundtrip for all eight actual Cook syntax tokens; `strictRejectOneExtraBit` and `strictRejectTwoExtraBits` reject trailing 1/2 bits. `strictDecodeCookFormulaBits` calls the **source owner's real `Prefix.parseCookFormula`**, requiring the suffix to be `[]`; `strictCookFormulaRoundTrip` proves exact AST decode-after-encode. `strictRejectTrailingCompleteFormulaToken` rejects a complete valid extra formula token; `strictRejectStandaloneNatZero` rejects a nonformula top-level integer token. Hence malformed *complete three-bit-token* formulas are distinguished from correct SAT words, not silently decoded as false.
2. **`Karp21CookStrictSATLanguageExact.agda`:** `strictSATLanguage : PR.Language Word.BitWord` is an **actual total binary SAT language**. `strictSATFormulaWordIff` transports `Cook.Satisfiable formula` iff strict word acceptance for every original Cook AST; `strictSATRejectsOneTrailingBit`, `strictSATRejectsTwoTrailingBits`, `strictSATRejectsCompleteExtraToken` discharge actual malformed-word *language nonmembership*. This is source-written proof-term construction, not an unimplemented parser interface.
3. **`Karp21CookLevinConcreteBitWordReuseExact.agda`:** `guardedCookLevinBitWord` serializes the **actual existing** concrete-tape Cook formula on `FiniteWordSizeExact.BitWord = List Bool`; `guardedBitWordDecodesToActualCookFormula`, `strictSerializedCookWordParsesExactFormula`, `strictCookSATWordAcceptanceToRun` and `exactRunToStrictCookSATWordAcceptance` now prove the concrete-tape accepting-run equivalence directly on the **same actual strict `PR.Language`**, not a guessed SAT language. `wordLengthMatchesCookCodecLength` identifies the two inherited list-length functions before `serializedCookFormulaWordLength` proves exact source-size `3 × cookFormulaTokenCount`. Exact source machine/input/budget and both directions are preserved. The further `nonemptyInputBelowActualSATWordSize` **reuses** the already source-written `ConcreteTapeCookLevinQuotationGrowthExact.nonemptyPayloadStrictlyBelowCookFormulaBitCode` and transports its strict input-payload-size lower bound to the *same* `FiniteWordSizeExact.encodingSize`; it is neither a global output upper bound nor a polynomial-time clock.

**What K00 *still* requires to be a genuine NP-complete SAT theorem:** every NP verifier in the selected concrete machine model → a uniformly generated machine/tableau family with an explicit polynomial clock *in the bit length of the original input and certificate*; uniform source-word→target-word real executable algorithm and its polynomial bit-cost proof (not just token-count equality or the bounded `steps × |rules|` dispatcher); compatible invalid-source policies; universal all-NP-language many-one reduction on one `Word` model; a paid `PR.InNP` instance for the strict SAT language; and pinned kernel receipts. Existing exact-budget correctness for **one machine + one budget** is mathematically substantive but does NOT quantify these obligations away. No `PR.NPComplete` inhabitant is claimed.

**Remaining 20 historical direct edges and 21 NP members are retained below**, including E20/N21 gamma/zigzag signed graph Word encoding and real runtime cost, E04/E05/E06/E12 finite semantics, and E01–E19 machine reductions. Existing Monster/VOA/PNF/SSP, character, eigenspace and finite sampling work cannot stand in for any of the above universal complexity statements. No CI or Agda kernel run.


### Common K00/N21 canonical Word size — no second binary carrier

`Karp21MaxCutCertificateBinaryCodecExact.agda` now additionally imports the **same** `FiniteWordSizeExact` used by the strict K00 language. `canonicalWordLengthMatchesListLength` proves the two source-owned length functions coincide for all `List Bool` words; `cutCertificateCanonicalBitWordLength` then proves `FiniteWordSizeExact.encodingSize (encodeCutLabels bits) ≡ n` on every actual `Vec Bool n` MAX CUT witness. This pays the N21 **exact certificate bit length on the canonical K00 metric**. It does **not** establish `n ≤ encodingSize graphWord` until a faithful target graph-word codec supplies the vertex-count bound, nor a time complexity theorem for graph parsing and signed summation. No user instruction to skip CI is treated as permission to promote uncompiled sources.

## 2026-11-02 Michael Levin corpus audit, real Cook prefix-free proof and signed Max-Cut observer/action weld

**Source audit and name disambiguation.** The repository contains **at least 68** `DASHI/Biology/Levin/` Agda files in [PR #99](https://github.com/chboishabba/dashi_agda/pull/99), and **15 additional** Levin/Everything-related changed files in [PR #132](https://github.com/chboishabba/dashi_agda/pull/132). The older Michael Levin programme is substantially larger than the previously inspected `PrefixFreeCodingBoundary`. Source-identified related later lanes include [#669](https://github.com/chboishabba/dashi_agda/pull/669) (observer-intervention/embodied-agent trust), [#548](https://github.com/chboishabba/dashi_agda/pull/548) (physical developmental goals, invariant future compression and cost), and [#584](https://github.com/chboishabba/dashi_agda/pull/584) (refinement/observation dynamics). The default-branch code search explicitly covered `Levin`, `LevinSearch`, `UniversalSearch`, `LevinKt`, `LevinK`, and `CookLevin`. No source-supported Leonid Levin `Kt` or universal-search solver was found under the literal named-search terms. **Michael Levin** (developmental biology, problem spaces, cellular agency) is not **Leonid Levin** (complexity, universal search), nor is the shared surname evidence of a formal mathematical equivalence. Cook–Levin is a different, historical SAT theorem and is not Michael Levin's work.

**Existing in-repo source owners read before implementation:**

- `DASHI/Biology/Levin/PatternMemoryCore.agda`: present morphology, electrical carrier, decoded target and triggered repair are different types; successful observable phenotype is not uniquely the latent goal/control mechanism.
- `HierarchicalGoalMemory.agda`, `CompetentGoalExecution.agda`, `ProblemSpaceAgency.agda`: hierarchical targets, accepted commands, distinct lower-level policies, task-indexed goal success; navigation/competence does not prove global algorithmic optimisation.
- `ObserverRelativePolycomputation.agda`, `SubstrateConstrainedComputation.agda`, `PolycomputationBiologyAdapter.agda`, `FungalPolycomputationAdapter.agda`: observer-selected encoding and an abstract input-output relation do not specify a unique physical mechanism, substrate runtime, thermodynamics or complete microtrajectory.
- `PrefixFreeCodingBoundary.agda`, `CompressionIntelligenceBoundaryCore.agda`, `PredictionCompressionEquivalence.agda`, `ContextualEntropyRateBoundary.agda`, `ShannonInformationEntropyBoundary.agda`: **their status fields are Bool**, not actual Agda witnesses of Kraft inequalities, optimal prefix-free compression, a probability model, literal tape execution or bounded computation. Decoder cost must be charged; length alone does not give polynomial machine time.
- `EffortOutcomeAccounting.agda` and `LevinDiverseIntelligenceSurface.agda`: task success, model-relative compression, agency and unexplained outcomes require distinct source/intervention/evaluation receipts. No biological or compression performance claim automatically proves NP membership or a machine-cost polynomial.

**New source-written, imported Agda proofs in PR #1445:**

1. `Karp21MichaelLevinGoalExecutionWitnessExact.agda`: instantiate the **existing** `Levin.GoalExecutionSystem` and real `GoalUnderdeterminesTrajectoryWitness`/`CompetentExecutionWitness` types on **one actual signed `Cut.WeightedCutGraph (suc n)`**. The two concrete policies are identity and global label complement (already proved cut-invariant by `Karp21SignedLaplacianCutExact`). Given an **actual accepted Bool cut witness** (not an unproved solver), construct both successes, with policy distinction `samePolicy false true ≡ false` and `distinctRealisedCutWitnesses`: for every nonempty `Vec Bool (suc n)`, the flipped literal certificate is genuinely different. This formalises *goal success underdetermines policy and witness*, NOT a biological solver for Karp.
2. `Karp21MichaelLevinObserverCutQuotientBoundaryExact.agda`: exact finite same-graph counterexample showing **global complement C2 preserves signed Karp cut score**, yet the actual first-vertex label observation changes. `sameDecisionObservableDoesNotRecoverLiteralPolicy` makes it impossible to promote the C2 quotient to a lossless observer for all provenance/policy observations. Reuse existing `ObserverRelativePolycomputation`/substrate/problem-space conceptual owners; it is not an empirical biological result.
3. `Karp21LevinPrefixFreeCookCodingExact.agda`: imports the original Michael Levin directory coding boundary **as provenance**, but supplies real proof terms instead of its `Bool` fields. It reuses the original `PNotEqualsNPCookFormulaPrefixCodecExact.parseCookFormulaEncodeInto` and strict three-bit decoder. `cookPrefixSuffixMustBeEmpty` proves a completed `Cook.BooleanFormula` prefix cannot absorb an additional AST-token suffix and equal another completed formula; `cookCompleteTokenBinarySuffixMustBeEmpty` proves the same property for the **actual source-owned 3-bit token code**. `cookCompleteTokenPrefixWitness` packages that proof (not a `prefixFreeWitness = true` flag). This covers complete-token suffixes; malformed 1/2-bit tails are already rejected by `Karp21CookStrictTripleBitBoundaryExact`, and a fully general bitwise prefix theorem, Kraft bound or optimal code theorem is **not** claimed.

**Same-object correspondence and mathematical non-promotion:**

- The symmetry and goal bridge are **exact for the real Karp finite signed graph**, with a supplied accepted witness. They **cannot** compute that witness polynomially, prove P=NP, reduce other Karp problems, or show that a biological system physically executes this algorithm. No bound on the physical transition/energy resources can be derived from success observations.
- `PrefixFreeCodingBoundary` is a *coding status record*. Its existing `prefixFreeWitness : Bool` and `CodingOptimalityBoundary` do not imply actual prefix-free Boolean languages, a Kraft–McMillan theorem or Shannon optimality; the new prefix proof does, however, discharge a precise complete-token restriction for the actual Cook source encoding. Keep Michael Levin biological attribution apart from Kraft/McMillan/Shannon coding theory and Cook's SAT code.
- The original `Karp21VOAZ2CutOrbitExact` remains a **search-witness quotient**. Its cut score remains exact; `sameDecisionObservableDoesNotRecoverLiteralPolicy` proves that retaining only that quotient is not an all-observer-recoverable full proof/PNF/provenance record.

**Unpaid exact lemma cut after this reuse (not forgotten):** `k00CookFullBitPrefixFree` beyond complete-token aligned suffixes; `k00StrictSATInNP` on genuine machine-verifier clock and binary witness bound; `k00UniformConcreteTapeToSATWordPolynomialClock` and universal all-NP source transport; `e20SignedIntegerGammaAndZigzagAgdaRoundtrip`, `e20GraphWordRoundtrip`, `e20GraphMalformedPolicy`, `e20PolynomialTapeTransducer`; `n21GraphWordParser`, `n21SignedAddBitClock`, `n21PolynomialVerifier`, `n21InNP`; all **E01–E19** machine-costed encoded maps, **N01–N20** NP membership proofs and 21-node complete DAG. Actual new Agda checks and same-revision kernel receipts are still absent; CI intentionally not run. No mutation in Biology/Levin, ITIR, SLR or SensibLaw.

## 2026-11-02 N21 critical sparse-graph binary-size correction (highest priority after Levin source audit)

**New exact counterexample to the old N21 NP-size argument:** The Python canonical graph word encodes the `vertices` count `n` by `gamma(n+1)`, using only `O(log(n+1))` bits. Thus there are valid *sparse graphs* with a single edge and `n=2^k` whose whole graph word uses `O(k)` bits, but the old exact `Vec Bool n` bit certificate uses `n=2^k` bits. The original `Karp21MaxCutCertificateBinaryCodecExact.cutCertificateCanonicalBitWordLength` is a correct **exact-n-bit identity**, **not** a polynomial witness bound in input length for the entire canonical signed weighted graph language. Do not promote it to `PR.InNP`. The graph representation, not the mathematics of Max-Cut, caused this debt.

**Correct strategy:** For `m` actual signed edges, encode two Boolean labels per *edge-endpoint occurrence*, length exactly **`2m` bits** even when the graph has exponentially many isolated declared vertices. Require repeated uses of any `Fin n` vertex to carry identical labels. Every globally labelled cut projects to one consistent local certificate. Conversely any consistent assignment of labels to the vertices that occur in edges extends to a global cut by assigning arbitrary defaults to isolated vertices; the signed edge contribution and positive threshold are unaffected. A canonical graph word serializes each of its `m` edge triples with at least three bits, hence `2m ≤ graphWordLength` under the Python grammar. This is the *correct polynomial-size existential witness route*; the converse extension theorem and machine-time proof must be formalised in Agda before claiming `InNP`.

**Implemented in DASHI PR #1445:**

1. `DASHI/Mathematics/Complexity/Karp21SparseEndpointCutCertificateExact.agda` adds a dependent `EdgeBits edges` carrier, `encodeSparseEdgeBits` / `decodeSparseEdgeBits` with exact roundtrip and `sparseRejectTrailingBit`; `twoPerEdge` and `sparseWordBitCount` prove a literal 2-bits-per-edge list-word size, completely independent of vertex-count `n`. `projectEdgeBits` translates the original `Vec Bool n` cut into the local endpoint bits. `edgeBitsCutMatchesContribution`, `projectedEdgeScoreEqualsOriginal`, `projectedSparseVerifierExactlyEqualsFull`, and `fullAcceptedWitnessHasSparseWitness` prove the actual signed weighted score and computed threshold verdict are unchanged by projection.
2. The same Agda source now contains the *real finite consistency-checking algorithm* `endpointObservations`, `observationsCompatible` using `Data.Fin.Properties._≟_`, `oneAgainstAll`, `allEndpointOccurrencesConsistent`, `verifyConsistentSparseCut`, and the full malformed-fail-closed `verifySparseCutBitWord`. `projectedObservationsAreActualVertexLookups`, `allActualVertexObservationsConsistent` and `projectedSparseCertificateAlwaysConsistent` show every globally encoded witness passes the actual repeated-vertex consistency test. `projectedConsistentSparseVerifierEqualsOriginal` / `projectedSparseBitWordVerifierEqualsOriginal` strengthen completeness to the **whole executable checker**, not a score-only surrogate. All are source-written; pinned Agda acceptance is still open.
3. `scripts/karp21_signed_cut_binary_codec.py` implements `sparse_certificate_from_labels`, `sparse_cut_certificate_verifier`, and `verifies_sparse_word`, with an `O(m)`-entry map of encountered vertex IDs, no allocation proportional to `n`, signed edge contributions, repeated-vertex conflict rejection, and a 2m-bit certificate. It preserves the original full-length verifier only as a compatibility/reference path; the **sparse** verifier is the proper NP witness representation for this binary graph grammar.
4. `scripts/check_karp_binary_codec.py` adds reference tests comparing the sparse and full verifier on all previously enumerated E20 cases, a graph with one edge and `n=2^1024`, signed weights, contradictory repeated-vertex label bits, exact 2m witness lengths and `2m≤encodedGraphBits`. These tests are **source-written but not run**, per the no-CI instruction; no observed pass counts are fabricated.

**Strict remaining N21 max-cut:** `n21SparseConsistencyImpliesFullCutExtension` and `n21SparseWordAcceptsIffGraphYES` are now source-written in `Karp21SparseEndpointConsistencySoundExact` and require Agda acceptance; independently unpaid `n21GraphWordParserExact` + positive-threshold/edge uniqueness/canonical signed-gamma bitstring correspondence with the executable Python reader; `n21GraphWordEdgeCountBitBound` (universally prove `2m≤wordLength` against that exact grammar); `n21PairwiseConsistencyPolynomialClock` and `n21SignedAdditionMachinePolynomialClock`; `n21InNP`; kernel receipt. For K00, E20 and other 19 edges/20 NP memberships see the complete lists below. **Not certified; 0/21 complete**. The original signed Laplacian/PSD and Michael Levin observer/action bridges are unaffected.

### Subsequent exact N21 finite semantic closure (same source branch, still kernel-unrun)

`Karp21SparseEndpointConsistencySoundExact.agda` is a further **source-written proof** (imported by `Karp21Everything.agda`) that now implements the formerly-open *finite converse*: `checkedObservationsHaveUniqueVertexLabels` extracts actual agreement from the `allEndpointOccurrencesConsistent` Bool checker, `firstObservedLabelAgreesWithEveryOccurrence` proves the first-occurrence readout is consistent with all endpoints, `vectorFromVertexFunction` creates a mathematical full assignment with arbitrary false defaults for isolated vertices, and `projectionMatchesEveryLocalOccurrence` proves that projecting this global vector **reconstructs the entire original EdgeBits**, not only its score. `extendConsistentSparseToFullLabels` returns the fully typed reconstructed global cut witness and certificate equality.

`sparseAcceptedLocalImpliesFullGraphYES` and `sparseAcceptedBitWordImpliesFullGraphYES` prove soundness of the **actual repeated-endpoint consistency and signed-threshold Boolean verifier**, including malformed no-certificate rejection; `fullGraphYieldsSparseAcceptedBitWord` proves completeness from each accepted `Vec Bool n` witness; `n21SparseBitWordDecisionIff` combines both arrows into `PR.Iff (Cut.WeightedMaxCutYES graph) (SparseBitWordYES graph)` on the exact same `Cut.WeightedCutGraph n` object, for all finite `n`, all signed weights and all edge lists. No nonnegative/PSD assumption or hidden biological solver.

**Updated residual after this stronger source-written result:** the finite semantic `n21SparseConsistencyImpliesFullCutExtension` / `n21SparseWordAcceptsIffGraphYES` are **source-written**, not kernel-checked. Remaining to construct and certify: `n21GraphWordParserExact`, `n21GraphWordEdgeCountBitBound`, `n21SparseVerifierBitTapePolynomialClock`, `n21InNP`, and pinned Agda kernel acceptance. The mathematical full `Vec Bool n` reconstruction is a *proof witness only*; the executable sparse verifier still uses only `2m` label bits and pairwise checks over at most `2m` observed endpoints. **No machine-cost conclusion follows from the proof reconstruction.**

## O/R/C/S/L/P/G/F: objective and contracts

- **O — Objective:** one typed executable, bounded and independently auditable reduction network preserving Karp (1972) problem definitions. Exactly one DAG owner per distinct mathematical proposition.
- **R — Prior art:** Cook (1971), DOI `10.1145/800157.805047`; Karp (1972), DOI `10.1007/978-1-4684-2001-2_9`; Zuckerman (1996), DOI `10.1137/S0097539794266407` (non-standard constrained approximation variants); Ford and Fulkerson (1956) and Edmonds and Karp (1972) (separate max-flow line); Goemans and Williamson (1995) (separate MAX CUT approximation). Original priority is not reassigned to DASHI or OpenAI.
- **C — Code:** reuse `DASHI.Mathematics.Complexity.PolynomialReductionExact`, `CookLevinCircuitGCTBoundary`, `PNotEqualsNPClayCoreExact`, and `Karp21ReductionTransportExact`. New graph semantics in #1445 are not a substitute for finite, size-bounded reductions.
- **S — Safety/claims:** keep historical decision, optimization, approximation, integer/signed weights, nonnegative capacities, and scheduling variants distinct. Boolean proof-of-status flags, search hits and finite numerical regressions never close a theorem.
- **L — Lemmas:** names below are *required exact target declarations*, NOT currently proved symbols unless explicitly named in the status inventory.
- **P — Preconditions:** finite bitstrings with a canonical parser/serializer, explicit input length, well-formedness/invalid-input policy, polynomial clock, and bounded witnesses. All reductions must handle rejected/ill-formed encodings in a specified manner.
- **G — Gates:** independent mathematical proof term, syntactic check in focused Agda root, actual pinned-toolchain check, axioms/postulates/hole audit, executable regression as secondary evidence, consumer parity, exact source commit attribution.
- **F — Follow-through:** after each edge, add the checked reduction to a *single* 21-node graph and propagate completeness using the existing `transportNPComplete` rather than creating 21 copied proofs.

## 2026-11-02 max-cut continuation — K00 malformed words, E04/E06 finite semantics, E20 pair coverage, N21 bitword certificate

**Repo boundary:** all implementation stays in `chboishabba/dashi_agda`, PR #1445. Original Cook (1971)/Karp (1972), inherited repository proof owners and subsequent DASHI proof sources retain separate attribution. No CI or Agda kernel run was performed in this tranche.

### New source-written Agda exact lemmas

| Owner | Source-written exact theorem / contribution | Residual before verified reduction |
| --- | --- | --- |
| `Karp21MaxCutCertificateBinaryCodecExact.agda` | `decodeEncodeCutLabels` gives exact `Vec Bool n` → `List Bool` → `Vec Bool n` roundtrip; `cutCertificateWordLength` is exactly `n`; `rejectTrailingCertificateBit` rejects extra data; `wordAcceptanceSound`, `wordAcceptanceComplete`, `n21PackedCertificateYESIff` prove the full existential finite MAX CUT bitword-certificate correspondence. | Graph Word decoder; quantified packed graph/cert parser correctness; actual bit-verifier machine polynomial clock, `PR.InNP`, kernel receipt |
| `Karp21IndexedUpperPairBijectionExact.agda` | `upperPairNoLoop`, `upperPairEndpointsInjective`, `upperPairCoversDistinct`, `allUpperPairsContains`, `enumeratedUpperPairCoversDistinct`: a canonical `UpperPair n` address covers every distinct vertex pair (either orientation), and its ordered endpoints identify it injectively. The enumerator includes each address as a **membership witness**. | Both address-occurrence no-repeat and the exact weighted edge-list projection are now source-written in `Karp21IndexedUpperPairBijectionExact` / `Karp21UpperPairGraphEnumerationExact`. Pinned Agda check and canonical binary Word encoding still remain |
| `Karp21FiniteCliquePackingDecisionExact.agda` (historical E04) | Reuses original `Karp21CliqueSetPackingExact`, same `SimpleGraph n` and `Vec Bool n` cardinality; `karpFiniteCliquePackingInstanceIff` establishes existential finite CLIQUE YES iff nonedge-incidence SET PACKING YES, all k. | Canonical explicit set-family universe/payload, source/target packed Word codecs, polynomial transform machine clock, concrete NP membership for the graph/set owner and Agda acceptance |
| `Karp21FiniteNodeSetCoverDecisionExact.agda` (historical E06) | Reuses `Karp21VertexSetCoverIncidenceExact` and finite graph/Boolean choice; `karpFiniteNodeSetCoverInstanceIff` gives existential node-cover iff indexed-edge set-cover with budget `countChosen ≤ k`. | Actual finite edge-universe and incidence set-family bit matrix, direct source/target Word parser/serializer and size proof, polynomial graph→family machine clock, NP certificate and Agda receipt |
| `Karp21MalformedWordTotalReductionExact.agda` (shared K00) | `TotalMalformedSource.totalMalformedReductionIff`: a **total** `Word → Word` reduction handles malformed source words by mapping them to a target NO object with a real proof of NO; valid source words use the actual instance-iff and independent target-encoding faithfulness. `makeCostedTotalReduction` creates the existing `PR.PolynomialManyOneReduction` when and **only** when a real `polynomialTimeMap` certificate for this map is supplied. | Concrete signed source/graph codecs in Agda and the actual polynomial machine clock; no resource certificate is manufactured |

**Agda source repair:** `Karp21FiniteCompleteGraphGeneratorExact.agda` incorrectly omitted Nat `_+_` from its import list while defining `triangularPairCount`. The import has been repaired. This is a static source fix, not evidence of pinned Agda acceptance.

### Concrete executable binary Karp E20/N21 adapter

`scripts/karp21_signed_cut_binary_codec.py` is an **actual** separate Python binary encoding/transducer implementation, not a generic codec record. It emits canonical, self-delimiting `gamma(n+1)` natural numbers with zigzag signed integers, source partition vectors, sorted off-diagonal unique undirected weighted edges, and a strictly positive MAX CUT threshold. An invalid source word maps to the valid fixed-NO graph (two vertices; one unit edge; W=2); a signed zero-sum source maps to a valid fixed-YES graph (same unit edge; W=1). Arbitrarily signed nonzero inputs use edges `w_uv=4*c_u*c_v` and `W=(Σ c)²`.

The target decoder rejects nonbinary words, truncated gamma tokens, out-of-range/reversed/looped/duplicated/unsorted edges, zero threshold and trailing data; the cut certificate must have exactly `n` bits. This satisfies the executable *reference semantics* for malformed input and the same finite graph decision predicate; **the same-object Agda `Word` codec/clock remains unproved**.

`scripts/check_karp_binary_codec.py` now contains exhaustive small-word roundtrip and YES/NO controls for **3906** signed source vectors of length 0..5, **111111** cut labelings, malformed words, exact reconstruction, positive/zero threshold branches, and **54** signed 1024-bit envelope scenarios; it is added to `run_karp21_reduction_regressions.py`. **The exact script has not been executed in this turn.** These are test cases authored, not test results or formal bit-complexity bounds. The observed heuristic envelope `outputLength ≤ 128*(inputLength+1)^3` on finite fixtures must not be promoted to a universally proven machine-time theorem.

### Remaining unclosed mathematical cut, ordered by reuse

1. **K00:** actual `Word=List Bool` decoding/encoding proof for signed integer vectors and canonical weighted graph, malformed source/target policies as language predicates, `PR.PolynomialCostModel` instantiated with an audited bit-operation/tape model, Cook–Levin SAT `NPComplete` for the **same** `Word`, and certified composition for all 20 direct reductions.
2. **E20:** source-written `e20UpperPairOccurrenceUniqueness` (`allUpperPairsNoRepeat`) and `e20UpperPairToCompletePairEdges` (`actualKarpGraphCanonicalUpperPairs`) require pinned Agda acceptance; still unpaid `e20AgdaSignedGammaCodecRoundtrip`; `e20AgdaGraphWordRoundtrip` and `e20GraphDecodeRejectsMalformed`; `e20IntMulBinaryBitCost`; `e20ConcreteTapeTransducerPolynomialClock`; `e20EncodedPolynomialReduction`. Signed finite cut objective and full finite positive-target YES iff are source-written already, not kernel accepted.
3. **N21:** the new exact `n`-bit cut certificate codec must be paired with the graph's binary Word and verified worst-case integer summation/multiplication clock to produce the actual `PR.InNP`, not merely an existential finite verifier.
4. **E04/E05/E06/E12 graph/set triangle:** retain the now-source-written finite existential iff; construct real packed set-universe/graph codecs, k-bound guards, polynomial clocks, and `PR.InNP` witnesses for each decision problem.
5. **Other E01–E03, E07–E11, E13–E19 and N01–N20** remain *exactly* as separately listed below (20 reductions and 21 membership problems overall). No edge is marked costed from bounded Python controls, a semantic iff, or a typed source record.
6. **Independent acceptance:** run pinned Agda source/axiom/termination check of `Karp21Everything.agda`, then source revision, exact statement and dependency SHA receipts. No CI was required or run in this tranche.

**Status still 0/20 new end-to-end Agda kernel-certified costed concrete reductions; 0/21 new concrete Agda kernel-certified NP-complete problem proofs.** This does not diminish the finite source-written theorem additions, but it prevents a false "all done" promotion.

### 2026-11-02 second Pareto pass: actual upper-pair list occurrence uniqueness + weighted graph identity

New source-written `Karp21IndexedUpperPairBijectionExact.allUpperPairsNoRepeat` (also `upperTriangleOccurrenceUnique`) now proves the actual upper-triangle address **list has no repeated occurrences**, not merely an injective address-to-endpoint function. It constructs a genuine list-membership reflection argument for recursive `Fin.suc`, `headTail` and `tailPair`, their disjoint head/tail images, and a generic `noRepeatAppendSeparated` induction. This completes the abstract upper-pair uniqueness proof obligation at the source level.

New source-written `Karp21UpperPairGraphEnumerationExact.agda` **connects those canonical addresses to the original generated edge list**, rather than leaving two unrelated representations. `headLinksAreCanonical` proves that the generator's head-edge weights are exactly `x * Vec.lookup tail j` for every index; `headPairsAreCanonical` proves the finite head-edge list corresponds to the canonical list; `completeGraphMatchesUpperPairEnumeration` and `actualKarpGraphCanonicalUpperPairs` inductively identify the *actual* `Gen.completePairEdges source` with `map (edgeAtUpperPair source) (Pair.allUpperPairs n)`. The edge projection preserves orientation, off-diagonal proofs and the true signed multiplication of original source values. **The algebraic and indexing prerequisites are now source-written, but no typecheck receipt exists.**

The E20 *semantic/indexing* max-cut therefore narrows to verifying the new sources in Agda and connecting their already-typed graph to an **Agda** `List Bool` source/target binary codec with exact parser roundtrip, malformed words and bit-complexity. Python has the source/reference implementation, but that source is not a machine-polynomial Agda theorem. The actual Cook–Levin K00 clock, E01–E19 costed edges and all 21 NP-verifier machine bounds remain separately open and are not replaced by graph completion.

## 2026-11-02 VOA / Monster 3B / Fock graded-action BIDI max-cut

**Scope:** Source-first re-examination of the existing *literal VOA* and Monster/3B action owners before doing Karp-21 reduction work. All code implementation is **only** in this DASHI Agda PR. No CI or Agda kernel run. This section adds neither an unowned Monster representation nor a new graded VOA construction. **The 20 historical polynomial reductions and 21 NP membership obligations remain active.**

### Actual upstream source owners and the two different "max-cuts"

- `DASHI/Moonshine/GradedRepresentation.agda`: graded finite-dimensional group representations expose abstract endomorphisms and traces, but the group record itself exposes only identity, composition and associativity; **do not assume arbitrary inverses, finite enumeration, or a finite orbit solver**.
- `DASHI/Moonshine/GradedVertexOperatorAlgebraBoundary.agda` and `VertexOperatorAlgebraCore.agda`: distinguish graded representation from actual VOA vacuum, vertex modes, linearity, truncation, Jacobi, Virasoro and grade compatibility. `GradedVOAHomogeneousLinearRealisationExact.agda` plus `GradedRepresentationLinearRealisationExact.agda` supply the correct **conditional two-sided homogeneous carrier identification and evaluated linear endomorphism**, rather than guessing a state-action from a character.
- `DASHI/Moonshine/MonsterGradedVOALiteralActionSameObjectBidiExact.agda`, `MonsterGradedVOASelected3BSameElementBidiExact.agda`, and `DASHI/Reasoning/Trialectic369Selected3BFullGradeActionMaxCutExact.agda`: literal selected element must act on **the same carrier/grade representation** as its trace. The 3B **action max-cut** here is the unresolved faithful inclusion + selected full-grade action agreement, *not* Karp's weighted graph MAX CUT. [DASHI PR #1250](https://github.com/chboishabba/dashi_agda/pull/1250) records source-selected 6.Suz character and D4 equivariance restrictions; no mere 720/729 dimension or character fingerprint settles actual Monster representation ownership. [PR #1244](https://github.com/chboishabba/dashi_agda/pull/1244) contains a distinct finite C3 horn-tree/VOA quotient line; do not substitute C3 information-loss or directed quotient data for an undirected Karp cut.
- `DASHI/Moonshine/RankOneFockPartitionGradingExact.agda`: oscillator-grade partitions of the integer **energy** have explicitly proved dimensions `1,1,2,3,5,7` through grade 5. These are NOT input-subset decisions of Karp's signed PARTITION problem. Its Heisenberg/VOA extension and modularity remain different proof owners.

### New source-written EXACT reusable bridges (imported into Karp21Everything)

1. **`Karp21VOAZ2CutOrbitExact.agda`** instantiates the action-preservation idea on a **genuine, already-paid** Karp certificate action: global bit complement `Lap.flipLabels` on `Vec Bool (suc n)`. `canonicalBitLabels` normalises the first label to false. `canonicalFirstFalse`, `canonicalCutScore`, `canonicalAcceptedIff`, `canonicalCutWitnessIff`, and `canonicalVerifierValue` prove the exact arbitrary-signed-weight cut score, acceptance, existential YES and calculated verifier-output preservation. `canonicalCertificateWord`, `canonicalCertificateWordLength`, `canonicalCertificateWordDecodes` and `canonicalCertificateWordVerifierEqualsOriginal` reuse the **actual N21 exact n-bit certificate codec**; canonicalisation does not change input/certificate bit length. This is a 2-way witness-orbit **search optimisation for graphs with n≥1**, not a polynomial-time Karp machine or a real Monster action.
2. **`Karp21VOAGradeActionCertificateWeldExact.agda`** consumes an **actual `VOAWithGroupAction`**, a `HomogeneousGradeLinearRealisation`, and its evaluated endomorphism on that same grade. Its `SameGradeWitness.ExactCertificateActionWeld` explicitly requires `encodeCertificate`, `decodeCertificate`, `decodeAfterEncode` and `actionPreservesScore` for the actual signed `Cut.WeightedCutGraph`. Theorems `sameGradeActionPreservesVerifier`, `sameGradeActionPreservesAcceptedCut`, `sameGradeActionPreservesGraphYES` then transport the **same** verified cut through the genuine grade action. The nested **`LocalEdgewiseCertificate`** module now adds the nontrivial proof compiler **`actionPreservesEdgeList`**, deriving global score invariance by induction from `preservesEachEdge` on each actual signed graph edge; **`constructExactWeld`** packages the result without assuming a global energy equality or using character fingerprints. `certificateInclusionInjective` and `gradeActionAgreementReflectsCutWitness` reuse the selected-3B proof pattern—*agreement after inclusion, then faithfulness to recover agreement on the finite certificate*—without manufacturing an inhabitant for the selected Monster/3B source or bit-level action.
3. **`Karp21VOAGradeDimensionCutSeparationExact.agda`** reuses *actual finite Fock basis dimension* `RankOneFockPartitionGradingExact.gradeTwoDimension` and the *actual* 2-vertex, 1-edge, W=1 `Karp21SignedPartitionActualGraphYESExact.fixedUnitGraph`: `fockGradeTwoKarpTwoVertexDecisionSeparation` source-writes a counterexample where the **same grade-2 dimension (2)** coexists with an accepted and a rejected Boolean cut assignment on the same graph. This is a stronger finite, same-object demonstration than empty artificial `WrongType` declarations. Graded trace/dimension/numerological coincidences cannot replace input-sensitive same-object maps or real verifier receipts.

### Exact unpaid VOA-to-K00/E20/N21 and all-21 gates

**VOA bridge, if ever promoted:** `voaGradeWitnessActualInstance` (a concrete grade embedding into the selected actual VOA, not a record declaration); `voaActualGroupElementAndGradeAction` (real literal action matching the same grade and actual group element, maintaining original Ibrahim 3B ownership); `voaActionPreservesKarpSignedCutScore` (all edge weights and original bitwords); `voaGradeActionWordCodecPolynomialClock` (machine semantics and input length); `voaCharacterObservationDoesNotEraseDecision` (injectivity if quotienting by any nontrivial VOA action). The present generic weld is conditional and does not pay these.

**Non-VOA mathematical priority remains higher:** K00 same-bitword SAT machine/Cook–Levin; N21 graph Word parser, integer addition clock and `PR.InNP`; E20 source/target Word same-object Agda gamma/zigzag parser roundtrip, bit polynomial bound and `PR.PolynomialManyOneReduction`; all other E01–E19 source-to-target costed maps and N01–N20 verifiers. Do not treat VOA character modularity, finite Fock partition numbers, 3B normalizer action candidates, quotient orbit counts, or any action max-cut scheduling flag as a lower-bound theorem or as 20 completed Karp reductions.

**Receipt boundary:** these are source-written new Agda lemmas imported by the focused root, **not typechecked** here. New 0/20 full costed edge and 0/21 complete NP-completeness counts remain unchanged. Primary attribution: Stephen Cook (1971), Richard Karp (1972); VOA foundations Kac (1998), FLM (1984, 1988), Borcherds (1992); prior DASHI VOA/Monster/3B mathematical owners including Ibrahim remain separate. No new Monster same-object representation or new infinite Fock VOA is claimed.

## A. Honest current status (audited against #1445 GitHub tree)

| Proof owner / receipt | Verified object | State |
| --- | --- | --- |
| `DASHI/Mathematics/Complexity/PolynomialReductionExact.agda` | generic `composeReduction`, `pullbackPAlongReduction`, `npCompleteInPImpliesPEqualsNP` over a common `Word` and assumed cost-model laws | prior source owner; *not* 21 concrete instances |
| `.../CookLevinCircuitGCTBoundary.agda` | literal Boolean formula evaluator and a sample tautology; Cook–Levin `Simulation` is a record of **unfilled obligations** | partial |
| `.../PNotEqualsNPClayCoreExact.agda` | SAT-not-in-P ↔ P!=NP *assuming* standard completeness premises | conditional |
| `.../Karp21ScaledThresholdExact.agda` / `.../Karp21PartitionScaledInstanceExact.agda` | signed E20 scaled decision iff, source-list witnesses, and positive-threshold branch | source-written; concrete graph bitstring adapter/cost/kernel receipt outstanding |\n| `.../Karp21FiniteCliqueCoverCardinalityExact.agda` | finite E05 complement cardinality and all-k additive threshold iff | source-written; finite graph index/serialization/cost/kernel receipt outstanding |\n| `.../Karp21HeterogeneousEncodingExact.agda` | generic source-word decoder + target-word encoder + instance-iff to costed PR bridge | source-written; concrete faithful codecs and machine time still unpaid |\n| `.../Karp21HistoricalDagExact.agda` | `twentyOneNamedNodes`, `twentyHistoricalEdges`, `allNodesHistoricallyReachable` on a **source-authored historical graph** | source-written; no concrete reduction or Agda kernel receipt |\n| `.../Karp21ReductionTransportExact.agda` | `npCompleteIsHard`, `transportNPHard`, `transportNPComplete` given costed reductions | source-written in #1445, kernel acceptance **not checked here** |
| `.../Karp21CliqueVertexCoverExact.agda` | `karpCliqueCoverSemanticEquivalence` over Boolean selected-vertex predicates; off-diagonal semantics | source-written; cardinality/bit cost unpaid |
| `.../Karp21CliqueSetPackingExact.agda` | `karpCliquePackingSemanticEquivalence` on symmetric adjacency and vertex-indexed nonedge-incidence subsets | source-written; finite instance/duplicate sets/bit cost unpaid |
| `.../Karp21WeightedCutObjectiveExact.agda` | `cutObjectiveFlip`, `flipThresholdCut`: global side reversal preserves edge-list objective | source-written; PARTITION→cut exact polynomial map unpaid |
| `.../Karp21Everything.agda` | focused import/check root for above | source-written; no pinned Agda receipt shown |
| `scripts/check_karp_partition_maxcut.py` | exhaustive positive-list PARTITION/cut identity and threshold finite regression | 19,530 strictly positive plus 3,906 signed/zero instances independently audited (23,436 total); all cut assignments, signed product identity, zero-total fixed YES instance and positive-threshold guard; not a proof |
| `dashi_lean4` PR #78 | pinned `openai/math` vendor + catalogue, `OAI.OptimalMaxCut.main` and `OAI.VertexCover.every_fixed_factor_below_two` routing | sources inspected; no Agda same-object port |
| `DASHI/Planning/NetworkFlowCapacityCongestionExact.agda` | qualitative toy joint-capacity no-promotion | not Ford–Fulkerson or maxflow/mincut |
| `DASHI/Computation/BellmanFordRelaxationScheduleFibreExact.agda` | shortest-path Bellman–Ford schedule fibre | **not** Ford–Fulkerson |

**Checked end-to-end Karp problem completions in this PR: 0/21. Checked direct concrete Karp reductions with polynomial time proof: 0/20.** The historical DAG and four semantic/transport Agda owners are source-written; their semantics do not discharge NP-hardness without the resource/certificate adapters. Do not overwrite these counts based on module names.

## 2026-11-01 max-cut implementation tranche: concrete finite executables (not machine proofs)

New executable checked against **independent brute-force instance predicates**:
`scripts/check_karp_historical_reductions.py`, source-written on this PR and independently run locally, all passing.

| Historical edge | Executable input construction and independent oracle | Exhaustive bounded checks |
| --- | --- | ---: |
| E01 SAT → 0–1 IP | literal true-count as integer equality with bounded binary slack | 523 |
| E02 SAT → CLIQUE | one literal-occurrence node per clause; cross-clause noncomplement edges | 10,128 |
| E03 SAT → 3-SAT | fresh-variable chain; no clauses wider than 3 | 10,132 |
| E04 CLIQUE → SET PACKING | indexed vertex incident nonedge pairs | 437 |
| E05 CLIQUE → NODE COVER | complement graph, threshold `n-k` with invalid `k>n` no-case | 437 |
| E06 NODE COVER → SET COVER | universe of actual graph edges; vertex-indexed incidence sets | 437 |
| E07 NODE COVER → FEEDBACK NODE SET | bidirected edge arcs and independent directed-acyclicity oracle | 41 |
| E08 NODE COVER → FEEDBACK ARC SET | two-layer graph, backbone/cross arcs, independent directed-acyclicity oracle | 41 |
| E10 DIRECTED → UNDIRECTED HAMILTON | three copies per vertex; exhaustive cycle oracle | 69 |
| E12 CHROMATIC → CLIQUE COVER | complement graph with same palette threshold | 361 |
| E14 EXACT COVER → HITTING SET | transpose incidence; **exactly one** hitting element | 585 |
| E15 EXACT COVER → STEINER TREE | root-set-element weighted gadget; independent exhaustive forest/terminal connectivity oracle | 85 |
| E17 EXACT COVER → KNAPSACK | carry-free base `numberOfSets+1` incidence digits | 585 |
| E18 signed KNAPSACK → JOB SEQUENCING | sign-safe digit-pair normalization → positive times/penalties → deadlines | 120 |
| E19 signed KNAPSACK → PARTITION | sign-safe digit-pair normalization before Karp's positive subset-sum gadget | 780 |

**Current finite cut:** E01–E08, E10, E12, E14–E15 and E17–E19 are checked in the first script; E09/E11/E13/E16 in the second; and E20 in the signed-domain script. **All 20/20 edges have independently executed bounded finite checks**, including 23,436 E20 instances. Do **not** translate 15/20 or 16/20 into 15/20 kernel-verified reductions: the latter remains **0/20**. E20 is intentionally not duplicated into the consolidated Python file.

**All 20 direct edge executable constructors are now present in the three scripts**, though E16 requires its Karp source preprocessing assumption and E09 needs full malformed/zero-budget handling. The universal mathematical correctness/cost/NP-membership obligations remain for all E01–E20.

### Newly audited Agda semantic bridges

- `Karp21VertexSetCoverIncidenceExact.agda`: `karpNodeCoverSetCoverWitnessIff` constructs incidence set-cover witnesses in both directions, for all off-diagonal graph edges.
- `Karp21ColouringCliqueCoverExact.agda`: `karpColouringCliqueCoverWitnessIff` moves a given colour assignment across adjacency complement, for arbitrary Boolean colour equality.
- `Karp21ExactHittingTransposeExact.agda`: `karpExactCoverHittingWitnessIff` retains the original **exactly-one** incidence requirement by transposition, with chosen-set uniqueness.
- These are **source-written Agda** declarations included in `Karp21Everything.agda`; none has a pinned-toolchain Agda acceptance receipt yet. Do not count them as certified E06/E12/E14 until concrete finite cardinality/encoding and machine cost are also proved.

### Critical Karp variant and signedness corrections

- N15 (Karp 1972) is **exact hitting**, `|W∩U_i|=1` for every `i`; the modern unrestricted hitting set requires `|W∩U_i|≥1`. They must be separate typed problems. The historical reduction E14 uses the original one-hit formulation; a separate reduction is required for modern hitting set.
- N18 KNAPSACK is signed subset sum `Σa_i x_i=b`, and the textbook two-extra-number E19 construction assumes positive nonnegative source items: applying it naively to arbitrary signed input admits spurious YES cases. For example `a=(-1), b=9` is NO but the naive resulting PARTITION has total 0 and an empty equal partition. **New DASHI executable extension** encodes each signed choice `a_i` by a pair of positive integers whose unique high digit forces exactly one member of each pair, with a low digit retaining the signed sum. The digit base exceeds the maximum low-digit sum, avoiding carries; then applies Karp's standard positive PARTITION gadget. Named Agda follow-on targets: `signedSubsetSumDigitPairSound`, `signedSubsetSumDigitPairComplete`, `signedSubsetSumNoCarry`, `signedSubsetSumEncodingPolynomialBits`, `positiveSubsetSumPartitionIff`, `signedKnapsackPartitionCompositeIff`.
- E18 JOB SEQUENCING uses the same newly normalized positive subset-sum instance, with `T_i=P_i=a_i`, common deadline `D_i=b` and penalty budget `Σa_i-b`. Cases with zero penalty budget are mapped to a fixed positive-budget YES scheduling instance. This is a DASHI extension of the historic Karp positive-subset-sum reduction, **not** a new historical result attributed to Karp.
- E01 0–1 IP is equality feasibility, not inequality-only optimization: each clause encodes `Σ_j truth(l_j) - Σ_h 2^h s_h = 1` using bounded Boolean slack. Need the exact malformed-input and bitwidth proofs.
- For E07/E08, the directed-cycle oracle checks actual graph acyclicity, rather than relabelling graph cover as a theorem.
- E15's bounded independent oracle checks the existence of an acyclic weighted subgraph connecting all required terminals. For nonnegative gadget weights, disconnected irrelevant forest components may be discarded without changing existence of a Steiner tree. The general proof still needs this discard lemma and a polynomial edge-count proof.

### Reuse correction: SAT / Cook–Levin source already has much more than a record shell

`DASHI/Mathematics/Complexity/FixedWidthCNFToCookFormulaExact.agda` source-writes `cnfCookSatisfiabilityExact` and literal CNF evaluation equivalence on the **same** `Cook.BooleanFormula` carrier.

`DASHI/Mathematics/Complexity/ConcreteTapeCookLevinCookFormulaExact.agda` source-writes `cookFormulaExactBudgetIff`, connecting an **actual exact-budget concrete tape accepting run** to `Cook.Satisfiable(guardedCookFormula ...)`. This is earlier repository prior-art; do not rebuild the same semantic theorem just to satisfy K00i. Its missing universal cost/computation quantifiers and the standard `PR.NPComplete` machine witness still need an exact proved bridge. **Updated K00i:** `cookLevinSATRoot` should consume these actual owners, prove the uniform polynomial clock/bit-size and tape reduction for arbitrary NP instances, and instantiate the shared concrete SAT `PR.NPComplete`, rather than asserting it from a record field.

### Exact completion acceptance counters (current)

- Historical problem definitions indexed: 21/21 (source-written Agda DAG, not kernel verified).
- Direct reduction graph entries indexed: 20/20 (source-written Agda DAG, not kernel verified).
- Finite executable edge implementations tested independently: 20/20 across three scripts, all still awaiting Agda end-to-end kernel proof.
- Agda kernel-verified **concrete** direct polynomial reductions on this PR: 0/20. The new `CertifiedKarpNetwork` proof compiler consumes the still-missing certificates.
- Agda kernel-verified **end-to-end** NP-completeness results on this PR: 0/21.
- OpenAI approximation/scheduling donor same-object kernel ports into Agda: 0.
- Source authorship, tests and conditional interfaces are tracked separately.


### Final 4-edge finite construction expansion (separate executable)

`scripts/check_karp_remaining_four_gadgets.py` now implements and tests the remaining historical edges:

| Edge | Exact finite construction | Passing bounded cases | Universal missing lemma |
| --- | --- | ---: | --- |
| E09 | Karp's node-cover → directed Hamiltonian anchor/incident-edge gadget; independent Held–Karp subset DP | 15 | `vertexCoverDirectedHamiltonianIff`, `vertexCoverDirectedHamiltonianCost`, incidence enumeration/isolated-node guards |
| E11 | 3-SAT → (m+1)-colour graph, four-variable padding, clause-literal adjacency; independent finite graph-colouring backtracker | 7,555 | `threeSATColouringIff`, `threeSATColouringCost`, tautology normalization and padded-anchor palette argument |
| E13 | Colouring → Exact Cover with vertex, edge, incident-colour slot tokens and indexed sets | 36 | `colouringExactCoverIff`, `colouringExactCoverCost`, small-palette fixed-NO guards |
| E16 | Exact Cover → 3D Matching incidence-cycle/permutation gadget `(alpha(i),sigma,sigma)` / `(beta,sigma,pi(sigma))`; independent perfect matching DFS | 21 | `exactCoverThreeDimensionalMatchingIff`, `exactCoverThreeDimensionalMatchingCost`, general singleton/empty-set preprocessing |
 
E11's construction checks the literal-source SAT truth after removing tautological clauses and duplicate literals, and uses `m≥4` so every ≤3-literal clause omits a variable to rule out spurious extra-colour assignments. E16 **only** constructs the Karp gadget for nonempty sets with ≥2 elements, exactly matching the quoted "without loss of generality" source precondition; preprocessing the general exact-cover domain remains an explicit lemma. E09 has source-domain guards (nonempty edge incidence, positive budget), with trivial positive-budget YES cases handled separately. Neither the bounded DP/DFS nor the graph-colouring backtracker is claimed polynomial.

**Revised finite implementation coverage: 20/20 historical direct reductions have a source-written executable candidate and passing bounded equivalence controls, spread across three scripts** (`check_karp_historical_reductions.py`, `check_karp_remaining_four_gadgets.py`, `check_karp_partition_maxcut.py`), plus a fourth independent flow/APX consumer. This does **not** prove any complete reduction theorem in Agda. All 20 remain open for general correctness proofs, binary encoding, constructive witness sizes, and actual polynomial machine costs. Completion count for 21 NP-completeness theorems remains 0/21.

### Binary-size repair (implemented, still awaiting formal time/size proofs)

The finite executables now normalize actual SAT variable identifiers to a dense `1..m` index before E01 binary-IP matrix construction and E11 colouring palette construction. Otherwise an instance declaring variable index `10^15` but using only one literal would allocate `10^15` columns/anchor vertices, which is not polynomial in the input's **binary length**. Regressions include a sparse variable of index `10^15`.

Likewise E13 `colouring_to_exact_cover` now returns a constant-size YES exact-cover instance whenever binary-encoded `k≥n`, rather than constructing `k` colour gadgets. The general branch only uses `k<n`. E09 already bounds nontrivial anchor count by the number of active vertices, with trivial YES guards.

Required additional formal lemmas: `denseCNFRenamingSatisfiabilityIff`, `denseCNFRenamingBitCost`, `colouringBudgetAboveVertexCountAlwaysYes`, `colouringToExactCoverBoundedPalette`, `binaryIPSlackBitwidthSuffices`. Proving only the constructor's termination (or testing the above finite controls) does not discharge `PR.polynomialTimeMap` in the real encoded cost model.

## Conditional kernel-facing 21-node proof compiler (source-written)

`DASHI/Mathematics/Complexity/Karp21CertifiedDagTransportExact.agda` now defines:
- `CertifiedKarpNetwork`: the **actual** shared `PR.PolynomialCostModel`, `PR.PolynomialMapComposition`, SAT NP-completeness root, all 21 NP membership proofs, and one `PR.PolynomialManyOneReduction` certificate for **each** historical `Dag.Edge`.
- `npCompleteAlongReachability`: structural induction on a genuine `Dag.Reachable` proof; recursively applies existing `Transfer.transportNPComplete`.
- `allTwentyOneNPCompleteIfCertified`: builds `PR.NPComplete cost (language p)` for **every** Karp node, using the source-written 21-node DAG reachability witnesses.
- `anyKarpTargetInPImpliesPEqualsNP`: conditional classical P=NP consequence for any **independently established** polynomial-time decision algorithm on one complete target, using the existing `PR.npCompleteInPImpliesPEqualsNP`.

This is a substantive proof-composition function, not a vacuous Boolean completion flag. **It assumes real evidence for each of the 20 edges, SAT-root completeness and all NP-membership certificates.** The source has not yet been kernel-checked in the pinned Agda environment; the theorem is not promoted to 21 accepted NP-completeness certificates.

The **remaining graph cut** is no longer inventing repeated completeness wrappers. It is constructing these exact `CertifiedKarpNetwork` inputs and proving their machine costs in the common encoded carrier.

## Additional exact finite consumer audit: flow, minimum cuts and APX

The repo's earlier `DASHI/Planning/NetworkFlowCapacityCongestionExact.agda` remains a **qualitative** capacity example and is not overwritten. New `scripts/check_karp_flow_cut_apx.py` provides separate executable implementations and independent finite checks:

| Target / algorithm | Exact executable invariant checked | Passed bounded cases | Missing Agda theorem |
| --- | --- | ---: | --- |
| Edmonds–Karp BFS residual max-flow | each augmentation strictly increases total integer flow; terminal residual reachable set excludes sink; net flow conserved at interior vertices; value equals cut capacity and exhaustive min **s-t** cut optimum | 738 directed capacitated networks | `augmentPathPreservesFlowFeasibility`, `augmentRaisesFlowValue`, `flowValueLeqCutCapacity`, `maxFlowMinCutEquality`, `edmondsKarpBFSRuntimePolynomial` |
| MAX CUT nonnegative APX baseline | deterministic conditional expectation yields cut at least half total edge weight, hence at least half optimum | 759 weighted graphs | `conditionalExpectationMaxCutHalf`, `maxCutNonnegativeApproximationRatioTwo`, explicit bit-cost polynomial algorithm |
| VERTEX COVER nonnegative APX baseline | endpoints of a maximal matching cover every edge and have cardinality `2*matchingSize ≤ 2*OPT` | 1,098 simple graphs | `maximalMatchingEndpointsCover`, `maximalMatchingLowerBoundOptimalCover`, `vertexCoverTwoApproximation` |
| MINIMUM k-CUT / min-s-t relation | canonical unlabelled `k`-partitions; global 2-cut = minimum over all distinct terminal-pair s-t mincuts; min-k objective nondecreasing in k for finite nonnegative graphs | 74 finite undirected graphs | `globalTwoCutEqualsMinOverST`, `minKCutMonotone`, fixed-k vs variable-k resource bounds |

**Historical boundaries:** Ford–Fulkerson is the general residual augmenting-path method, not the Bellman–Ford shortest-path algorithm. Edmonds–Karp adds BFS selection, yielding polynomial `O(VE²)` (source complexity still to be proved in Agda). Min s-t cut is a **minimum** nonnegative-capacity objective, not Karp's **maximum** signed-weight threshold objective. Constant-factor APX algorithms are not the OpenAI `OAI.OptimalMaxCut.main` optimal-inapproximability theorem and do not supply its Lean/Agda same-object port. Minimum k-cut for variable k has a different complexity contract than fixed-k.

With the original 55,824 Karp-edge finite checks plus 2,669 additional flow/mincut/APX test instances, the independently executed bounded controls now cover **58,493 edge/consumer cases**. The source-committed runner `scripts/run_karp21_reduction_regressions.py` enumerates all four scripts; no exact GitHub checkout execution or pinned Agda kernel acceptance is claimed for the new source.

## 2026-11-01 genuine E20 source proof cut (signed graph objective)

New canonical owner: `DASHI/Mathematics/Complexity/Karp21PartitionCutQuadraticExact.agda`, directly imported by `Karp21Everything.agda`. This is **new Agda proof source**, not an Agda kernel receipt:

1. `signedTotalDecomposes`: over a list of signed integer values paired with Boolean side labels, total equals left sum + right sum.
2. `partitionCutProductIdentity`: reuse existing DASHI integer ring solver to prove `4ab=(a+b)²-(a-b)²` for arbitrary `a,b:ℤ`.
3. `crossWithTrue` / `crossWithFalse`: crossing edges from a fixed source vertex sum to that vertex weight times the **opposite-side** total.
4. `completeGraphCutEqualsPartitionProduct`: induction on the *actual triangular complete-graph edge enumeration*, each pair counted once; the weighted cut equals leftTotal × rightTotal for **all** signed-weight inputs and **all** side labelings.
5. `completeGraphCutQuadratic`: compose (2) and (4) to give `4*cut=T²-(A-B)²` on the actual cut objective.
6. `balancedSelectionIffExactMaximum`: using the earlier repo's `IntP.i*j≡0⇒i≡0∨j≡0` no-zero-divisors owner and RingZ cancellation, prove the exact bidirectional equivalence `leftTotal=rightTotal` **iff** `4*actualCompleteGraphCut=total²` for all signed input lists.

This is no longer a merely assumed objective identity. **Historical intermediate status:** the old unscaled route required a ceiling lemma. Later in this roadmap, the new scaled E20 route discharges the integer threshold, zero-total and positive-threshold *semantic* obligations without ceiling. The still-open gates are a faithful explicit graph serializer, universally proved bit-cost/machine clock, target NP verification and a pinned Agda check.

**Source-critical counterexample:** Karp p.100's printed typography renders the MAX CUT threshold as a bracketed quarter of a **sum of squared inputs** `ceil((Σ cᵢ²)/4)`; used literally this is **not** equivalent to PARTITION. Independent local counterexample `c=(2,1)`: source partition is NO, but graph edge weight 2 meets the printed threshold `ceil(5/4)=2`. The actual algebraically justified threshold is `ceil((Σ cᵢ)²/4)=3`, making the cut NO. Other published discussions identify the same distinction; do not silently upgrade the literal printed expression to a proof. The executable `check_karp_partition_maxcut.py` now includes this explicit false-positive regression, alongside its signed-integer/zero-total checks. The original source remains credited to Karp; the corrected formula/diagnostic is an independently documented DASHI reconstruction, not claimed as his verbatim statement.

**E09 totality repair:** `graph_to_directed_hamiltonian` no longer raises an assertion for a graph with a nonempty edge set and zero cover budget; it maps this impossible source case to a fixed 3-node NO instance. This is a total-function repair, not a universal Hamiltonian-gadget proof.

## 2026-11-01 additional exact-source lemma tranches

**E20 signed complete-graph algebra**, `Karp21PartitionCutQuadraticExact.agda`:
- `signedTotalDecomposes`: every signed weighted partition equals the sum of its two sides.
- `completeGraphCutEqualsPartitionProduct`: recursively enumerated complete-graph *crossing edges* sum to `leftTotal*rightTotal`.
- `completeGraphCutQuadratic`: compose with previously existing DASHI integer RingZ solver, yielding `4*actualCut = total²-(left-right)²`.
- The source is part of the focused Agda root. Independent SymPy symbolic expansion passed; no pinned Agda check yet. **Historical unscaled-route alternative:** ceiling comparison remains optional; the subsequent scaled positive-threshold route covers all total values. Common remaining tasks: explicit encoded graph/word semantics, universal polynomial clock and actual `PR.PolynomialManyOneReduction`.

**E03 Cook-origin four-to-three exact Boolean gadget**, `Karp21SATToThreeSATGadgetExact.agda`:
- `fourToThreeWitness`: explicit fresh assignment `x=(c∨d)` takes an accepted `a∨b∨c∨d` to both true `a∨b∨x` and `¬x∨c∨d`.
- `threeToFourWitness`: conversely any accepted two-clause model implies the original four-literal clause; false case closes by impossible Booleans.
- `cookKarpFourToThreeClauseIff`: a constructive `PR.Iff` for the gadget, using no postulates or oracle.
- Independent local truth-table check passed 16/16 assignments with both values of fresh bit examined. Still **not kernel checked**. **E03 residuals:** general >3 recursive clause compiler, fresh-name hygiene, bounded extension witnesses, global CNF satisfiability preservation, canonical source SAT/3SAT encodings, polynomial input/output tape cost.

**New counterexample/malformed regression controls**:
- `scripts/check_karp_partition_maxcut.py` pins `(2,1)` against the literal sum-of-squares reading of Karp's printed threshold, and distinguishes the mathematically correct square-of-sum threshold.
- `scripts/check_karp_remaining_four_gadgets.py` is now total on zero/negative node-cover budgets for E09, including empty graphs; negative k is mapped to a fixed NO digraph before the vacuous edge-empty YES case.

**Numerical regression status is unchanged:** the earlier bounded finite controls are evidence, not universal proofs. The new small SymPy/truth-table checks do not change the per-edge 0/20 kernel acceptance count.

### Signed integer binary size regression (E20)

The E20 script now measures a conservative **bit count** of each vertex identifier, sign/magnitude edge weight and positive threshold, rather than just counting arithmetic operations or edges. It checks the loose polynomial envelope `outputBits ≤ 32*(sourceBits+1)^3` on 54 zero/positive/signed instances with input magnitudes up to `2^1024`; an independently executed matching local Python check passed all 54 cases. The formal residual remains `partitionSignedWeightBitCost`: a theorem bounding **all** signed integer inputs under a precise canonical serializer and fixed machine-clock model. Sampled bit lengths do **not** close that universal obligation.

## 2026-11-01 advanced E20 closure: exact signed decision iff **without ceiling**

The new source-written modules are imported from the focused `Karp21Everything.agda` root:

- `Karp21ScaledThresholdExact.agda`: `squareSubtractBound`, `scaledScoreBelowSquare`, `scaledThresholdIffBalanced`, `nonzeroIntegerSquare`, `nonzeroTotalSquareIsPositiveThreshold`. The scaled graph has signed weights `4*c_i*c_j` and integer threshold `T²`, where `T=Σc_i`; for nonzero T the threshold is certified as nonnegative and nonzero, hence positive. The score is at most `T²` by the previously proved exact signed quadratic identity and pre-existing integer square nonnegativity, so threshold acceptance iff balance.
- `Karp21PartitionScaledInstanceExact.agda`: `Selection` is one Boolean label for **each input list element** (duplicates preserved); `taggedTotalMatchesSource` transports the sum independently of labels; `signedPartitionScaledCutInstanceIff` proves the existential source/target YES equivalence; `zeroTotalPartitionYES` constructs the all-false choice witness for every zero-total input. `totalPartitionToPositiveCut` returns a genuine proof-tagged positive-threshold `PositiveCutTarget` in **both** cases: the zero-total fixed two-vertex unit-edge YES graph, or the scaled signed complete graph with T≠0 proof. `positiveTargetThresholdCertified` and `totalPartitionPositiveCutIff` prove its exact threshold validity and universal total reduction YES-iff, respectively.
- `Karp21HeterogeneousEncodingExact.agda`: `compileHeterogeneousKarpReduction` proves the **general** faithful source parser / source iff / heterogeneous instance transform / target iff / encoded map → `PR.PolynomialManyOneReduction` result, explicitly demanding a *real* `PR.polynomialTimeMap` witness. Every source word, including malformed encodings, is handled by the source-faithfulness premise. There is **no** invented polynomial time assertion.

**Decisive result:** the E20 arithmetic, integer order/threshold acceptance, zero-total guard, positive threshold, and existential signed-input **semantic** equivalence are now present as source-written Agda theorems. The earlier `partitionCeilThresholdIffEquality` obligation becomes **optional** for the historical literal unscaled formula: E20's new integer-scaled reduction uses no ceiling. Attribution: Karp (1972) originated PARTITION→MAX CUT, whereas DASHI's scaled threshold `w(i,j)=4c_ic_j, W=T²` is an equivalent reconstructed convenience formulation.

**E20 exact residuals before `PR.PolynomialManyOneReduction` and NP-completeness can be claimed:**
1. `scaledCompleteGraphEdgeListFaithful`: materialize actual labelled finite undirected simple-graph edge lists/vertex ids from the input list, and prove their cut objective equals the current list-based triangular complete-graph sum (without reading any selection witness while constructing the graph).
2. `scaledGraphCanonicalWordEncoding` / `scaledGraphMalformedInputPolicy`: canonical signed integer and graph byte serialization, faithful source and target parsers for all words (including bad encodings), and exact roundtrip.
3. `scaledSignedWeightBitBound` / `scaledPartitionGraphMachineClock`: binary output length and real time for all input bitstrings in the repository's explicit machine cost model; the 23,436-instance Python oracle and 54 large integer bit-size samples are only secondary evidence.
4. `e20EncodedPolynomialReduction`: instantiate `compileHeterogeneousKarpReduction` with the actual graph target, source language, semantic iff, and paid machine cost. `weightedMaxCutInNP` still requires concrete bounded cut labels, exact signed sum bit-cost and verifier clock.
5. Run the pinned Agda type-check root and audit actual compiled imports for holes/axioms. **Source-written ≠ kernel-verified.**

## 2026-11-01 E05 cardinality max-cut (source-written)

`Karp21FiniteCliqueCoverCardinalityExact.agda` is included in the focused Agda root and derives:
- `chosenAndUnchosenAddToLength`, `countFlippedEqualsNotChosen` and `cliqueCoverFiniteCardinalityComplement`: finite vertex-list slots partition exactly into selected and complement sets, preserving duplicate vertex-position identity.
- `cliqueBoundToCoverBound`, `coverBoundToCliqueBound`, and `karpCliqueCoverFiniteThresholdIff`: **for every natural k, including k>n**, the cardinality inequality `k≤cliqueCount` iff `complementCoverCount+k≤n`. This avoids truncated Nat subtraction while proving the mathematically exact threshold relation.
- The prior source `Karp21CliqueVertexCoverExact.karpCliqueCoverSemanticEquivalence` already has the pointwise adjacency complement iff. **Unpaid E05**: combine both in the *same finite indexed graph model* (vector-to-list selection/lookup correspondence), materialize complement graph and target budget `n-k` with its k>n fixed-NO case, prove the binary graph map and clock, and kernel-check source.

An independent local Python truth-table audit of the E05 finite cardinality theorem covered **26,622** choice-list/threshold combinations (length 0..10, k 0..n+3) with no counterexample. This is secondary evidence, not Agda acceptance.

## 2026-11-01 Pareto continuation: E05 same-object finite carrier + N21 signed verifier

**E05 source repair:** `Karp21FiniteCliqueCoverCardinalityExact.cliqueBoundToCoverBound` had a misplaced use of `NatP.+-monoʳ-≤`: the lemma produces `k+unselected ≤ chosen+unselected`, whereas the theorem needs `unselected+k≤n`. The source now first uses `NatP.+-comm unselected k`, then the monotonicity step and the proved partition cardinality identity. This is a proof repair, not a claim that Agda was run.

**E05 finite same-object bridge:** `Karp21FiniteCliqueVertexCoverCombinedExact.agda` defines `FiniteCliqueAt` and `FiniteComplementCoverAt` using precisely one `Vec Bool n`, one `Fin n` vertex carrier, one adjacency function and one natural `k`. `selectionListLength` proves list/vector length agreement structurally; `finiteCliqueToComplementCover`, `finiteComplementCoverToClique`, and `karpFiniteCliqueVertexCoverIff` jointly transport (a) pointwise complement adjacency/selection and (b) finite cardinality constraints on the **same** selection. The all-`k` additive budget `coverCount+k≤n` works even when `k>n`. **Still open:** explicit simple-graph matrix/edge-list encoding, diagonal removal, graph symmetry, ordinary target `n-k` with fixed-NO guard, faithful bitstring parsers, polynomial map clock, concrete node-cover `PR.InNP`, and pinned Agda acceptance.

**N21 signed MAX CUT verifier semantics:** `Karp21FiniteWeightedMaxCutVerifierExact.agda` represents each off-diagonal edge by two `Fin n` endpoints and signed `ℤ` weight, and bundles a constructive positive integer threshold. A cut certificate is exactly a `Vec Bool n` assigning one label per position. `edgeListCutValue` sums the crossing-edge weights; `verifyWeightedMaxCut` uses existing `Data.Integer.Base._≤ᵇ_`, with `weightedMaxCutVerifierSound` and `weightedMaxCutVerifierComplete` reusing `Data.Integer.Properties.≤ᵇ⇒≤` / `≤⇒≤ᵇ`. `karpWeightedMaxCutExistentialIff` transports the full existential YES witness in both directions without assuming an oracle. The explicit finite graph is not asserted simple *as a whole*: no self-loops are constructible, but duplicate/reversed edges remain possible in a list until the canonical representation/normalizer is supplied.

**Exact remaining N21 NP proof obligations:** `maxCutUndirectedUniqueEdges` (canonical unique orientation/no duplicates), `maxCutMalformedParserTotal`, `maxCutGraphWordRoundtrip`, `maxCutPackedCertificateLength`, `maxCutPackedCertificateLookup`, `maxCutSignedSumBitBound`, `maxCutVerifierPolynomialClock`, `maxCutNPCompleteCarrierBridge` (a genuine `PR.InNP`, not merely existence of a Boolean check). **E20 consumer seam:** `scaledCompleteGraphEdgeListFaithful` must connect the signed pairwise complete graph generated from source list elements to `edgeListCutValue` for the same Boolean vector; no theorem currently equates these two separately implemented objectives.

**Global max-cut unchanged:** `K00` shared machine/word encoding and uniform Cook–Levin SAT completeness; `E01`–`E20` concrete encoded polynomial reductions and costs; `N01`–`N21` polynomial-time verifiers and certificate bounds; donor-source same-object correspondence and independent kernel checking. There are still **0/20** *new kernel-verified concrete costed* direct reductions and **0/21** *new kernel-verified complete problem theorems* on this PR. No CI or Agda typecheck was run.

### Additional E05/N21 witness closure in the same tranche

- `Karp21FiniteCliqueVertexCoverCombinedExact.karpFiniteCliqueVertexCoverInstanceIff`: quantifies over the **same** `Vec Bool n` and proves the full finite existential CLIQUE YES iff finite complement-cover YES decision predicate; not just a pointwise statement for a preselected vector. Exact source/target witness functions: `finiteCliqueYESImpliesComplementCoverYES`, `finiteComplementCoverYESImpliesCliqueYES`. The graph and threshold remain in the same typed `Fin n` representation; the concrete target bitstring's budget `n-k` and machine cost remain open.
- `Karp21FiniteWeightedMaxCutVerifierExact.cutCertificateHasVertexCountBits`: every `Vec Bool n` cut certificate has exactly `n` Boolean entries, reusing the previously proved `FiniteCounts.selectionListLength`. `karpWeightedMaxCutExistentialIff` proves the actual existence of an accepted signed-cut witness iff the Boolean verifier accepts some witness. This closes the **mathematical finite certificate-length identity**, not the general bitstring length/clock portion of `PR.polynomialCertificateBound` / `PR.polynomialTimeVerifier`.

**Still required for completion:** `e05EncodedPolynomialReduction` with a no-loop, undirected, unique-edge complement transducer and certified `k>n` guard; `e20CompleteGraphToWeightedCutEdgeListIff` connecting the signed pairweight constructor to the verifier's finite edge list; `weightedMaxCutGraphAndCertificatePackedCodec`; actual `PR.InNP` on the shared Word and polynomial clocks. The corresponding E01–E19 encoded machine reductions and all 21 NP members remain open except for explicitly reused source-level pieces.

### Further E05 actual simple-graph closure (source-written)

`Karp21SimpleGraphComplementExact.agda` eliminates the diagonal defect of naïve pointwise Boolean negation. Its `SimpleGraph n` contract explicitly records symmetric adjacency and absent self-loops. `simpleComplementAdjacency` uses a decidable `Fin n` equality test and negates adjacency **only off the diagonal**. Reused `Data.Fin.Properties._≟_` yields: `simpleComplementLoopFree`, `simpleComplementSymmetric`, and `simpleComplementOffDiagonal`. `complementSimpleGraph` constructs the genuine simple target graph.

The exact semantic transport continues through `finiteAbstractCoverToSimpleCover` and `finiteSimpleCoverToAbstractCover`, giving `karpCliqueSimpleComplementCoverIff` for a chosen `Vec Bool n`; `karpSimpleGraphCliqueCoverInstanceIff` then proves the **existential full finite source/target decision iff** without losing the source selection or its all-`k` additive cardinality bound. This supersedes the earlier abstract finite complement for simple graph semantics, but does not claim the **canonical binary** complement graph serializer, classical `n-k` budget guard, or costed many-one reduction.

**Exact remaining E05 targets**: `simpleGraphMatrixEncodingRoundtrip`, `simpleComplementCanonicalBitMap`, `simpleComplementPolynomialMachineClock`, `complementCoverAdditiveToStandardBudget` (including `k>n` fixed-NO), `finiteCliqueCertPackedCodec`, `finiteCoverCertPackedCodec`, `finiteCliqueInNP`, `finiteVertexCoverInNP`, `e05EncodedPolynomialReduction`, and pinned kernel receipt. For N21, `cutCertificateHasVertexCountBits` is source-written, but bit-level certificate parsers and a polynomial verifier clock remain open.

### E12 reused finite graph/palette theorem (source-written)

`Karp21FiniteColouringCliqueCoverExact.agda` reuses the **same** loop-free `SimpleGraph n` and `simpleComplementAdjacency` owner as E05. It defines a `Vec (Fin k) n` palette assignment so each actual vertex has exactly one colour from `k` choices. The finite `samePaletteColour` equality test has reflexivity/soundness lemmas. `colouringToSimpleCliqueCover` and `simpleCliqueCoverToColouring` transport the existing `Karp21ColouringCliqueCoverExact` pointwise theorem across the *actual off-diagonal simple complement*. `karpFiniteColouringCliqueCoverInstanceIff` upgrades this to the full existential source/target finite decision iff, with exactly the **same** colour assignment witness and finite graph.

**Remaining E12:** `colouringCanonicalWordParser`, `cliqueCoverCanonicalWordParser`, `colouringToComplementGraphBitMap`, `colouringToCliqueCoverPolyClock`, `colouringPaletteLargeKGuard` (binary `k≥n` direct YES), `colouringNPVerifierClock`, `cliqueCoverNPVerifierClock`, `e12EncodedPolynomialReduction`; the full targeted Agda kernel typecheck remains unrun. This does not by itself complete E11 SAT→colouring, E13 colouring→EXACT COVER, nor any other E01–E20 costed reduction.

### Agda source-compatibility repair before kernel validation

A manual check against Agda's actual builtin module and existing DASHI stdlib imports found a concrete issue in three newly written E05 graph/cardinality owners: `Agda.Builtin.Nat` does **not** export propositional `_≤_`. This has been corrected to `Data.Nat.Base._≤_` in `Karp21FiniteCliqueCoverCardinalityExact`, `Karp21FiniteCliqueVertexCoverCombinedExact`, and `Karp21SimpleGraphComplementExact`. This is a real source repair; static/no-hole checks must not be misreported as successful compilation. The remaining required proof is the pinned Agda kernel typecheck of `Karp21Everything.agda` and its full dependency cone, followed by resolution of any actual diagnostics.

## B. Canonical shared obligations (finish once; all problem nodes consume)

| ID | Required exact lemma/declaration | Statement and done condition |
| --- | --- | --- |
| K00a | `parseEncodeRoundTrip` | parsed canonical finite instances recover same instance; `decode(encode(x)) = x`, malformed cases deterministic |
| K00b | `encodingLengthPolynomial` | bits of every encoded finite graph, set-family, schedule, integer matrix/weights are polynomial in explicitly measured source bit-length |
| K00c | `heterogeneousReductionToWord` (reuses `compileHeterogeneousKarpReduction`, source-written in `Karp21HeterogeneousEncodingExact.agda`) | embed `A:InstanceA→Set`, `B:InstanceB→Set` into common `Word` without changing truth; no oracle or unproved cost assumption |
| K00d | `polynomialMapComposeConcrete` | prove actual clock polynomial composition/bit-comparison cost, instantiate `PR.PolynomialMapComposition` |
| K00e | `verifierPolynomialWitnessLength` | witness has finite encoded length polynomial in input size; verifier computes in bounded time, *including* arithmetic bit complexity |
| K00f | `reductionMalformedInputIff` | every source input, including bad encodings, reduces to a correctly classified target input |
| K00g | `costModelNonDegenerate` | polynomial predicates tied to concrete machine/size model; no vacuous model assigning all maps polynomial |
| K00h | `canonicalKarpNPCompleteTransport` | instantiate existing `transportNPComplete` with a concrete Karp edge and target NP certificate |
| K00i | `cookLevinSATRoot` | **actual** Cook–Levin tableau/circuit compiler, polynomial cost, iff acceptance/satisfiability on shared SAT language; not a record field assumed inhabited |
| K00j | `completeHistoricalReductionDAG` | exact 21 distinct typed nodes, exactly 20 source-labelled directed edges, proof of reachability from SAT and transport for all 21 |

For every node `Nxx`, use `<stem>Instance`, `<stem>Accepts`, `<stem>VerifierSound`, `<stem>VerifierComplete`, `<stem>CertificateBound`, `<stem>VerifierPolyTime`, `<stem>InNP`. The six latter declarations are **required** and currently unpaid for every new concrete Karp instance, except for any independently kernel-verified earlier owner established by source lookup. Semantic, clock and NP claims must be explicit; `InNP` must assemble them.

## C. Exact 21-node matrix (historical decision problems)

Each row's exact named `<stem>InNP` is the final NP-membership lemma; the uniform six supporting obligations above apply to that same `stem` (not implicit).

| Node | Karp 1972 problem / decision formulation | Exact terminal NP lemma | Current status |
| --- | --- | --- | --- |
| N01 | CNF SAT — satisfying Boolean assignment exists | `karpSATInNP` | BooleanFormula evaluator exists; canonical CNF/certificate/cost incomplete |
| N02 | 0–1 INTEGER PROGRAMMING — integer matrix equation feasibility with Boolean variables, **no optimisation** | `binaryIntegerProgrammingInNP` | open |
| N03 | CLIQUE — simple undirected graph has a clique of cardinality ≥ k | `karpCliqueInNP` | graph-selected predicate semantics only |
| N04 | SET PACKING — at least k pairwise disjoint indexed subsets | `karpSetPackingInNP` | clique/packing semantic duality only |
| N05 | NODE COVER / VERTEX COVER — cover all edges with ≤ k vertices | `karpVertexCoverInNP` | clique/complement-cover semantic duality only |
| N06 | SET COVERING — cover full universe using ≤ k indexed sets | `karpSetCoverInNP` | open |
| N07 | FEEDBACK NODE SET — delete ≤ k vertices to make directed graph acyclic | `karpFeedbackVertexSetInNP` | open |
| N08 | FEEDBACK ARC SET — delete ≤ k arcs to make directed graph acyclic | `karpFeedbackArcSetInNP` | open |
| N09 | DIRECTED HAMILTON CIRCUIT — single directed cycle visits every vertex once | `karpDirectedHamiltonianInNP` | open |
| N10 | UNDIRECTED HAMILTON CIRCUIT — single undirected cycle visits every vertex once | `karpUndirectedHamiltonianInNP` | open |
| N11 | SAT with at most 3 literals per clause — 3-CNF satisfiability | `karpThreeSATInNP` | OAI 378 CNF source donor; exact shared bridge open |
| N12 | CHROMATIC NUMBER — proper colouring with ≤ k colours | `karpColouringInNP` | open |
| N13 | CLIQUE COVER — partition vertices into ≤ k cliques | `karpCliqueCoverInNP` | open |
| N14 | EXACT COVER — pairwise disjoint indexed subsets cover universe exactly | `karpExactCoverInNP` | open |
| N15 | Karp's EXACT HITTING SET — select an index subset intersecting **each transposed set exactly once** (not modern ordinary hitting set) | `karpHittingSetInNP` | open |
| N16 | STEINER TREE — connect required terminals with length/weight ≤ k | `karpSteinerTreeInNP` | open |
| N17 | 3-DIMENSIONAL MATCHING — disjoint triples cover designated three sets | `karpThreeDimensionalMatchingInNP` | open |
| N18 | KNAPSACK — Karp's *subset-sum-like* feasibility variant; not a generic utility optimisation | `karpKnapsackInNP` | open |
| N19 | JOB SEQUENCING — single machine, deadlines, durations, tardiness penalties and budget | `karpJobSequencingInNP` | open; NOT Job-shop scheduling |
| N20 | PARTITION — split **signed integer vector** into equal sums (original `Z^s`) | `karpPartitionInNP` | Python finite identity only |
| N21 | MAX CUT — weighted graph has cut with weight ≥ threshold, Karp's sign/weight domain preserved | `karpWeightedMaxCutInNP` | generic edge-objective/reversal only |

For Karp's exact historical variants, normalize against the 1972 original before fixing the machine encoding. For example, clique-cover convention (partition versus cover) and negative-edge/zero-weight domains require explicit variant bridges if the original and modern statements differ. Do not silently substitute an easier optimization variant.

## D. Exact 20 reduction-edge matrix (historical adjacency; all currently resource-open)

Every `reduce...` below is a concrete **polynomial-time total encoder**; every `...Iff` is source yes iff target yes **for every accepted encoding**; and every `...Cost` proves an actual polynomial time / bit-length bound. These three statements are all required for each row. `...Hardness` then invokes the existing generic transport.

| Edge | Reduction | Exact function | Iff lemma | Time/size lemma |
| --- | --- | --- | --- | --- |
| E01 | N01 SAT → N02 0–1 IP | `reduceSATToBinaryIP` | `satBinaryIPIff` | `satBinaryIPCost` |
| E02 | N01 SAT → N03 CLIQUE | `reduceSATToClique` | `satCliqueIff` | `satCliqueCost` |
| E03 | N01 SAT → N11 3-SAT | `reduceSATToThreeSAT` | `satThreeSATIff` | `satThreeSATCost` |
| E04 | N03 CLIQUE → N04 SET PACKING | `reduceCliqueToSetPacking` | `cliqueSetPackingIff` | `cliqueSetPackingCost` |
| E05 | N03 CLIQUE → N05 VERTEX COVER | `reduceCliqueToVertexCover` | `cliqueVertexCoverIff` | `cliqueVertexCoverCost` |
| E06 | N05 VERTEX COVER → N06 SET COVER | `reduceVertexCoverToSetCover` | `vertexCoverSetCoverIff` | `vertexCoverSetCoverCost` |
| E07 | N05 VERTEX COVER → N07 FEEDBACK NODE SET | `reduceVertexCoverToFeedbackVertex` | `vertexCoverFeedbackVertexIff` | `vertexCoverFeedbackVertexCost` |
| E08 | N05 VERTEX COVER → N08 FEEDBACK ARC SET | `reduceVertexCoverToFeedbackArc` | `vertexCoverFeedbackArcIff` | `vertexCoverFeedbackArcCost` |
| E09 | N05 VERTEX COVER → N09 DIRECTED HAMILTON CIRCUIT | `reduceVertexCoverToDirectedHamiltonian` | `vertexCoverDirectedHamiltonianIff` | `vertexCoverDirectedHamiltonianCost` |
| E10 | N09 DIRECTED → N10 UNDIRECTED HAMILTON CIRCUIT | `reduceDirectedToUndirectedHamiltonian` | `directedUndirectedHamiltonianIff` | `directedUndirectedHamiltonianCost` |
| E11 | N11 3-SAT → N12 CHROMATIC NUMBER | `reduceThreeSATToColouring` | `threeSATColouringIff` | `threeSATColouringCost` |
| E12 | N12 CHROMATIC NUMBER → N13 CLIQUE COVER | `reduceColouringToCliqueCover` | `colouringCliqueCoverIff` | `colouringCliqueCoverCost` |
| E13 | N12 CHROMATIC NUMBER → N14 EXACT COVER | `reduceColouringToExactCover` | `colouringExactCoverIff` | `colouringExactCoverCost` |
| E14 | N14 EXACT COVER → N15 HITTING SET | `reduceExactCoverToHittingSet` | `exactCoverHittingSetIff` | `exactCoverHittingSetCost` |
| E15 | N14 EXACT COVER → N16 STEINER TREE | `reduceExactCoverToSteinerTree` | `exactCoverSteinerTreeIff` | `exactCoverSteinerTreeCost` |
| E16 | N14 EXACT COVER → N17 3D MATCHING | `reduceExactCoverToThreeDimensionalMatching` | `exactCoverThreeDimensionalMatchingIff` | `exactCoverThreeDimensionalMatchingCost` |
| E17 | N14 EXACT COVER → N18 KNAPSACK | `reduceExactCoverToKarpKnapsack` | `exactCoverKnapsackIff` | `exactCoverKnapsackCost` |
| E18 | N18 KNAPSACK → N19 JOB SEQUENCING | `reduceKarpKnapsackToJobSequencing` | `knapsackJobSequencingIff` | `knapsackJobSequencingCost` |
| E19 | N18 KNAPSACK → N20 PARTITION | `reduceKarpKnapsackToPartition` | `knapsackPartitionIff` | `knapsackPartitionCost` |
| E20 | N20 PARTITION → N21 WEIGHTED MAX CUT | `reducePartitionToMaxCut` | `partitionMaxCutIff` | `partitionMaxCutCost` |

**Every E01–E20 must also export** `<edge>PolynomialReduction : PR.PolynomialManyOneReduction cost source target` and `<edge>NPComplete`, *using* `Karp21ReductionTransportExact.transportNPComplete`, after proving the target's NP lemma. Avoid materializing multiple alternate proof owners.

### Concrete proof obligations on the currently closest edges

- **E04/Set Packing:** finite universe of nonedge pairs, vertex-indexed sets and optional unique private tokens; `nonedgeIncidenceCorrect`, `packingPairwiseDisjointIffClique`, `packingIndexInjective`, `packingPreservesAtLeastK`, `packingSetListSizeQuadratic`, `packingBitEncodingPoly`. If duplicate empty sets collapse in a set-of-sets carrier, the reduction is invalid without an indexed-family or uniqueness repair.
- **E05/Vertex Cover:** `simpleComplementOffDiagonal`, `complementSymmetric`, `cliqueCoverFiniteCardinalityComplement` (source-written, plus `karpCliqueCoverFiniteThresholdIff` additive cardinality bridge; finite graph index model still open), `cliqueVertexCoverThresholdIff` (k↔n−k, explicit k>n cases), `complementGraphBitsQuadratic`, `cliqueVertexCoverPoly`. Existing `karpCliqueCoverSemanticEquivalence` handles the pointwise predicate, not these bounds.
- **E20/Max Cut:** historical objective identity and actual complete-graph crossing-edge proof are source-written as `completeGraphCutEqualsPartitionProduct`; historic signed PARTITION `2A=T` iff equal sides is source-written as `historicalPartitionEquationIffBalanced`. The **new scaled integer route** source-writes `scaledThresholdIffBalanced`, `signedPartitionScaledCutInstanceIff`, `totalPartitionPositiveCutIff`, and `positiveTargetThresholdCertified`, including zero-total fixed YES and original positive MAX CUT threshold domain, with no ceiling. **Unpaid exact owners:** `scaledCompleteGraphEdgeListFaithful`, `scaledGraphCanonicalWordEncoding`, `scaledGraphMalformedInputPolicy`, `scaledSignedWeightBitBound`, `scaledPartitionGraphMachineClock`, `e20EncodedPolynomialReduction`, `weightedMaxCutInNP`. The source-written modules still need Agda kernel checking; Python's 23,436 finite cases are secondary evidence.
- **E19/signed Knapsack:** `signedSubsetSumDigitPairSound`, `signedSubsetSumDigitPairComplete`, `signedSubsetSumNoCarry`, `signedSubsetSumEncodingPolynomialBits`, `positiveSubsetSumPartitionIff`, `signedKnapsackPartitionCompositeIff`. The pure two-extra-number Karp construction only follows after a positive normalization for signed source input.\n- **E01/Binary IP:** `binaryClauseInequalityIff`, `slackVariableBound`, `inequalityToEqualitiesIff`, `satToBinaryIPWitnessEquivalence`, `binaryCoefficientBitCost`.
- **E03/SAT→3SAT:** `tseitinExtensionIff` (existential rather than unique unless actually proved), `threeSATWidthBound`, `threeSATClausesLinear`, `threeSATCompilerCost`, `threeSATSharedOpenAISemantics` (cross-repo exact literal identity only once proved).

## E. Eight follow-on topics / exact external boundaries

These are *not* extra nodes in Karp's 21. Keep as lanes consuming common graph/NP interfaces.

| Lane | Exact target declarations | In-repo donors and non-conflation |
| --- | --- | --- |
| X01 Integer programming optimisation | `binaryIPFeasibleIffKarp`, `ipObjectiveDoesNotChangeFeasibility`, `lpRelaxationDirection`, `totalUnimodularityIntegralityUnderHypotheses` | Karp's N02 is **feasibility**. LP, integer optimisation, and TUM each require additional hypotheses |
| X02 Set packing optimisation | `maximumPackingObjective`, `packingCliqueThresholdIff`, `packingApproximationRatioBridge` | E04 supplies decision hardness, *not* approximation hardness |
| X03 Vertex cover optimisation | `minimumVertexCoverObjective`, `minimumCoverComplementMaximumClique`, `vertexCoverGapSameObjectWithOAI` | upstream `openai/math/lean/OAI/Computability/VertexCover/Main.lean` theorem `OAI.VertexCover.every_fixed_factor_below_two`: separate α<2 approximation-gap donor |
| X04 Job-shop scheduling | `jobShopInstance`, `jobShopScheduleSoundComplete`, `jobSequencingEmbeddingHypotheses`, `jobShopFeasibilityCost` | Karp N19 is single-machine job sequencing; never rename it Job-shop |
| X05 MAX CUT/APX | `maxCutDecisionOptimizationBridge`, `maxCutNonnegativeFiniteApproxObjective`, `maxCutGapSameObjectWithOAI`, `maxCutGoemansWilliamsonRatioCertificate` | upstream `OAI.OptimalMaxCut.main` is gap/hardness for unweighted finite simple graphs, not E20; DASHI #1438 27-grid example is finite |
| X06 Minimum k-cut | `kCutPartitionSound`, `kCutObjective`, `minSTCutIsTerminalConstrainedTwoCut`, `fixedKPolynomialWithCost`, `variableKDecisionHardness` | separate MINIMUM objective; nonnegative capacities; k=2 *global* cut is not an s-t mincut without specified terminals |
| X07 APX | `NPOObjectiveEncoding`, `approxFactorValid`, `apReductionPreservesApproxGuarantee`, `lReductionPreservesGap`, `apxMaxCutMembership`, `apxVertexCoverMembership` | zero-optimum, negative-weight, minimization/maximization, fixed-factor and PTAS domains explicit. Normal many-one reductions do not imply approximation preservation |
| X08 Ford–Fulkerson | `residualCapacityNonnegative`, `augmentPathPreservesFlowFeasibility`, `augmentRaisesFlowValue`, `noAugmentingPathProducesCut`, `flowValueLeqCutCapacity`, `maxFlowMinCutEquality`, `edmondsKarpBFSRuntimePolynomial` | no same-object algorithm found on indexed `dashi_agda` master; `NetworkFlowCapacityCongestionExact` is toy; Bellman–Ford shortest paths is unrelated |

**Historical/algorithmic caveats:** Karp's `MAX CUT` accepts signed weights in its original formulation; standard approximation theory generally assumes nonnegative edges and nonnegative optimum. Minimum k-cut is polynomial for fixed k and NP-hard when variable; an `O(n^{f(k)})` guarantee is not FPT. Ford–Fulkerson with integer capacities yields a bounded number of unit augmentations but may be pseudo-polynomial in binary capacity; Edmonds–Karp's BFS selection supports `O(V E²)`.

## 2026-11-01 AO / eigen / ITIR–SLR–SensibLaw cross-repository MAX CUT audit (DASHI-only implementation)

**Request boundary:** do not implement in ITIR-suite, SLR or SensibLaw; use their recent PRs as provenance/queue/evidence guidance. Golden proof code and exact remaining proof lemmas stay here in `chboishabba/dashi_agda`, PR #1445.

### The three genuinely different "max-cuts" (do not conflate)

1. **Literal Karp (1972) weighted MAX CUT (E20/N21):** finite undirected edges with *signed* integer weights and a positive integer decision threshold; a Boolean bipartition is a witness. The formalization uses `Karp21FiniteWeightedMaxCutVerifierExact.agda` and `Karp21PartitionScaledInstanceExact.agda`.
2. **Finite grid max-cut donor:** DASHI PR [#1438](https://github.com/chboishabba/dashi_agda/pull/1438), `DASHI/Combinatorics/GraphColouring369PantsWeightedMaxCutExact.agda`, establishes that a native checkerboard cut saturates all 54 **enumerated native grid edges** with *nonnegative Nat* weights. It is a **special bipartite instance** and does NOT imply a general exact/max-cut algorithm or signed-Laplacian positivity. The same PR's `TrialecticGraphWaveConsumerLossCutExact` exhibits a concrete C3 orbit-averaging collision that destroys a directed edge consumer; averaged spectral fingerprints do not determine every directed edge.
3. **AO/Pareto/snowball proof-frontier "max-cut":** task dependency and typed no-meet scheduling; **NOT** Karp's Max-Cut optimization problem. DASHI PR [#1415](https://github.com/chboishabba/dashi_agda/pull/1415) `WorldEigenResidualStratification` separates world, macro-eigen, sub-eigen and fibre; PR [#1416](https://github.com/chboishabba/dashi_agda/pull/1416) `HierarchicalSpectralParetoExact` establishes capacity/order boundaries and explicitly denies proof authority from alpha priority. PR [#1417](https://github.com/chboishabba/dashi_agda/pull/1417) covers topic-conductor costs; downstream Lean mirror [#102](https://github.com/chboishabba/dashi_lean4/pull/102) documents K=50/K=100 truncations, Fin 20 schedules, discrete Laplacian cut witness and *bounded* SDP receipt, **not** the Goemans–Williamson ratio or physical YM/NS equations. The golden `CombinatorialMaxCutPhysicsAlignmentExact` is referenced by that donor but was not found on `master` in this audit, so no source import, implicit attribution, or independent Agda proof receipt is claimed.

### Native signed spectral mathematical bridge (implemented **only in PR #1445**)

`Karp21SignedLaplacianCutExact.agda` imports the **actual source-owned N21 signed finite edge-list objective** and defines `spin false=-1`, `spin true=+1`. The lemma chain is:
- `spinGapTrueTrue`, `spinGapFalseFalse`, `spinGapTrueFalse`, `spinGapFalseTrue` plus `fourCutEqualsSpinQuadratic`: exact four-case Boolean ↔ integer spin-energy equality for every signed weight `w`.
- `edgeContributionMatchesBitCut`, `edgeCutEqualsSpinQuadratic` and **`karpCutEqualsSignedLaplacianQuadratic`**: structural induction over the same literal finite edge list, proving
  `4*edgeListCutValue(E,b)=Σ_(e∈E) w_e*(s_first(e)-s_second(e))²`.
  This is the unnormalised signed graph-Laplacian quadratic evaluated on a ±1 signal; edge direction, self-loop assumptions, signed weight and duplicate-edge identity are retained. **Do not** insert an extra factor 1/2 or import a positive-semidefinite approximation theorem without its hypotheses.
- `lookupFlippedLabels`, `signedMaxCutGlobalFlipInvariant`, `signedLaplacianGlobalFlipInvariant`, `positiveThresholdAcceptanceGlobalFlip`: exact global Z₂/complement parity (gauge) symmetry on **all signed weights**; saves a factor two in exhaustive *search* with a nonempty-graph representative guard but is not a polynomial algorithm for general MAX CUT.
- `negativeEdgeSignedQuadratic` / `unrestrictedSignedLaplacianNotPSD`: one edge `w=-1`, labels opposite, yielding `Q=-4`; the latter is a constructive contradiction of universal signed PSD, using integer Boolean-order reflection. Therefore the signed Karp quadratic is **not** generally positive semidefinite, and the nonnegative-weight donor in #1438 / standard Goemans–Williamson hypotheses cannot be promoted without a separately certified nonnegative-weight restriction.
- `scripts/check_karp_signed_laplacian.py` independently enumerates all signed-weight undirected complete-edge subsets on up to four vertices, all labelings, the ±1 quadratic, global flip, positive decision thresholds and the negative-edge counterexample. It is now invoked by `run_karp21_reduction_regressions.py`. An independent local replication of the identical combinatorial iteration passed **251,023** finite (graph weights, labels) cases on n=0..4, including global flip and signed quadratic; the exact committed branch script itself was not executed from a checkout. The Karp runner invokes it, but no Agda or CI receipt is claimed.

**Urgent exact next lemmas** to turn this mathematical bridge into certified Karp E20/N21, not another conceptual roadmap:
- `e20CompleteGraphEdgesFiniteIndexed`: build finite **canonical** undirected edge list from input signed vector without using cut witness, exactly once per unordered off-diagonal pair.
- `e20CompleteGraphToWeightedCutEdgeListIff`: prove that the constructed edge-list's cut value equals the source triangular `4*c_i*c_j` cut for every `Vec Bool n`, including negative and zero weights.
- `e20GraphThresholdPositiveAndSignedCost`: reuse `totalPartitionPositiveCutIff`; establish actual positive W target and integer bit-length/multiplication/sum bounds, including `T=0` fixed YES.
- `n21SignedGraphCanonicalCodec`, `n21FiniteCutCertificateCodec`, `n21SignedSumVerifierMachineClock`: make the finite N21 `verifyWeightedMaxCut` into `PR.InNP` over the repo's shared binary Word with malformed-word policy and **real** polynomial time.
- `e20EncodedPolynomialReduction` on `PR.PolynomialManyOneReduction`, sourced from the existing heterogeneous proof compiler with real encoded time cost.
- **General spectral restrictions:** `signedVsNonnegativeLaplacianDomain` and `goemansWilliamsonNonnegativeInstanceIff` are *conditional* source/typing tasks. Proving a special 27-grid optimality theorem or obtaining an eigenvector **does not** discharge E20 reduction, general cut optimization, or an approximation-ratio theorem.

### Cross-repo receipt/authority reuse, no external code writes

- [ITIR-suite #20](https://github.com/chboishabba/ITIR-suite/pull/20) `da51_slr_formal_evidence_artifact_contract_v1_20261017.md`: a Karp proof completion must bind obligation identity, exact statement digest, checker/dependency revision and result kind, not just a matching symbol, AO candidate or DA51 label. [ITIR #63](https://github.com/chboishabba/ITIR-suite/pull/63) explicitly classifies AO Pareto/max-cut scheduling as candidate work and kernel checking as separate.
- [ITIR #70](https://github.com/chboishabba/ITIR-suite/pull/70) and [SLR #76](https://github.com/chboishabba/slr/pull/76) govern source-pinned epistemic deliberation and distinguish candidate assertions/authority from verified source; their Wikidata governance graph is **not** a Karp cut graph.
- [SLR #75](https://github.com/chboishabba/slr/pull/75) adds candidate-only protected fleet grouping and a fail-closed formal-tool handoff requiring authenticated isolated kernel check, exact source/artifact/checker/dependency digests and independent success. Its receipt model helps prevent false `0/20 → 20/20` promotions.
- [SensibLaw #508](https://github.com/chboishabba/SensibLaw/pull/508) content SHA-256/idempotency identity; [#510](https://github.com/chboishabba/SensibLaw/pull/510) content/profile/version-scoped cache keys; [#509](https://github.com/chboishabba/SensibLaw/pull/509) nested spectral/eigen progress as *observation* only. These support provenance and efficient duplicate lookup; none supply semantic equivalence or a Karp reduction.
- [DASHI `PNFSpectralFieldGraph.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Interop/PNFSpectralFieldGraph.agda) already has signed residual severity and typed edge-source evidence; its structural origin classes **do not** by themselves witness an undirected finite labelled Karp graph with distinct endpoints, canonical weights and objective correspondence.
- **Attribution/promotion:** Cook 1971 ↔ SAT root, Karp 1972 ↔ historic E01–E20, standard algebra `4cut=Q` ↔ signed graph formulation, DASHI source owner ↔ newly written specific lemmas. OpenAI `OAI.OptimalMaxCut.main` in Lean donor [#78](https://github.com/chboishabba/dashi_lean4/pull/78) concerns different (gap/approximation) variants. Distinguish original theorem, handwritten proof source, finite tested code, independently checked kernel theorem, empirical receipt and scheduling heuristic.

**All remaining K00a–K00j, E01–E20, N01–N21 and X01–X08 remain in earlier sections.** Do not drop the other 19 historical reductions because E20 now has a Laplacian bridge. Current Agda receipt count: **0/20** new complete costed direct reductions; **0/21** new concrete NP-completeness conclusions. This pass did not run CI or Agda and does not claim a proof of P≠NP.

### E20 signed graph scaling/list decomposition (same indexed edge object)

`Karp21SignedGraphScaleAndAppendExact.agda` (imported in `Karp21Everything.agda`) now proves **three additional universal finite-graph laws** from the actual N21 signed weighted edge carrier:
- `edgeListCutAppend`: `cut(E++F, bits)=cut(E,bits)+cut(F,bits)`, preserving edge multiplicities and weight signs.
- `scaleEdgeFourContribution` / `scaleEdgeListFourCut`: changing **only** each edge's signed weight to `4*w`, keeping its original `Fin n` endpoints and off-diagonal proof, yields `cut(scale4(E),bits)=4*cut(E,bits)` for **every** finite graph and Boolean label vector.
- `scaledSignedGraphCutEqualsSpinQuadratic`: exact same-object weld of the E20 scaled finite-edge-list graph objective to the signed ±1 Laplacian quadratic (from `Karp21SignedLaplacianCutExact`) on precisely the unscaled source edges; no unsupported spectral-eigen positive definiteness or linear-time algorithm inferred.

This removes another purely semantic E20 multiplier and graph-edge-sum gap, but leaves one crucial **unpaid** construction: `e20CompleteGraphEdgesFiniteIndexed` and its `e20CompleteGraphToWeightedCutEdgeListIff` tying the **original signed PARTITION list** to the unique pairwise indexed graph without access to a cut witness. This is followed by actual canonical signed graph `Word` coding and a polynomial machine clock. The source-written lemmas still need pinned Agda kernel checking, as do all other Karp edges and NP-membership witnesses.

## 2026-11-01 PNF / signed-PSD / SSP-ternary / Cheeger same-object steelman + E20 graph closure

### Actual PNF owners discovered (not merely AO spectral metadata)

**Checked *source archaeology*, not a new Agda compiler run:** the existing master files are `DASHI/Interop/PNFSpectralFieldGraph.agda`, `PNFHodgeResidualTopology.agda`, `PNFSignedResidualDelta0Exact.agda`, `PNFTernaryCycleSpectralExact.agda`, `PNFSignedResidualDelta0Regression.agda`, `SpectralOperatorShapeCore.agda`, and `DASHI/Physics/YangMills/BalabanReversibleRGCheegerSpectralGapExact.agda`. The PNF graph owner distinguishes **partial residual**, **noTypedMeet**, **contradiction**, source/provenance/time edges, signed residual weight severity, and diagnostic-only higher Hodge layers. This is NOT equivalent to a freely chosen Karp graph weight or to a statement's semantic truth. The literal PNF `Δ₀=BᵀWB` on its canonical triangle has edges **0→1 partial(+1), 1→2 noTypedMeet(+3), 2→0 contradiction(−9)**; the existing `signedIncidenceEnergyIdentity` and `canonicalSignedIndefiniteWitness` prove the exact signed incidence quadratic and opposite-sign zero-sum modes. `PNFTernaryCycleSpectralExact` is the distinct unsigned C3 operator, NOT that full weighted PNF Δ₀. The Lawler–Sokal Cheeger owner is an RG **Markov** conductance/spectral-gap conditional with different hypotheses; it cannot discharge unsigned dual Cheeger, signed graph Cheeger, or Karp NP-completeness without real graph/measure same-object bridges.

**New Agda PNF adapter:** `Karp21PNFSignedTriangleSameObjectExact.agda` imports those **actual PNF** source owners, extracts each weight through `Hodge.graphWeight` and the original magnitudes, constructs an actual three-edge undirected `Fin 3` Karp graph with off-diagonal proof, and source-writes `pnfLiteralSignedDelta0CutIdentity`:
`4*Cut(typedPNFtriangle,b)=spin(b)ᵀ·PNF.signedResidualDelta0(spin(b))` for each of eight binary assignments. This is the precise finite bridge to the original PNF signed-weight incidence operator. Conversion to undirected Karp edges retains weight/endpoint data, **not** the full directed/provenance/authority semantics: those must stay attached to the PNF source or be packaged as extra typed receipts. It does not imply an Agda kernel check or an external policy truth decision.

### Real signed graph objects and **optimization directions**

| Object and edge semantics | Finite spin edge term | What actually gets optimized | Proof state |
| --- | --- | --- | --- |
| **Karp signed MAX CUT** (Karp 1972) | `w*[a≠b]`; `4Cut=Σw*(s_i−s_j)²` | **MAX** signed cut; negative edges penalize crossing | Prior `Karp21SignedLaplacianCutExact` source-written |
| **Literal signed-weight PNF incidence Δ₀** (Chung 1997 vocabulary, DASHI PNF original owner) | `w*(x_i−x_j)²`, with PNF signed -9 contradiction edge | Indefinite signed evidence-energy diagnostic; **no automatic semantic authority** | Source PNF `signedIncidenceEnergyIdentity`, new exact binary `pnfLiteralSignedDelta0CutIdentity` |
| **PSD signed-clustering/frustration Laplacian** `D_|W|−W` (Kunegis et al. 2010 and signed-balance sources) | `|w|*(s_i−sign(w)*s_j)²` | **MIN** frustration for attraction-positive / repulsion-negative signed clustering | New `Karp21SignedFrustrationBidiExact` Boolean finite graph energy |
| **SSP ternary partial cut** (original DASHI `SSPTritCarrier`) | `w*(x_i−x_j)²`, gaps 0/1/4 | Explicit **induced active** + **neutral bleed** signed energies; not Karp's binary decision language | New `Karp21SSPTernaryMaskedCutExact` finite carrier |
| **Unsigned/nonnegative signless 1-Laplacian** (Shao–Yang–Zhang 2016 preprint / 2025 publication) | `|x_i+x_j|` with **Nat nonnegative** magnitude | Different nonlinear dual Cheeger objective; requires degree normalization and independent eigen/subgradient/ratio hypotheses | New `Karp21SSPDualCheegerSignlessOneExact` finite 9-case table/list additivity, not a full Cheeger theorem |

The key affine signed-graph identity for fixed edges and labels is **`frustration(E,b) = cutSigned(E,b) + Σ_{e:w_e<0}|w_e|`**. The added `Karp21SignedFrustrationBidiExact.signedMaxCutFrustrationAffineBidi` and `signedPSDSpinIsAffineMaxCutScore` source-write this over every signed finite indexed edge list, with exact Boolean `4*frustration=correctedSignedPSDSpinEnergy`. Therefore the **same graph's** `MAX signed Cut` is `MAX frustration`, *not* the `MIN frustration` for repulsive negative edges. A negative weight has a perfectly coherent signed-graph meaning but **does not imply repulsion in the original signed Karp MAX objective**. The ordinary signed-weight `BᵀWB` becomes indefinite, but the `D_|W|−W` corrected-gap operator is PSD; this does **not** mean a finite normalized Rayleigh/SDP relaxation ceases to have a minimum, only that unqualified PSD/Cheeger theorems no longer apply to the *indefinite* operator. An unconstrained indefinite real quadratic can be unbounded below, while finite/discrete ±1 assignments and unit-norm spectral problems are bounded. This distinction is mathematical, not merely terminology.

**Ternary decomposition:** `Karp21SSPTernaryMaskedCutExact` reuses **the original `DASHI.Foundations.SSPTritCarrier`**, not a new ternary enum, and proves `ternaryEnergyExactlyInducedPlusBleed` for *all signed graphs* and `binaryTernaryEdgeListSpecialization` back to the prior binary signed Laplacian. A masked active-zero edge contributes **`w`** (not zero); the cut of the induced active subgraph is `Q_induced` while the old full graph's ternary energy is `Q_induced+Q_bleed`. In particular zero does **not** automatically create an ordinary 3-way cut or a pure "don't-care" graph deletion. `Karp21SSPDualCheegerSignlessOneExact` separately records the `|x_i+x_j|` table on SSP trits with natural **nonnegative** magnitudes and its list additivity. `x=(+1,+1)` gives ordinary gap-square 0 and signless-one value 2: they are **not the same energy** and an SSP extension does *not* force replacing every quadratic Karp verifier with absolute-value/subgradient arithmetic. It only creates a separate target family.

**Source roots/conditional spectral claims:** Fan R. K. Chung, *Spectral Graph Theory* (AMS 1997, DOI 10.1090/cbms/092); J. Kunegis et al., *Spectral Analysis of Signed Graphs for Clustering, Prediction and Visualization* (SDM 2010, DOI 10.1137/1.9781611972801.49); F. Bauer, B. Hua, J. Jost, *The dual Cheeger constant and spectra of infinite graphs* (2012, arXiv:1207.3410); F. M. Atay and S. Liu, *Cheeger constants, structural balance, and spectral clustering analysis for signed graphs* (2020, DOI 10.1016/j.disc.2019.111616); S. Shao, C. Yang, D. Zhang, *Dual Cheeger constants, signless 1-Laplacians and maxcut* (2016 preprint, 2025 SCIENCE CHINA Mathematics, DOI 10.1007/s11425-024-2376-2). Do not attach their worst-case **0.769** restricted recursive spectral-algorithm ceiling to arbitrary signed Karp cut, the PNF evidence triangle or the *non-normalized* indefinite Δ₀. No signed/unsigned degree normalization, Cheeger ratio, denominator positivity or eigenvalue interval `[0,2]` has been proven for those consumers.

### Previously unpaid E20 graph construction — now source-written, including the existential list→indexed cut bridge

1. `Karp21FiniteCompleteGraphGeneratorExact.agda`: `HeadLink n` retains each `Fin n` destination independently of Boolean cut choice. `headLinks`, `emitHeadLink`, `completePairEdges` generate the **upper triangle only** with off-diagonal proofs; `headPairCount` and `completePairCount` show the exact `n(n-1)/2` triangular edge count; `completeScaledPairEdges` multiplies signed weights by 4. Pair-uniqueness as an explicit proof-level all-different lemma, canonical positive `GraphWord` serializer and machine-cost bound remain unverified.
2. `Karp21FiniteCompleteGraphObjectiveExact.agda`: `headLinkCutShift`, `headLinkCutMatchesHistoricalCross`, `emitHeadLinksScore`, `tailGraphPromotionPreservesCut`, and the requested **`e20CompleteGraphToWeightedCutEdgeListIff`** prove the constructed graph's cut score equals the historical `completeGraphCut` over a *position-preserving annotated Vec*, for **every** assignment and signed input, empty/duplicate/zero elements included. `e20ScaledIndexedGraphExactCut` transports 4× edge scaling to the exact objective.
3. `Karp21SignedPartitionIndexedGraphDecisionExact.agda`: `vectorOfList` / `labelsOfSelection` convert original source List and dependent Selection to same-length vectors; `annotatedListIsSameObject` proves exact per-position preservation; `indexedSignedGraphCutSourceScore` welds the actual indexed graph to the **original** source partition expression; `karpPartitionActualIndexedGraphYESIff` proves full **existential** yes-iff; `sourcePartitionIndexedPositiveTargetIff` retains Karp's required positive-threshold zero/nonzero source guard without ceiling. A real fixed unit-edge `Cut.WeightedCutGraph` now exists in `Karp21SignedPartitionActualGraphYESExact` with existential witness transport; the canonical **Word parser and machine-clock** component remains unconstructed.

**Finite independent numerical controls**: An independent Python replication verified 251,023 signed graph/label cases for corrected PSD frustration and **111,111** signed Partition/graph/label combinations for n=0..5, exact 4×cut = 4A(T−A) = T²−(A−B)², positive threshold and the zero-total exception. `scripts/check_karp_pnf_signed_ternary.py` is committed and invoked by the Karp runner; the exact GitHub branch script itself was not run from a checkout. Neither Python totals nor source-written Agda imply kernel acceptance.

**Updated precise next high-alpha cut (do not re-open the completed source-written seam as a placeholder):** `e20IndexedPairUniqueAndComplete` (now source-written with no-repeat address list and weighted edge-list correspondence; requires Agda check), `e20PositiveUnitGraphRealization` (actual 2-node target object at total zero), `e20IndexedTargetGraphWordsRoundtrip`, `e20MalformedWordPolicy`, `e20GraphMachinePolynomialClock`, and `e20EncodedPolynomialReduction` under `PR.PolynomialCostModel`; on the NP side `n21CanonicalGraphWord`, `n21CertificateWord`, `n21SignedSumBitBound`, `n21PolynomialVerifierClock`, `n21InNP`. K00 uniform original Cook–Levin + E01–E19 concrete costed maps + N01–N20 InNP remain open. This tranche wrote no implementation into ITIR, SLR or SensibLaw.

**Status gate:** All these new Agda theorem names are source-written with no run of the pinned Agda kernel. Until that check and actual costed Word reductions are available, preserve the explicit **0/20 newly kernel-certified concrete reduction** and **0/21 newly kernel-certified NP-complete result** counts. Explicitly distinguish original mathematical theorems, PNF source operators, new typed proof terms, independently executed finite controls and checker receipts.

### E20 actual positive-threshold graph object and existential witness transport

`Karp21SignedPartitionActualGraphYESExact.agda`, imported by the focused root, builds literal `Cut.WeightedCutGraph` objects for **both** Karp branches: `fixedUnitGraph` (two distinct `Fin 2` vertices, one unit edge, threshold +1 and actual `fixedUnitGraphAccepts` Boolean-cut certificate) and `sourceIndexedWeightedGraph parts nonzero` (new signed upper-triangular `4*c_i*c_j` edge list with exact `T²>0` certificate). `choiceFromLabels` and `choiceLabelsRoundTrip` close **both** directions of the List `Selection` ↔ `Vec Bool n` cut-certificate transport, so no target witness is lost. `sourceIndexedGraphAcceptsIff` links the indexed decision to `Cut.WeightedMaxCutYES` on the same graph, and `sourcePartitionActualPositiveGraphIff` is the full original signed PARTITION YES iff this genuine **positive-threshold finite weighted graph's** existential YES predicate, with exceptional zero-total covered by the fixed graph. The constructor depends only on original input, never its selected witness.

**This advances E20's real mathematical max-cut.** Remaining E20 before costed NP-hardness: `e20IndexedPairUniqueAndComplete` beyond proven triangular cardinality; `e20GraphPackedWordRoundtrip`; `e20MalformedWordRejectOrCanonicalNo`; `e20SignedMulAdditionBinaryBitCost`; `e20ConcretePolynomialTransducerMachineClock`; `e20ConcreteManyOneReduction`. On N21: graph/labels packed parsers, `n21CutSumBinaryClock`, `n21InNP`. **All 21 end-to-end NP-completeness theorems remain OPEN** pending Cook–Levin root, 20 costed reductions, 21 NP bounds, Agda kernel and independent receipts. No CI was run.

## F. Priority cut / dependency order (Pareto and snowball)

**Tier 0 — proof-system blockers (must precede any "21 done" claim):**
- K00a–K00j, especially concrete word encoding, actual cost model, Cook–Levin and malformed-input handling. Existing `PR.InNP` and `PR.NPComplete` records are typed *interfaces*, not globally supplied proofs.

**Tier 1 — shortest reusable graph triangle:**
- E03 and E02 SAT/CNF bridges → E04 CLIQUE/SET PACKING → E05 CLIQUE/NODE COVER → E06 SET COVER.
- Aim first for the concrete *E05* theorem using #1445's `karpCliqueCoverSemanticEquivalence`, then E04 using `karpCliquePackingSemanticEquivalence`. Build finite cardinality once and reuse it throughout vertex- and set-indexed constructions.

**Tier 2 — arithmetic terminal:**
- E17 EXACT COVER→KNAPSACK → E19 KNAPSACK→PARTITION → E20 PARTITION→MAX CUT.
- In parallel, E01 integer constraints and X01 arithmetic optimization (without conflating feasibility).
- Reuse bit-cost exact arithmetic from existing number-theory modules, not literal numerology analogies.

**Tier 3 — complete historically remaining branches:**
- E07–E10 feedback and Hamiltonian; E11–E16 colouring/clique cover/exact cover/hitting set/Steiner/3DM; E18 sequencing.

**Tier 4 — independent approximation/flow graph:**
- X03, X05, X07 consume the actual OAI Lean declarations after pinned toolchain and same-object audit; X06/X08 consume a separate finite flow network with residual arcs and conservation.
- Report Karp decision completeness separately from APX/flow and from the Clay P != NP frontier.

## G. Mechanical acceptance checklist (per lemma, per edge, per 21-node closure)

1. Source owner path and earliest actual implementation SHA/time, original author DOI/date; later source ports keep *both* provenances.
2. Well-formed and ill-formed inputs; exact instance and certificate encoding, duplicate-index, parity, empty, weight signs, loop convention; prove parser roundtrip.
3. Explicit `forward` and `backward` proof terms, no `postulate`, `sorry`, unconstrained boolean status, or `Set` field used as a disguised theorem.
4. Actual polynomial **machine** steps plus output-bit budget. Do not infer a cost theorem merely from a total Agda function.
5. Finite exhaustive regression on small instances, including at least one YES/NO per edge and malformed controls, is *secondary* evidence.
6. `scripts/run_agda29_parallel_check.sh DASHI/Mathematics/Complexity/Karp21Everything.agda` for draft; repository-pinned Track A Agda for final acceptance. Do not claim either passed unless an actual run/receipt is attached.
7. Same-object Agda ↔ Lean bridge (if used), pinned original source, kernel/axiom report, regression and TOE consumer after successful independent verification.
8. Update this roadmap with exact lemma names and close only a lemma whose file/line and kernel receipt can be inspected.

## H. Source bibliography / exact URLs

- Cook (1971): https://doi.org/10.1145/800157.805047
- Karp (1972): https://doi.org/10.1007/978-1-4684-2001-2_9\n- Karp 1972 source PDF (pages 96–100 for the list, reduction diagram and E20): https://cgi.di.uoa.gr/~sgk/teaching/grad/handouts/karp.pdf
- Zuckerman (1996), *On Unapproximable Versions of NP-Complete Problems*, SIAM J. Comput. 25(6):1293–1304, DOI 10.1137/S0097539794266407: applies additional constraints to 21 historical problem families; **not** the claim that their ordinary variants all have the same approximation difficulty.\n- Karp original/tree overview: https://en.wikipedia.org/wiki/Karp%27s_21_NP-complete_problems
- Zuckerman constrained approximation distinction: https://doi.org/10.1137/S0097539794266407
- OpenAI original Max-Cut Lean: https://github.com/openai/math/blob/main/lean/OAI/Computability/MaxCut/Main.lean
- OpenAI original Vertex Cover Lean: https://github.com/openai/math/blob/main/lean/OAI/Computability/VertexCover/Main.lean
- In-repo Lean OpenAI atlas PR #78: https://github.com/chboishabba/dashi_lean4/pull/78
- In-repo finite same-object Max-Cut graph: in `dashi_agda` PR #1438 (not a general NP-completeness proof).
- Ford–Fulkerson background: https://en.wikipedia.org/wiki/Ford%E2%80%93Fulkerson_algorithm
- Minimum k-cut distinction: https://en.wikipedia.org/wiki/Minimum_k-cut
