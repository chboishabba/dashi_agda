# Exact remaining lemma and certificate register — DASHI/OpenAI SAT / corpus / adjacent max-cuts

**Audited 31 October 2026; addendum 1 November 2026.** Authority: original Golden Agda source owners, Lean downstream, upstream `openai/math`, actual PR branches. This register is a *live statement-and-status inventory*, not a declaration that every source term has been checked.

**Critical distinction:** `SOURCE-WRITTEN` means source text exists on a PR; `KERNEL` means an exact toolchain independently accepted the proof. This run had **no Agda/Lean compiler** and the GitHub runner at the inspected head offered no existing result. Nothing in this register promotes source-only P1/P2 into theorem acceptance.

**Primary bounded task statement**: For every original DAG circuit `C` with `n` inputs and `g` gates, construct and validate the original counted 3-CNF on exactly `n+g` finite coordinates; optional 1/2/3-clauses yields ≤`3g+1` source list clauses. Prove `countCompiledCNF(C) = countAcceptedCircuitInputs(C)`; normalize without losing counts to the *actual* OAI `SAT.CNF (Fin (n+g))`; produce exact `Encoding.encodeCNF` bits and faithfully consume original OAI fixed primitive counting/SAT runtime and all-prefix space theorem.

**Selected existing reusable numerology/structure**: 369 / 3×3 trialectic axes, C3/S3 orbit group actions, 27-function / 11-orbit / 7+4 eigenspace, 27-vertex weighted checkerboard graph, radix/CRT/eisenstein λ⁹, sieve/primecount, and finite reflection parity. These are **typed donors** or test harnesses only where an explicit index/coordinate/equivariance theorem exists; do not infer SAT hardness, arithmetic infinitude, RH, physical mass gaps or Monster representation from the occurrence of 3, 9, 27 or matching fingerprints.

**Unfinished normal form**: Each obligation below must carry (a) exact quantified mathematical target, (b) prior owner/first commit, (c) preconditions and target types, (d) source proof term, (e) kernel/environment receipt, (f) independent executable check when useful, (g) same-object consumer and (h) promotion boundary. The *existing* #1212 and Lean #78 code are the authoritative source of definitions; this markdown file does not override those sources.


## KERNEL — 3 exact obligations or owners

| ID | Exact task / precondition / required postcondition | Reuse owner / consumer | Evidence / missing receipt |
|---|---|---|---|
| **K00** Agda P1/P2 import spine | Run exact-head Agda typecheck of `DASHI/Research/OpenAIMath/Everything.agda` and all transitive imports, plus optional `OpenAIMathSharedTseitinOptimizedCNFExact.agda`; fix every source elaboration failure; safe/0-postulate/0-metavariable audit before Golden promotion. | `Everything.agda`, `OpenAIMathFiniteSupportedTseitinModelsExact.agda`, `OpenAIMathSharedTseitinGateCNFExact.agda`, `OpenAIMathSharedTseitinUniqueExtensionExact.agda` | UNVERIFIED — source only |
| **K01** Lean generic adapter | Compile `Integration/OpenAIMath/ListFinsetCNFTransport.lean` on pinned Lean 4.28.0/mathlib and prove no `sorry`/new axioms, then join import spine. | `ListFinsetCNFTransport.lean` | UNVERIFIED — staged source |
| **K02** Lean version-gated later adapter | Pin/migrate an *explicit separate* OAI 378 4.34.1-compatible dependency environment; compile `Upstream378FiniteCNFBridge.lean`, inspect `#print axioms`, and only then enable consumers. Never silently rewrite old 4.28 vendor commit. | `Upstream378FiniteCNFBridge.lean`, `Upstream378EncodingLengthExact.lean`, upstream `SAT.lean`/`Encoding.lean`/`SqrtLogSpace/Final.lean` | SEPARATE 7ef5c0c source pin staged and local check script exists on Lean #78; upstream 4.34.1 kernel STILL UNVERIFIED |

## ORIGINAL — 9 exact obligations or owners

| ID | Exact task / precondition / required postcondition | Reuse owner / consumer | Evidence / missing receipt |
|---|---|---|---|
| **S00** Original circuit and compiler ownership | Preserve exact `Circuit.evaluateProgram`, `evaluateGate`, `evaluateCircuit`, `Compiler.gateVariableIndex`, `programSharedConstraints`; no second circuit evaluator. | `PNotEqualsNPConcreteBooleanCircuitDAGExact.agda`, `PNotEqualsNPConcreteCircuitSharedCompilerExact.agda` | EXISTING — #1040 provenance |
| **S01** Original functional gate uniqueness | Reuse `Unique.uniqueAuxiliaryGateValues` and `Unique.uniqueUsedCoordinates` and `Existing.ProgramAssignmentRealizes` rather than a parallel induction. | `OpenAIMathSharedTseitinUniqueExtensionExact.agda`, `PNotEqualsNPConcreteCircuitSharedSemanticsExact.agda` | EXISTING SOURCE — kernel status inherited/needs checking |
| **S02** 3-bit local gate semantics and placement | `placedGateCNFOutputSound/Complete` and `compiledProgramLastGateOutputForced`; output wire is actual indexed circuit variable; unused operands in const/NOT must not create models. | `OpenAIMathSharedTseitinGateCNFExact.agda`, `CNFVariableRenamingExact.agda` | SOURCE-WRITTEN — kernel pending |
| **S03** Canonical finite vector ↔ original Cook assignment | For all `i:Fin(n+g)`, `finiteCNFToCookAssignment b (toℕ i) ≡ CNF.lookupBit b i` and input/past/fresh gate index joins, no Nat→Bool tail counting. | `OpenAIMathFiniteSupportedTseitinModelsExact.agda` `finiteCNFToCookLookup`, `finiteCNFCookPriorWireExact`, `finiteCNFCookNewestGateExact` | SOURCE-WRITTEN — kernel pending |
| **S04** Chronological ↔ newest-first gate order | Use stdlib `Fin.opposite` and `FinP.opposite-involutive`, `FiniteSource.chronologicalGateNumberExact`, `finiteCookChronologicalGateExact`; confirm original `Compiler.gateVariableIndex` equation literally. | `Data.Fin.Base/Properties`, `OpenAIMathFiniteSupportedTseitinModelsExact.agda` | SOURCE-WRITTEN — kernel pending |
| **S05** Prefix preservation through appended gate | Show `finiteCNFPrefixCookAgreement`, `realizationTransportToExtendedBits` and reverse `realizationTransportToPrefixBits` for every original used index. | `OpenAIMathFiniteSupportedTseitinModelsExact.agda`, `Original.extendEarlierFin`, `Rename.pullbackLookup` | SOURCE-WRITTEN — kernel pending |
| **S06** Whole-program constraints ⇔ original circuit gate evaluation | Prove `globalPlacedProgramGivesOriginalRealization` and `globalOriginalRealizationGivesPlacedValid` by reusing #1040 `ProgramAssignmentRealizes` and earlier uniqueness owner. | `OpenAIMathFiniteSupportedTseitinModelsExact.agda` | SOURCE-WRITTEN — kernel pending |
| **S07** Whole CNF SAT soundness/completeness | `originalPlacedCNFImpliesAcceptedInput` and `canonicalGlobalPlacedCNFCompleteness` for actual recursively compiled CNF, include gate-free and repeated-wire cases. | `OpenAIMathFiniteSupportedTseitinModelsExact.agda` | SOURCE-WRITTEN — kernel pending |
| **S08** Canonical extension and uniqueness on finite support | `originalPlacedCNFModelCanonical`, `originalPlacedCNFModelsUniqueForInputs`, `canonicalOriginalProgramInputRoundTrip`; reuse `Unique.uniqueUsedCoordinates`, `Fin.splitAt/join` not new carrier. | `OpenAIMathFiniteSupportedTseitinModelsExact.agda`, `OpenAIMathSharedTseitinUniqueExtensionExact.agda` | SOURCE-WRITTEN — kernel pending |

## COUNT — 5 exact obligations or owners

| ID | Exact task / precondition / required postcondition | Reuse owner / consumer | Evidence / missing receipt |
|---|---|---|---|
| **N00** Fubini sum splitting actual global assignment | `sumOriginalFiniteCNFBitsAppend` over input/gate suffix, with no mismatch to `Canonical.appendBits` and zero dimensions. | `OpenAIMathFiniteSupportedTseitinModelsExact.agda` | SOURCE-WRITTEN — kernel pending |
| **N01** Exactly-one gate extension counted as one | `sumOriginalFiniteCNFBitsUnique` plus empty-gate and rejected-fibre (`sumOriginalFiniteCNFBitsZero`) proofs. | `OpenAIMathFiniteSupportedTseitinModelsExact.agda` | SOURCE-WRITTEN — kernel pending |
| **N02** Per-input compiled gate fibre count equals circuit acceptance | `originalOneOrZeroGateFibreCount`: for every input `x`, sum over all gate bits of `indicator (CNF C (x,g)) = indicator (evaluateCircuit C x)`.  | `OpenAIMathFiniteSupportedTseitinModelsExact.agda` | SOURCE-WRITTEN — kernel pending |
| **N03** Original whole-CNF #SAT equals original input #SAT | `originalGlobalCNFCountExact : originalCompiledCNFModelCount circuit ≡ countAcceptedCircuitInputs circuit`. Its proof must actually typecheck from N00/N01/N02. | `OpenAIMathFiniteSupportedTseitinModelsExact.agda` | SOURCE-WRITTEN — kernel pending |
| **N04** Optional optimized 1/2/3-clause compiler exact count | `optCircuitEqualsOriginal`, `optCircuitThreeClauseBudget`, `optGlobalCNFCountExact`. Exact original source LIST ≤3g+1; do not claim Finset.card equality. | `OpenAIMathSharedTseitinOptimizedCNFExact.agda` | SOURCE-WRITTEN — kernel pending |

## FINSET — 5 exact obligations or owners

| ID | Exact task / precondition / required postcondition | Reuse owner / consumer | Evidence / missing receipt |
|---|---|---|---|
| **L00** Finite clause truth under literal dedup | `ListFinsetCNFTransport.clauseSemanticsExact` and complete `cnfSemanticsExact`; polarity/variable mapping must agree with **actual** original Agda literal representation. | `ListFinsetCNFTransport.lean`, original Agda `FixedWidthTruthTableCNFExact.agda` | GENERIC SOURCE-WRITTEN, same-object mapping pending |
| **L01** Finset normalized clause count and width | `clauseNumberUpper`, `normalizedClauseWidthUpper` and concrete ≤3g+1 bound; duplicate ordered clauses can collapse only after literal normalization. | `ListFinsetCNFTransport.lean` | GENERIC SOURCE-WRITTEN — kernel pending |
| **L02** Normalize count without changing set of input valuations | `normalizedModelCountExact` for every finite assignment, specialize to actual upstream `SAT.Literal (Fin n)` (both polarity and finite variable index). | `ListFinsetCNFTransport.lean`, `Upstream378FiniteCNFBridge.lean` | STAGED — vendor/pinned kernel pending |
| **L03** Upstream `SAT.count` exactly equals source-list count | `Upstream378FiniteCNFBridge.exactUpstreamCount`: actual upstream Finset-of-Finset count, not a surrogate truth predicate. | `Upstream378FiniteCNFBridge.lean`, upstream `SAT.lean` | STAGED — vendor/pinned kernel pending |
| **L04** Bounded encoding and bit-length | `upstreamExactBitLengthBound` and `upstreamQuadraticBitLengthBound`: with `v=n+g`, `L≤v+2+(24v+28)(3g+1)≤72(v+1)^2` and `g≤v`. | `Upstream378FiniteCNFBridge.lean`, upstream `Encoding.formulaBitLength_upper` | STAGED — kernel pending |

## MACHINE — 6 exact obligations or owners

| ID | Exact task / precondition / required postcondition | Reuse owner / consumer | Evidence / missing receipt |
|---|---|---|---|
| **M00** Verified executable original DAG serialization | Define actual original `GateProgram` ↔ Python JSON frontend relation, accepting only creation-ordered earlier gate indices and *exact constructor-specific JSON keys*. Show each source gate maps to original indexed window/clauses. | `scripts/compile_dashi_circuit_openai378.py`, `Circuit.GateProgram`, original compiler | EXECUTABLE STRICT SCHEMA now staged Lean #78; Agda↔JSON typed relation and kernel proof STILL MISSING |
| **M01** Verified executable literal/polarity/Finset serializer | Prove actual finite list from M00 equals `Upstream378FiniteCNFBridge.toUpstreamCNF`; bitstream equals upstream `Encoding.encodeCNF`, including sorted numbers, unary/frame. The exact length statement must be `v+2+Σ_C (4+Σ_code (4*code+8))`. | Python frontend, Lean `Upstream378EncodingLengthExact.exactFormulaBitLength`, upstream `Encoding.lean` | EXECUTABLE exact-length assertion and source-written Lean length induction; no Lean kernel or Agda↔Lean source identity |
| **M02** Uniform source frontend primitive time | Give a concrete source→bitstream primitive-machine transducer and all-prefix runtime certificate. Reuse executed source clause bound `m≤3g+1`, ordered insertion probes ≤`6m+m(m−1)/2`, actual equality+ordering calls ≤`2(6m+m(m−1)/2)`, insertion element shifts ≤`3m+m(m−1)/2`, and exact bit-write count `L`; account for integer comparison bit costs and input parsing, not merely Python calls. | Python frontend, `PNotEqualsNPQ1ExecutedConstructionMachineExact.ExecutedQ1ConstructionRun`, `StandardSingleTapeMachineExact.standardNext`, `LocalOptimizationCompilerExact.LocalSemanticCompiler` | PARTIAL executable operation-count + exact output-bits certificate; STILL MISSING native TM trace / primitive bit-cost theorem |
| **M03** Uniform source frontend all-prefix visited space | Show each prefix of input preprocessing/serializer uses polynomially many primitive tape cells, compose with the OAI `SqrtLogSpace.exact_count_and_sat` all-prefix bound. Python `stream_original_circuit` now retains ≤`chunk_bits` pending **logical output bits**, plus input and clause lists; do not identify this with visited tape cells. | OAI `Computation/VisitedTape/Final`; existing `LocalOptimizationCompilerExact.StreamingResidencyCertificate` and `peakBoundIsLocalSum` | PARTIAL bounded streaming implementation + checkout-native regression staged; STILL MISSING original primitive machine/prefix-space proof |
| **M04** Fixed machine source-list count/SAT output | `sourceListExactCountMachine` rewrites actual machine count tape, SAT tape, time, space to source **list** model counts, same machine not new algorithm. | `Upstream378FiniteCNFBridge.lean`, upstream `Final.exact_count_and_sat` | STAGED — 4.34.1 kernel pending |
| **M05** Complete end-to-end Agda circuit count as machine tape result | Given genuine source circuit and its checked serialized compiled bitstream, compose N03/N04+L02/L03+M01-M04 into statement that tape yields original `countAcceptedCircuitInputs`. Preserve polynomial frontend and upstream complexity. | DASHI #1040/#1212; Lean #78; OAI 378 | MISSING FINAL SAME-OBJECT KERNEL COMPOSITION |

## CORPUS — 3 exact obligations or owners

| ID | Exact task / precondition / required postcondition | Reuse owner / consumer | Evidence / missing receipt |
|---|---|---|---|
| **C00** 208 upstream source-qualified declaration references | Catalogue exactly all 208 current `main_results` entries (192 comparator configurations), upstream blob `372bcd714cd3a186a9139ac8e0f3318961fb2df1`; metadata NOT 208 formal theorem ports. | Lean #78 `FullUpstreamMainResultsCatalogue.lean` | 208 declaration source index CATALOGUED AND ROW-CHECKED; 721 manuscript and 373 family indices also materialized; kernel/ports separate |
| **C01** Corpus family/discovery bridge | 721 manuscripts / 373 families current README; map manuscripts/families to 208 declarations with date/author/authority and in-repo original mathematical owner; no title-only same-object promotion. | Existing `SourceAtlas.lean` / `OpenAIMathSourceAtlasExact.agda` / full catalogue | 373 indexed, per-family source-provenance/owner comparison not fully reviewed; 101/208 subject-anchored lexical candidates (API Lean tree truncated), six source-reviewed comparator boundaries; zero certified transports |
| **C02** Full theorem imports into Golden Agda/Lean | For each desired mathematically relevant declaration: source premise/comparator, zero-sorry proof/axiom audit, exact object/typing equivalence, full kernel, consumer/attribution and stable vendor. | Lean/Agda `SourceAtlas`, upstream `formalization.yaml`, native DASHI proofs | NOT FINISHED; 208 entries ≠ 208 accepted DASHI ports |

## MATH — 8 exact obligations or owners

| ID | Exact task / precondition / required postcondition | Reuse owner / consumer | Evidence / missing receipt |
|---|---|---|---|
| **R00** Native 27-vertex weighted Max-Cut uniqueness | For strictly positive weights, prove 27-grid connectedness and only two saturated cuts up to complement in golden Agda; then construct SAME-OBJECT original 27-input source circuit for all 54 edge-XOR constraints and kernel-prove `countAcceptedCircuitInputs = 2`, transporting it to the exact 3-CNF count by N03/N04. Keep separate from unrestricted graph hardness. | Agda #1438 `GraphColouring369PantsWeightedMaxCutExact` and QID atlas | OPEN KERNEL THEOREM; independent Python large shared-DAG fixture PASS |
| **R01** Unrestricted graph Max-Cut/UGC theorem transport | Match exact variable-size graph type and gap parameter of OAI family 102, prove reduction or lemma application with original #1438 carrier *only when same object*; not from 27-node toy alone. | OAI `OAI.OptimalMaxCut.main`; native #1438; Lean #103 | OPEN SAME-OBJECT TRANSPORT |
| **R02** C3/S3 27-function orbit and 7+4 parity relation | Reuse `PolynomialC3S3...` 27→11→7 quotient and earlier positive/negative projector; prove any claimed link to graph only with explicit equivariant function/relation. 27-functions ≠ 27-vertices. | Agda #1414; original `MoonshineOrbifoldSectorProjectorExact` | PARTIAL; no Monster same-object promotion |
| **R03** Twin-prime genuine unbounded pair count jumps | Remove or discharge explicit `laterJump` assumption with actual prime-specific arithmetic estimate or alternative theorem; wheel/CRT finite residue survival alone is insufficient. | Agda #1408 `TwinPrimeConditionalUnboundedFromCountJumpsExact`, sieve/SSP/FRACTRAN donors | OPEN ANALYTIC CERTIFICATE |
| **R04** RH signed correlation and strict scalar | Pay source owner #1434 A1 carrier summation/curvature/compensation, A2 scalar and B signed-fifth eventual gap with genuine analytic estimates. Zero-free Re(s)>7/8 is not RH. | Agda #1434 `RiemannRHMaxCutTOEExact`, Lean RH donors | OPEN ANALYTIC CERTIFICATE |
| **R05** Pickover actual giant real phase sign | Certified interval enclosure for relevant real fractional phase digit at exponent 9999!, with huge arithmetic cost or sharper analytic bound. CRT/Eisenstein phase reindexing alone is not the sign. | Agda #1260 `PickoverBase99SignedTailExact` | OPEN REAL-PHASE CERTIFICATE |
| **R06** YM physical continuum/OS mass-gap construction | Discharge continuum physical measure, OS reconstruction and physical mass-gap on the actual source carrier, not only route-S conditional algebra. | Agda #1440 `YMClayDirectSourceOSMassGapFrontierExact` and prior Balaban donors | OPEN PHYSICAL/ANALYTIC CERTIFICATE |
| **R07** TOE/QID/Ibrahim/Monster 3B evidence firewall | Integrate C3/369 lattice, orbit/projector, graph/sieve roles as independent typed lemmas; preserve Ibrahim 3B priority, explicit source date, no ESD modifications and no synthetic fingerprint→same-object proof. | Agda `Unifier`, `EverythingTOESymmetryResolved369`, QID/SSP and #1414/#1438 branches | ONGOING GOVERNANCE & SAME-OBJECT OBLIGATIONS |

## 31 Oct executed graph→SAT cross-pollination and frontend normalization cost cut

**Real native source inspected**: #1438 `GraphColouring369PantsWeightedMaxCutExact.agda`, with `unitNativeGridEdges` 54 witnessed unit edges (18 for each coordinate), `checkerCutsEveryNativeEdge`, `checkerMaximumCut` and `unitWitnessTotalWeightIs54`; also existing symmetry owner `GraphColouring369PantsSymmetryCutInvariantExact.agda`. Independent Python fixture encodes **the SAME 27-vertex, 54-edge ternary adjacency**, *not* #1414's 27-function C3 conjugation quotient. The circuit shares each one of 27 negated input wires once, uses a 3-gate XOR decomposition on each of 54 edges, and 53 shared conjunction gates. Result: **27 input variables + 242 new gates = 269 finite variables; 700 source 3-CNF clauses**, exactly 700 normalized Finset-equivalent clauses for this fixture, 1,515,935 actual unary/framed encoded bits, and 188,225 ordered insertion comparisons versus the explicit 248,850 budget. The bipartite graph is connected, so there are exactly two valid all-crossing cuts, checked by BFS and 2,502 input colourings. Independent finite Python script `/mnt/data/check_27grid_oai378_sameobject_20261031.py` passed; repo checkout regression `dashi_lean4/scripts/check_openai378_27grid_maxcut_bridge.py` was committed, but exact checkout wasn't run. **The Agda theorem identifying the native finite graph witness list with this serialized source circuit, and a kernel proof of its count exactly 2, remain OPEN in R00**; no transfer of unrestricted OAI family 102 hardness.

**P4 executable real algorithm improvement**: instead of Python `sorted(set(...))`, the actual `scripts/compile_dashi_circuit_openai378.py` now uses explicit ordered scans/insertion of at most 3 literals per source clause and each normalized clause among prior normalized clauses. For `m` source clauses, the script checks that **literal+clause tuple comparison calls ≤ 6m + m(m−1)/2**; each tuple has at most 3 literal codes < 2v. This avoids an unpriced Python hashing/sorting oracle but is **not a proof of Turing-machine primitive bit-comparison cost**. Independent local Python PASS 10,735 arbitrary CNF fixtures and 2,430 original-circuit gate-template fixtures, identical normalized clauses and exact encoded bitstreams. A checked-in `scripts/check_openai378_frontend_exact.py` now targets actual checkout's frontend directly; exact GitHub copy remains UNEXECUTED until environment available. Upstream 378 `sourceRuntimeWithinQuadraticInputBudget` and `sourceVisitedSpaceWithinQuadraticInputBudget` are newly source-written Lean lemmas applying `L≤72(v+1)^2` to the SAME original machine’s formulas; **Lean kernel not run, actual source frontend machine trace/time/space still M02–M03**.

## Native resource/optimization donors discovered before building a new machine

The current default-branch Agda repository already contains these **distinct, reusable resource-proof carriers**:

- `DASHI/ComputerScience/LocalOptimizationCompilerExact.agda`: `LocalSemanticCompiler`, `wholeFoldObservationPreserved`, `LocalResidencyBound`, `StreamingWorkShape`, `StreamingResidencyCertificate`, `peakBoundIsLocalSum`. Semantic equivalence **does not pay residency**; reuse its explicit cost-vs-behavior separation.
- `DASHI/Mathematics/Complexity/PNotEqualsNPQ1ExecutedConstructionMachineExact.agda`: `Iterates`, `ExecutedQ1ConstructionRun`, original construction work/trace and state-transition certificates. This is an existing source-defined operational **construction carrier**, not a proof that the new Python OAI frontend automatically runs on that machine.
- `DASHI/Mathematics/Complexity/StandardSingleTapeMachineExact.agda`: `StandardSingleTapeMachine`, `standardNext`, `standardControlFetchWorkBound` for an actual conventional operational machine, independently from OAI `Computation.PrimitiveMachine`. A **typed simulation** and bit-time accounting are necessary before transferring P4 costs.
- `DASHI/Mathematics/Complexity/PNotEqualsNPConcreteCircuitSharedUpperBoundExact.agda`: source syntax-node upper bound (13 per original gate constraint), **not** canonical bit length nor an executable serializer cost. Use it only for distinct syntax/resource statements.
- `DASHI/ComputerScience/TriadicActiveCountPhysicalLoweringExact.agda`: total trit-popcount is not prefix-address knowledge; this supplies a negative-control pattern for not inferring every-prefix space from a whole-run count or a final bitstream size.

These were **read from actual source** in this continuation; search terms for P4 were redirected to these owner declaration names rather than creating a competing optimization/machine ontology. Remaining typed joins M02/M03 must instantiate a real source step machine and prove its simulation/cost; matching symbolic names do not constitute a machine run receipt.

## 1 November finite SAT machine-interface advance — exact acceptance boundaries

Lean PR #78 now stages the executable JSON **constructor grammar** (no ignored fields), the *exact* OAI unary/framed bit-length identity, a source-written Lean structural proof of that identity, and a bounded-chunk streaming output path. The eager and streaming paths share the source-ordered finite clause normalizer. Python test scripts have additional strict-schema, finite-assignment, exact-bit and bit-for-bit streaming checks, including the original 27-node/54-edge graph witness; **these changed scripts were not run from the exact current GitHub head**. A separate small arithmetical fixture independently checked the nested-frame identity.

For `v=n+g`, canonical normalized clause codes `C`, `m≤3g+1`, and three literals per clause:

```text
L = v+2 + Σ_(clause∈C) (4 + Σ_(code∈clause) (4*code + 8))
  ≤ v+2 + (24v+16)(3g+1)
  ≤ v+2 + (24v+28)(3g+1)
  ≤ 72(v+1)^2.
```

The exact equality is implemented on both sides as (i) an executed Python assertion over actual output bits and (ii) *source-written, not kernel-checked* Lean `Upstream378EncodingLengthExact.exactFormulaBitLength` applied to the actual `SAT.CNF (Fin v)`. The sharpened constant `16` is currently a Python arithmetic bound, not a separate accepted Lean theorem. The full M00/M01 same-object `Agda GateProgram → JSON → ordered source clauses → Finset clauses → encodeCNF` chain, primitive-machine source compiler, combined trace, and end-to-end M05 count remain OPEN. These changes do not change the 39-ID count or resolve RH, twin primes, Pickover, or physical YM.

**Executable exact acceptance to run locally (no CI needed):**
```sh
# Lean source checks require a separate upstream OAI 378 / Lean 4.34.1 environment:
# Integration/OpenAIMath/Upstream378EncodingLengthExact.lean
# Integration/OpenAIMath/Upstream378FiniteCNFBridge.lean
python scripts/check_openai378_frontend_exact.py
python scripts/check_openai378_27grid_maxcut_bridge.py
python scripts/compile_dashi_circuit_openai378.py source.json --stream-bits-out source.bits --out receipt.json
```

## 1 November — K02 isolated version gate now implemented (not checked)

Lean PR #78 now owns `vendor/openai-math/PIN_378.json` at **7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a** (OpenAI OAI378 / Lean 4.34.1), independently of the original `1581d4cb...` Git submodule. The new `scripts/materialize_openai378_toolchain.sh` enforces the pin and refuses the old vendor path; `scripts/check_openai378_staged_lean.sh` builds the upstream 378 dependency and elaborates the generic normalization adapter, exact-length adapter and fixed-machine adapter in that newer environment. **Neither script was executed here.** K02 remains a missing kernel/axiom receipt, but the version/pin conflict now has a non-mutating executable local acceptance path. The length adapter reuses original `Encoding.length_encodeNat` / `length_encodeList_cons` rather than re-proving those lemmas.

## 1 November A+B continuation — independently scoped work completed today

**A source-data work:** The original `PNotEqualsNPConcreteBooleanCircuitDAGExact.GateProgram` uses newest-first `gateWire : Fin g`, while the Python creation-order JSON uses gate index `j` earliest-first. The correct transport is `j = g−1−i`, already owned mathematically by `FiniteSource.chronologicalGateNumberExact`/stdlib `Fin.opposite`. Lean PR #78 now commits `agda_fin_wire_to_json`, its inverse, and an indexed-numbering finite regression to pay the executable half of M00 without creating a second Agda circuit evaluator. The Agda-to-Python typed serialization theorem **remains missing**. This is not a kernel receipt.

**B source inventory actually materialized, not just promised:** On Lean PR #78, the full exact-head source indices are committed for **721 manuscript links**, **373 families**, and **208 main-result declaration references** from upstream `CONTENTS.md` / `lean/formalization.yaml` (upstream 7ef5c0c, original manuscript map 721/373, YAML blob 372bcd7). The manuscript extractor handles the literal `CAT(0)` parentheses in an upstream PDF directory; naive regex otherwise drops one paper. A source-tree candidate routing scan over the present Agda/Lean trees records **101 of 208** declarations with at least one subject-name route and **107** without any subject-anchored route; this is lexical DISCOVERY ONLY (zero typed transports certified). The Lean tree API reported truncated source-tree results, so those candidate counts are a partial scanner snapshot, not exhaustive source discovery. `scripts/build_openai_math_same_object_matrix.py` can re-evaluate against complete local Agda/Lean trees, extract earliest Git-commit origin, and output every family, manuscript, declaration and source owner lead. This script has **not** been run locally from exact checkout here.

**Six high-alpha comparator/source boundaries actually inspected and recorded** in `Integration/OpenAIMath/reviewed_cross_corpus_same_object_boundaries_20261101.json`: OAI378 vs original finite DASHI `#SAT` (complementary, not yet same object), unrestricted Max-Cut hardness vs fixed 27-node maximum cut (different scope), quasi-RH 7/8 zero-free vs full RH (strictly weaker target), CM abelian Hodge vs universal Hodge (strict subclass), classical relativistic Vlasov–Maxwell vs quantum YM mass gap (different physical problem), and finite Fourier-circuit complexity vs other spectral/analytic Fourier donors (no typed identity inferred). No source was promoted to a kernel port or to a general Millennium theorem.

**Exact remaining gates unchanged:** K00–K02 kernel acceptance; M00 source AST-to-JSON typed relation, M01 whole Agda clause/Lean literal and byte-equivalence, M02 primitive compiler trace/runtime, M03 all-prefix visited space, M05 original counted circuit word on the same OAI machine; and the remaining per-family/comparator mathematical transports. Source metadata coverage is now complete for the upstream published 721/373/208 snapshot; proof integration is NOT complete. Source-written ≠ executed finite checks ≠ Agda/Lean kernel ≠ accepted same-object theorem.

## Max-cut execution order (do not replace a mathematical proof with a roadmap)

1. **K00** must genuinely elaborate the existing P1/P2 modules: fix first error with `agda --safe` where compatible and repeat through transitive imports. Exact local compiler unavailable here; no fabricated receipt. There are already source-written P1/P2 modules, so optimize by fixing proof terms in place.
2. **K01–K02** independently compile the Lean generic and 378-specific bridge. Upstream 378 release requires Lean 4.34.1, while DASHI pinned checkout is 4.28.0. Stage in separate reproducible environment and preserve existing pin.
3. **M00/M01** map *actual* source Agda gates and polarity through the executable source encoding and current upstream's exact Finset syntax. Matching Python finite tests ≠ proof of an Agda→Lean same-object map.
4. **M02/M03/M05** build genuine machine front-end trace/time/space (not just count output length); compose exact OAI source-list machine proof with Agda source circuit count. Never claim a better asymptotic ETH exponent from a polynomial compiler overhead alone.
5. **C01/C02** reuse this compiler/provenance substrate to prioritize mathematically proximate among current 208 declaration references; do not blindly transplant all catalogue rows.
6. **R03–R06** are genuine mathematical/physical estimates, not representational tasks. Their direct evidence requirements remain open and should be pursued as separate high-alpha lanes without silently claiming solved.

## Attribution/acceptance schema

| Claim type | Minimum evidence |
|---|---|
| Published classical identity | Named original mathematical author/date and precise hypotheses |
| Repository source claim | Exact owner module, PR branch, source declaration and author/commit |
| Executed finite check | Exact Python script, input families, deterministic counts/receipt |
| Lean/Agda theorem | Pinned toolchain and dependency/axiom audit, exact kernel run |
| Same-object cross-domain result | Typed transport with preserved carrier, operations, numerical normalization and negative controls |
| External result used downstream | Original upstream commit and proof, original researcher attribution; not an independently invented DASHI proof |
| Monster / QID / TOE connection | Explicit identity/action/representation proof, not matching numerical fingerprints or topical category labels |

No CI changes requested, no protected ESD edit, no independent author credit overwritten.


## 1 November 2026 — M00 parser ambiguity and corpus discovery max-cut continuation

These are **sub-obligations of the existing 39 IDs**, not additional completed proof certificates.

- **M00a, executed input boundary:** the actual Lean #78 Python frontend now has `parse_original_circuit_json`, which rejects duplicate object members (including nested wire/gate members), non-JSON numeric constants, and malformed/out-of-range/future-gate references. The previous `json.loads` CLI could silently overwrite repeated keys, so strict constructor-field validation alone was not enough. `canonical_original_circuit_json` supplies a deterministic validated JSON output form and its regression asserts parse/serialize/parse roundtrips. **STATUS: SOURCE-WRITTEN, SCRIPT CHECK NOT RUN IN THIS ENVIRONMENT; Agda GateProgram ↔ JSON typed relation, serialization injectivity and kernel receipt OPEN.** The decoder accepts multiple legal whitespace/key orders; text uniqueness is claimed only for the canonical encoder, not the input grammar.
- **C01, native owner discovery:** Lean #78's offline corpus candidate router now indexes *actual Agda top-level type signatures and Lean declaration names* as well as source paths, with a separate synthetic regression for filename-invisible owners. This improves search reach, **not** statement equality, inherited ownership, proof strength, or kernel verification. Real provenance/first-commit inspection and per-result typed transport remain open.
- **C02, source integrity:** Lean #78 adds a fail-closed, 208-row upstream declaration-source identifier audit. It intentionally reports `IDENTIFIER_TEXT_FOUND_UNVERIFIED` rather than inferring a theorem proof from matching text; absent file/identifier is a blocker. Requires the exact matching upstream revision and remains **NOT EXECUTED** here; an identifier hit does not discharge type checking, axiom audits, or imports.
- **Regression driver:** `run_openai_math_ab_acceptance_local.sh` now includes the owner-discovery and declaration-source audits alongside its Agda/Lean and original-DAG checks. Actual acceptance on the correct toolchains remains K00–K02 and M00–M05.

**Max-cut precedence unchanged:** K00→K02 kernel acceptance; M00/M01 typed original-object equivalence; M02/M03 fixed-machine compiler trace and all-prefix resource bounds; M04/M05 same-machine composition; then C01/C02 individual upstream theorem audit and genuine imports. The corpus count 721/373/208 is metadata, not a proof-count assertion.

