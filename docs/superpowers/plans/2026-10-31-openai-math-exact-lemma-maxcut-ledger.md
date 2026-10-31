# Exact remaining lemma and certificate register — DASHI/OpenAI SAT / corpus / adjacent max-cuts

**Audited 31 October 2026.** Authority: original Golden Agda source owners, Lean downstream, upstream `openai/math`, actual PR branches. This register is a *live statement-and-status inventory*, not a declaration that every source term has been checked.

**Critical distinction:** `SOURCE-WRITTEN` means source text exists on a PR; `KERNEL` means an exact toolchain independently accepted the proof. This run had **no Agda/Lean compiler** and the GitHub runner at the inspected head offered no existing result. Nothing in this register promotes source-only P1/P2 into theorem acceptance.

**Primary bounded task statement**: For every original DAG circuit `C` with `n` inputs and `g` gates, construct and validate the original counted 3-CNF on exactly `n+g` finite coordinates; optional 1/2/3-clauses yields ≤`3g+1` source list clauses. Prove `countCompiledCNF(C) = countAcceptedCircuitInputs(C)`; normalize without losing counts to the *actual* OAI `SAT.CNF (Fin (n+g))`; produce exact `Encoding.encodeCNF` bits and faithfully consume original OAI fixed primitive counting/SAT runtime and all-prefix space theorem.

**Selected existing reusable numerology/structure**: 369 / 3×3 trialectic axes, C3/S3 orbit group actions, 27-function / 11-orbit / 7+4 eigenspace, 27-vertex weighted checkerboard graph, radix/CRT/eisenstein λ⁹, sieve/primecount, and finite reflection parity. These are **typed donors** or test harnesses only where an explicit index/coordinate/equivariance theorem exists; do not infer SAT hardness, arithmetic infinitude, RH, physical mass gaps or Monster representation from the occurrence of 3, 9, 27 or matching fingerprints.

**Unfinished normal form**: Each obligation below must carry (a) exact quantified mathematical target, (b) prior owner/first commit, (c) preconditions and target types, (d) source proof term, (e) kernel/environment receipt, (f) independent executable check when useful, (g) same-object consumer and (h) promotion boundary. The *existing* #1212 and Lean #78 code are the authoritative source of definitions; this markdown file does not override those sources.


## KERNEL — 3 exact obligations or owners

| ID | Exact task / precondition / required postcondition | Reuse owner / consumer | Evidence / missing receipt |
|---|---|---|---|
| **K00** Agda P1/P2 import spine | Run exact-head Agda typecheck of `DASHI/Research/OpenAIMath/Everything.agda` and all transitive imports, plus optional `OpenAIMathSharedTseitinOptimizedCNFExact.agda`; fix every source elaboration failure; safe/0-postulate/0-metavariable audit before Golden promotion. | `Everything.agda`, `OpenAIMathFiniteSupportedTseitinModelsExact.agda`, `OpenAIMathSharedTseitinGateCNFExact.agda`, `OpenAIMathSharedTseitinUniqueExtensionExact.agda` | UNVERIFIED — source only |
| **K01** Lean generic adapter | Compile `Integration/OpenAIMath/ListFinsetCNFTransport.lean` on pinned Lean 4.28.0/mathlib and prove no `sorry`/new axioms, then join import spine. | `ListFinsetCNFTransport.lean` | UNVERIFIED — staged source |
| **K02** Lean version-gated later adapter | Pin/migrate an *explicit separate* OAI 378 4.34.1-compatible dependency environment; compile `Upstream378FiniteCNFBridge.lean`, inspect `#print axioms`, and only then enable consumers. Never silently rewrite old 4.28 vendor commit. | `Upstream378FiniteCNFBridge.lean`, upstream `SAT.lean`/`Encoding.lean`/`SqrtLogSpace/Final.lean` | UNVERIFIED — newer upstream not pinned |

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
| **M00** Verified executable original DAG serialization | Define actual original `GateProgram` ↔ Python JSON frontend relation, accepting only creation-ordered earlier gate indices. Show each source gate maps to original indexed window/clauses. | `scripts/compile_dashi_circuit_openai378.py`, `Circuit.GateProgram`, original compiler | MISSING FORMAL SAME-OBJECT RELATION; executable Python exists |
| **M01** Verified executable literal/polarity/Finset serializer | Prove actual finite list from M00 equals `Upstream378FiniteCNFBridge.toUpstreamCNF`; output bitstream equals upstream `Encoding.encodeCNF`, including literalCode, sorted numbers, unary and frame. | Python frontend, upstream `Encoding.lean` | MISSING FORMAL CROSS-LANGUAGE CODE PROOF |
| **M02** Uniform source frontend primitive time | Give concrete algorithm and trace/certificate showing finite source-gate → emitted canonical bitstream time bounded by a polynomial in `inputs+gates`; no free oracle, no uncosted sort or noncomputable Finset choice. | Python frontend and actual bounded primitive machine model | MISSING MACHINE COST CERTIFICATE |
| **M03** Uniform source frontend all-prefix visited space | Show each prefix of input preprocessing/serializer uses polynomially many cells, then compose with upstream `SqrtLogSpace.exact_count_and_sat` all-prefix bound. | OAI `Computation/VisitedTape/Final` | MISSING MACHINE COST CERTIFICATE |
| **M04** Fixed machine source-list count/SAT output | `sourceListExactCountMachine` rewrites actual machine count tape, SAT tape, time, space to source **list** model counts, same machine not new algorithm. | `Upstream378FiniteCNFBridge.lean`, upstream `Final.exact_count_and_sat` | STAGED — 4.34.1 kernel pending |
| **M05** Complete end-to-end Agda circuit count as machine tape result | Given genuine source circuit and its checked serialized compiled bitstream, compose N03/N04+L02/L03+M01-M04 into statement that tape yields original `countAcceptedCircuitInputs`. Preserve polynomial frontend and upstream complexity. | DASHI #1040/#1212; Lean #78; OAI 378 | MISSING FINAL SAME-OBJECT KERNEL COMPOSITION |

## CORPUS — 3 exact obligations or owners

| ID | Exact task / precondition / required postcondition | Reuse owner / consumer | Evidence / missing receipt |
|---|---|---|---|
| **C00** 208 upstream source-qualified declaration references | Catalogue exactly all 208 current `main_results` entries (192 comparator configurations), upstream blob `372bcd714cd3a186a9139ac8e0f3318961fb2df1`; metadata NOT 208 formal theorem ports. | Lean #78 `FullUpstreamMainResultsCatalogue.lean` | CATALOGUED AND ROW-CHECKED; kernel/ports separate |
| **C01** Corpus family/discovery bridge | 721 manuscripts / 373 families current README; map manuscripts/families to 208 declarations with date/author/authority and in-repo original mathematical owner; no title-only same-object promotion. | Existing `SourceAtlas.lean` / `OpenAIMathSourceAtlasExact.agda` / full catalogue | MISSING FULL 373-FAMILY SAME-OBJECT MAPPING |
| **C02** Full theorem imports into Golden Agda/Lean | For each desired mathematically relevant declaration: source premise/comparator, zero-sorry proof/axiom audit, exact object/typing equivalence, full kernel, consumer/attribution and stable vendor. | Lean/Agda `SourceAtlas`, upstream `formalization.yaml`, native DASHI proofs | NOT FINISHED; 208 entries ≠ 208 accepted DASHI ports |

## MATH — 8 exact obligations or owners

| ID | Exact task / precondition / required postcondition | Reuse owner / consumer | Evidence / missing receipt |
|---|---|---|---|
| **R00** Native 27-vertex weighted Max-Cut uniqueness | For strictly positive weights, prove 27-grid connectedness and only two saturated cuts up to complement in golden Agda. Keep separate from arbitrary-size graph Max-Cut hardness. | Agda #1438 `GraphColouring369PantsWeightedMaxCutExact` and QID atlas | OPEN KERNEL THEOREM; existing Python finite evidence |
| **R01** Unrestricted graph Max-Cut/UGC theorem transport | Match exact variable-size graph type and gap parameter of OAI family 102, prove reduction or lemma application with original #1438 carrier *only when same object*; not from 27-node toy alone. | OAI `OAI.OptimalMaxCut.main`; native #1438; Lean #103 | OPEN SAME-OBJECT TRANSPORT |
| **R02** C3/S3 27-function orbit and 7+4 parity relation | Reuse `PolynomialC3S3...` 27→11→7 quotient and earlier positive/negative projector; prove any claimed link to graph only with explicit equivariant function/relation. 27-functions ≠ 27-vertices. | Agda #1414; original `MoonshineOrbifoldSectorProjectorExact` | PARTIAL; no Monster same-object promotion |
| **R03** Twin-prime genuine unbounded pair count jumps | Remove or discharge explicit `laterJump` assumption with actual prime-specific arithmetic estimate or alternative theorem; wheel/CRT finite residue survival alone is insufficient. | Agda #1408 `TwinPrimeConditionalUnboundedFromCountJumpsExact`, sieve/SSP/FRACTRAN donors | OPEN ANALYTIC CERTIFICATE |
| **R04** RH signed correlation and strict scalar | Pay source owner #1434 A1 carrier summation/curvature/compensation, A2 scalar and B signed-fifth eventual gap with genuine analytic estimates. Zero-free Re(s)>7/8 is not RH. | Agda #1434 `RiemannRHMaxCutTOEExact`, Lean RH donors | OPEN ANALYTIC CERTIFICATE |
| **R05** Pickover actual giant real phase sign | Certified interval enclosure for relevant real fractional phase digit at exponent 9999!, with huge arithmetic cost or sharper analytic bound. CRT/Eisenstein phase reindexing alone is not the sign. | Agda #1260 `PickoverBase99SignedTailExact` | OPEN REAL-PHASE CERTIFICATE |
| **R06** YM physical continuum/OS mass-gap construction | Discharge continuum physical measure, OS reconstruction and physical mass-gap on the actual source carrier, not only route-S conditional algebra. | Agda #1440 `YMClayDirectSourceOSMassGapFrontierExact` and prior Balaban donors | OPEN PHYSICAL/ANALYTIC CERTIFICATE |
| **R07** TOE/QID/Ibrahim/Monster 3B evidence firewall | Integrate C3/369 lattice, orbit/projector, graph/sieve roles as independent typed lemmas; preserve Ibrahim 3B priority, explicit source date, no ESD modifications and no synthetic fingerprint→same-object proof. | Agda `Unifier`, `EverythingTOESymmetryResolved369`, QID/SSP and #1414/#1438 branches | ONGOING GOVERNANCE & SAME-OBJECT OBLIGATIONS |

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
