# OpenAI × DASHI Clay: three-frontier bidirectional steelman / exact maximum cut
**14 November 2026 — canonical Golden:** Agda Clay #1499; complementary Lean Clay #108.
**Provenance policy:** independently authored OAI results, earlier mathematical literature, review/comparator definitions, prior DASHI source and *new* bridge candidates are credited separately. This file records source signatures, typed forward and reverse proof obligations, negative controls and testable acceptance. No Clay result is declared solved. All new Lean 4.32/4.34 modules are external-toolchain *candidates*; none has a pinned native checker receipt.

## Decisive source pins (never mix them)

| Origin | Source commit | Toolchain | Exact theorem owner / verified signature |
|---|---|---|---|
| OAI October YM original | `yang-mills-group/OpenAI-YM-20261028@3456e5e75cf8d4cd558955a5c7638fba2d68f464` | Lean 4.32.0 | `Solution.lean: YangMills.jointExistence`; OAI's own continuum/physical definitions |
| Independent October YM review | `yang-mills-group/YM@55ba9fc36293b3f4d52c6b1f813169a0be76ee98` | Lean 4.32.0 | `CombinedAcceptance.lean: YMReview.Acceptance.combined_acceptance`, `OPECheck.lean: YMReview.OPE.from_source` |
| OAI September NS C/D | `openai/NavierStokesAndEuler@8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538` | Lean 4.34.0-rc2 | `NavierStokes/ComparatorSolution.lean: NavierStokes.Comparator.navier_stokes_breakdown_R3 / navier_stokes_breakdown_periodic`; `ComparatorDefinitions.lean` |
| OAI October #SAT index | `openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` | Lean 4.34.1 | `OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean: exact_count_and_sat, sat_polynomial_space`; `SAT.lean`, `Encoding.lean` |
| DASHI immutable vendor (DIFFERENT OAI source) | `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a` | Lean 4.34.1 | Pinned `vendor/openai-math-src`, 200 main-result *references*; new 208-index declaration source is NOT the same pin |
| DASHI owner | Agda #1499 and Lean #108 | Agda 2.9; native Lean 4.28.0 | Original Wilson F19/R445/R736/SAT DAG/Tseitin owners; no imported OAI theorem types assumed |

Pinned source Git blob receipts read directly this round:
YM review `CombinedAcceptance.lean@2b22d1c94ca5b21fdfaae89e97e6c05ad7096af9`, `OPECheck.lean@87baa3e02f36aee7b611bac2fe940c504c01c87c`; NS `ComparatorSolution.lean@cc232068cd384dbbddce2753b1fc4a4017c0f2d7`, `ComparatorTheorem.lean@8105493534a5007c689c59e22bc252623bcbe901`, `ComparatorR3Theorem.lean@eb98522380b91b209421bf7519f34bc68ba95c1d`, `R3PressureKernel.lean@94cdfa7c25bec92ac0b157813a75660bd9306c7f`, `R3PressureFlux.lean@fee9426b1d9b9a88408709aab9aa137bcf3ca2fb`; OAI SAT `SAT.lean@14dcfd0c910a08b005354da1fa66fbdac3ae7192`, `SqrtLogSpace/Final.lean@a69635a2492e06a26f2e33d4251edd1e21ba3332`. Source-byte identity does NOT certify elaboration/trust.

## YM: accepted continuum, original R445/F19, and missing mass gap

**OAI → DASHI, positive steelman.** The reviewed A7 existence chooses one Wilson family C **before** every extraction order p and one associated (q,S,F) for each order. `LatticeAndScale.finite_law` compares the original OAI Wilson law with `lgt` after the explicit beta/dimension conversion; `PhaseAndOS` uses the *selected centered scalar* zero-diagonal Schwartz family. Its finite full-UV/extracted-IR limit and scalar Wightman/OS claims provide a serious potential donor for original E1. It explicitly lacks a D2 mass gap, all-field OS identification and uniqueness.

**DASHI → OAI, positive steelman.** Golden `YMClayOriginalWilsonPhysicalF19PartitionExact.originalFinePhysicalPartitionEqualsActualEffectivePartition` already handles the original SU(N) 1024-link/64-pair+896-spectator Haar disintegration in the same interacting Wilson partition under explicit source interfaces. The original two-marked F19 normalized laws, R445 covariance and exact conditional-TV compilers can audit OAI's A3 finite law and its selected Wilson insertions. This does **not** independently prove A7 or give a polymer decay inequality. It could make the OAI finite-law / effective-action equality more source-explicit.

| ID / class | Exact required theorem or transport | Inputs to prove, not assume | State |
|---|---|---|---|
| **YM.A01 / SOURCE** | `oai32A3ConfigurationEquivMatchesOriginal1024F19` | same compact simple group/SU(N) representation; orientation, links, periodic side and original 1024→64+896 codec | OPEN |
| **YM.A02 / SOURCE** | `oai32WilsonLawEqualsOriginalF19NormalizedHaar` | beta/(N+1) conversion; normalized Haar; Wilson plaquette action and volume/cutoff indices; 64-pair weighted disintegration | OPEN |
| **YM.A03 / SOURCE** | `oai32A7WilsonFiniteMomentsEqualOriginalF19Marked` | for *actual nonconstant* F,G,FG source marks; same Wilson law and common partition; no fictitious bare-coarse identification | OPEN |
| **YM.A04 / SOURCE** | `oai32A7ScalarOSMatchesOriginalR445OSCarrier` | selected vs phase-averaged state; zero-diagonal Schwartz domain; same reflection map; common OS reconstruction H, not merely nonnegative finite Gram | OPEN |
| **YM.A05 / SOURCE** | `oai32A7WilsonLimitYieldsOriginalE1` | **same** cylinder/test alphabet, weak/topology, UV-before-IR extraction, normalized/nontrivial Schwinger laws and OS; faithful original-source transport | OPEN; OAI at its own E1 stronger than verified DASHI E1 |
| **YM.A06 / A-VERIFY** | `combined_acceptance_with_same_hierarchy_commonOPE` | extract existing `Accepted.source` hierarchy/Q; use OAI review `OPE.from_source`; **do not** select unrelated A8 T | Lean #108 external-4.32 proof candidate; no kernel |
| **YM.B01 / NEW_PHYSICAL** | `originalR445PhysicalExteriorInfluenceSiteBound` | physically varying Wilson effective and target measures; nonperturbative large field and boundary errors | OPEN |
| **YM.B02 / NEW_PHYSICAL** | `originalR445GenuineScaleIrrelevantContraction` and original F,G,FG uniform moment covariance | summable cut-off/volume-uniform RG errors for actual renormalized law, not a toy two-state transfer | OPEN |
| **YM.C01 / NEW_PHYSICAL** | `originalSameOSDenseNonvacuumPhysicalTimeGap` | one H, dense gauge-invariant nonvacuum sector, one uniform positive decay exponent after continuum and IR | OPEN |
| **YM.C02 / NEW_PHYSICAL** | `originalYMNonGeneralizedFreeFieldAndAllCompactSimpleGroups` | nontrivial interacting field, all required compact simple groups, group-specific uniform estimates | OPEN |

**BIDI test:** If OAI A7 has the same literal original F19 Wilson carrier, then its finite-moment equations can be transferred *forward* into original E1 tests; conversely, original F19/F,G/FG can be used *backward* as source-independent audits of OAI finite law A3. Neither direction implies `D_k` small: original R445 TV needs the physical effective-vs-target pair. A5's positive lattice probe does not imply a uniform same-H spectral gap (safe finite negative control already in the rollup).

## NS: distinguish proven forced scope from original unforced programme

**OAI → DASHI:** external `ComparatorSolution.lean` states for every ν>0 an *existential smooth force f* and initial data satisfying the exact comparator force and initial-velocity conditions, but no global comparator solution (C on R³ with uniformly bounded energy; D periodic). `ComparatorTheorem.option_D_of_candidate` traces the actual smooth, periodic, compact-time-support, viscosity-rescaled forced candidate; `ComparatorR3Theorem.option_C_of_compact_candidate` does the separate whole-space analysis. This is not a proof of nonexistence for f=0, nor a direct refutation of DASHI unforced R736/B. The latest pinned source has explicit comparator adapters, not merely prose.

**DASHI → OAI:** R736 already expresses its two critical signed weighted leaves on the physical original torus carrier:
`W_N(T)+Q_+-,N(T) ≤ B(T)` and
`[X_N(T)-12Q_+-,N(T)]-[X_N(0)-12Q_+-,N(0)]+δ_N D_N(T)≤12W_N(T)` (δ_N>0).
Any proposed **forced-universal** extension of this method must survive the external C/D counterexample; an unforced f=0 estimate is not eliminated by that check.

| ID / class | Exact target | Genuine obstacle | State |
|---|---|---|---|
| **NS.A01 / SOURCE** | `oaiNSComparatorCAndDHaveOriginalClayDataAndSolutionClasses` | verify comparator's `ForceConditionDecay/Periodic`, energy, smoothness, periodicity and pressure against **current published/official** statement, not just its own definition | OPEN independent manuscript→formal semantic audit |
| **NS.A02 / A-VERIFY** | `no_universal_forced_periodic_global`, `no_universal_forced_R3_global_energy` | direct logical corollaries of *exact external Comparator* C/D theorems; maintain whole-space energy caveat | Lean #108 external-4.34-rc2 candidate; no kernel |
| **NS.A03 / A-VERIFY** | `unforced_no_solution_to_forced_periodic_breakdown`, R³ analogue | backward implication requires zero forcing to belong to the exact comparator force class; theorem currently takes admissibility as explicit input | Lean #108 external-4.34-rc2 candidate; no kernel |
| **NS.B01 / SOURCE** | `oaiR3PressureFluxToR736RemoteCollarCorrespondence` | external `R3PressureKernel.integral_kernel_moment` (`L^{4/3}` commutator moment ∝1/R), `R3PressureFlux.regularized_flux_le`; original torus pressure, Biot–Savart, zero-mode, cutoff and sign | OPEN: promising **analysis donor**, not periodic signed-flux estimate |
| **NS.B02 / SOURCE** | `oaiR3EnergyBoundaryToOriginalR736EnergyCarrier` | external `diffusionFlux_le`, `transportFlux_le` multiply compact cutoff but use R³ L²; original W1/W2 quartic signed carrier and torus | OPEN |
| **NS.B03 / FORMALISE** | `originalR71RealGalerkinLocalSolution`, `originalR853SignedRateAlongGalerkinSolution`, `originalR828R854RateLipschitzAlongSolution` | original finite-dimensional quadratic vector field, fixed horizon, same R853 observable; R829 negative at t=0 is already paid | OPEN |
| **NS.C01 / NEW_PDE** | `originalR736SignedCollarAbsorbable` + `originalR736RemoteFluxControlled` + uniform PDE continuation | actual unforced 3D nonlinear trajectory, N-independent constants and time horizon; a finite example cannot pay this | OPEN |

**NS pressure donor scale direction:** the exact external R³ identity
`R3PressureKernel.integral_kernel_moment` states an L^(4/3)-moment
of the cutoff commutator proportional to 1/R. It tends to zero in the
**large-radius R→∞** comparison, but grows like 1/R for shrinking
R→0; the associated L^(4/3)-norm scales like R^(-3/4).
It is therefore a plausible donor for R³ **remote-boundary** control,
not automatically a positive small-collar viscosity reserve.
Transport to a periodic pressure kernel requires a new periodization/
zero-mean and nonlocal stress correspondence, not replacing R³ by T³
by notation. This is the exact reason NS.B01 and NS.B02 stay
separate gates.

**Historical manuscript audit:** the 27 Oct 2026 King’s/Cambridge preprint compared an earlier Lean/written proof and reported, among other differences, an inverse-operator bound using an extra input derivative (m+5 rather than m+4). The latest pinned comparator theorem is **not** thereby automatically refuted; check chronology and the exact current manuscript/Lean pair. Do not conflate logical C/D comparator acceptance with full prose-fidelity validation.

## P≠NP: source #SAT machine into original DASHI DAG/bit-cost, then back again

**OAI → DASHI:** actual `SqrtLogSpace.exact_count_and_sat k hk` (k≥2) supplies one primitive machine for all bounded-width `SAT.CNF (Fin n)`, exact `SAT.count F` count tape and positivity-based SAT answer tape/state; its runtime bound is parameterized by the *actual `Encoding.formulaBitLength F` and n*, and the quantified every-prefix visited-space bound is polynomial in encoded bit length. `sat_polynomial_space` (k≥3) already supplies `answer=true ↔ SAT.Satisfiable F`. DO NOT duplicate this construction or count bit proof.

**DASHI → OAI:** the Golden original Boolean DAG, creation-order typed reversals, original Tseitin unique extension and optimized source CNF have their actual count identities:
`Source.originalGlobalCNFCountExact`,
`Opt.optGlobalCNFCountExact`,
`Creation.creationOptimizedTseitinCountExact`. These certify the original *mathematical count*; they do not yet certify OAI Finset normal form, literal byte encoding or machine cost. New Agda source `OpenAIMathOriginalOptimizedSATDecisionBitExact` composes those identities to the exact nonzero SAT decision bit, preserving same original circuit.

| ID / class | Exact needed theorem | Inputs/acceptance | State |
|---|---|---|---|
| **SAT.M00 / SOURCE** | `oai378ParserJSONBytesDecodeOriginalCreationCircuit` | real canonical JSON schema, creation/serialization order, total parser, no collisions; typed `decodeEncodeCircuit` alone is not a byte parser | OPEN |
| **SAT.M01a / A-VERIFY** | `normalizeListCNF_eval_true_iff` + `normalizeListCNF_count_eq` on **actual OAI `SAT.CNF (Fin n)`** | source list/Finset dedup and literal index/polarity, *all* n declared variables incl. unused; original Agda `OpenAIMathLiteralCodeTransportExact` still needs cross-language type equality | Lean #108 external-4.34.1 candidate; no kernel |
| **SAT.M01b / SOURCE** | `oai378EncodeCNFEqualsOriginalOptimizedCircuitBits` | canonical Finset clause/literal sorting, framing, number encoding and **exact bitstream**, not only list semantics | OPEN |
| **SAT.M02 / FORMALISE** | `oai378OriginalPrimitivePreprocessingClockPolynomial` | actual source compiler time for JSON/source circuit → OAI binary encoded `SAT.CNF (Fin n)`; include copies, sorting and output | OPEN |
| **SAT.M03 / FORMALISE** | `oai378OriginalPreprocessEveryPrefixVisitedCellsPolynomial` | all heads/tapes/allocated buffers/decoding and produced count length, in the original primitive cost model | OPEN |
| **SAT.M04 / SOURCE+COMPOSE** | `oai378FixedPrimitiveMachineReturnsOriginalCircuitCount` | apply OAI exact machine only **after** M00–M03, same original count and same width k | OPEN |
| **SAT.M05 / SOURCE+COMPOSE** | `oai378FixedPrimitiveMachineDecidesOriginalSATWithResources` | source count/nonzero bit, original Cook-Levin polynomial circuit encoding and all machine costs; quantify over input lengths | OPEN |
| **SAT.F1-F4 / FORMALISE** | `originalBitTapeStepSimulatesN21Rule`, `nativeN21CompleteLiveHeapPolynomial`, `originalN21InNP` | original N21 verifier/FRACDASH word, all parser/history/ledger/scratch heads, acceptance quotient and bit polynomial clock | OPEN; Karp-21 ∈NP does NOT give SAT∉P |
| **SAT.CLAY / NEW_COMPLEXITY** | `UniversalPolynomialSATDecisionFailure` | for **every** polynomial-time original cost-model candidate D exhibit an input φ where D fails | OPEN, independent of OAI ETH-refuting upper bound |

**BIDI test:** the model counts flow forward `original DAG → optimized 3-CNF → actual OAI Finset CNF → original native machine count tape`, and backwards `machine result → decoded OAI count → source CNF → original accepted inputs`. BOTH directions are required to exclude false positives from padding, order, missing variables, changed polarity and output encodings. Every-prefix polynomial space is not polynomial *time*. OAI's published superpolynomial-shaped upper bound does not provide a polynomial runtime certificate; it is also NOT a lower bound for that machine. Thus no P≠NP result follows either way.

## Work source-written on canonical PRs in this round

**Agda Golden #1499**
- `DASHI/Research/OpenAIMath/OpenAIMathOriginalOptimizedSATDecisionBitExact.agda`: original count ⇒ original SAT decision bit in three representations, no replacement evaluator. Added to `OpenAIMathFullSourceRollup20261114.agda`.
- `scripts/check_oai_bidi_ns_sat_20261114.py`: 580 exact finite CNF list/Finset cases for 0–3 variables plus unused-variable, empty-clause and duplicate controls; 4 forced/unforced scope truth models with one compatibility countermodel. Registered in `scripts/check_clay_sixfrontier_physical_local_20261114.sh`.
- Earlier A7/A8 two-witness Agda negative control and F19/R445 sources remain in same #1499.

**Lean Clay #108 (external adapter staging, NOT native 4.28 imports)**
- `Integration/OpenAINavierStokes34/ForcedGlobalScopeCorollariesCandidate.lean`: direct exact Comparator C/D no-universal-forced-global corollaries plus reverse conditional zero-force lifts, no fresh PDE proof.
- `Integration/OpenAIMath34/OriginalListFinsetCountTransportCandidate.lean`: actual native OAI `SAT.CNF (Fin n)` normalization from original-style literal lists and all-assignment exact model-count equality candidate.
- Earlier `Integration/OpenAIYangMills32/CombinedA7A8SameWitnessCandidate.lean`: single accepted F / Q ⇒ CommonOPE without a new independent witness.

## Acceptance and next execution — one active PR per repository

0. **Local exact-head source-only regression:** from Agda #1499 worktree set `DASHI_CLAY_LEAN_WORKTREE` to Lean #108 and run `CLAY_SIX_SOURCE_ONLY=1 bash scripts/check_clay_sixfrontier_physical_local_20261114.sh`. This only checks finite simulations and source presence, NOT new Agda/Lean proof terms.
1. **Golden Agda 2.9:** `AGDA_JOBS=1 DASHI_NO_TMUX=1 bash scripts/run_agda29_parallel_check.sh DASHI/Research/OpenAIMath/OpenAIMathFullSourceRollup20261114.agda` with transitive axiom/legacy-real audit. Never infer the root is `--safe` because it imports other owners.
2. **Three independent upstream toolchains:** stage YM A7+A8 adapter into the exact Lean 4.32 review package; stage NS corollaries into pinned 4.34.0-rc2 `openai/NavierStokesAndEuler`; stage SAT list/Finset adapter into pinned 4.34.1 `openai/math`. Run `lake env lean` and `#print axioms`; exact code needs source-interface review and may require elaboration fixes. Never compile these foreign imports as native Lean 4.28.
3. **BIDI original source proofs:** prioritize **YM.A01–A05** and **SAT.M01b–M05** (greatest direct theorem reuse). In NS, **NS.B01/B02** are concrete analytic reuse targets but must respect R³ vs torus and unsigned vs signed flux. Complete the separate original R71/R853 finite-flow joins.
4. **True C frontier:** original Wilson mass gap / nontriviality and all groups, original 3D uniform regularity vs validated C/D breakdown, and the universal polynomial SAT lower bound. These are not discharged by a checker, a finite regression or a source/witness record.

**Exact local regression receipt:** the committed source Git blob `5a37096a5d7579bea3a439b31020d1621259eb21` was independently reconstructed and run on 14 Nov 2026: PASS (580 finite CNF formulas and four NS predicate models). This source-only receipt is **not** a Lean/Agda proof.

**Status:** selected original count→SAT decision and foreign typed corollary/proposed count transport *source-written*; the local finite regression passed 580 CNFs and 4 NS models; no pinned new Agda/Lean kernel checks, no full external proof replay, no same-object YM E1/D2, no Clay solution. Preserve all donor heads, author priority, original math and review citations.
