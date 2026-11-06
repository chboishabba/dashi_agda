## HIL01/HIL07 full algebra noncommutativity scope: exact negative theorem (7 Nov)

`TSVFOriginalCylinderFullAlgebraCommutativityNoGoExact.agda` is a **safe** theorem on the original M2a algebraic shape. Any `compile` preserving products from a commutative cylinder algebra into operator composition necessarily has commuting images (`originalCylinderImagesAlwaysCommute`). Any pair of noncommuting operators in that image refutes the global M2a premise (`aNoncommutingPairInTheImageIsImpossible`). If the cylinder image is falsely asserted onto the *whole* operator algebra via a selected right inverse, `noFullNoncommutativeOntoCylinderOperatorRepresentation` forces all operators to commute. This is an exact algebraic falsifier, not a chosen physical QFT.

**Required HIL01/HIL07 repair:** M2a must be explicitly scoped to the appropriate commutative Wilson/gauge-invariant cylinder sector, and full noncommutative observer star algebra must be separately generated/represented and completed with justified density/continuity. The finite HIL08 Gram lemmas remain valid for their selected cylinder input, but do not entail a full onto operator-algebra equivalence. Original selected reflection M2b remains one physical map (see arbitrary-reflection-collapse no-go), not a universally arbitrary map.

The new safe falsifier is imported into the golden unified regression and listed in `run_tsfv_unification_maxcut_20261106.sh` for exact-head `parallel_checker`; source-written only, no kernel receipt or continuum physical input.

# #1460 unification TODO — Pareto source construction and fail-closed acceptance

**Four-cut source-producing proof queue:** [40 named exact OBS/HIL/KK/BIDI producer lemmas](TSFVFourPhysicalCutsExactProducerLemmas20261106.md), each mapped to existing canonical IDs. **Canonical:** [186 exact P00–P11 lemma IDs](Emergent31QuantumYMKKExactLemmaRoadmap20261103.md). **Executable:** [48 deliverables / five phases](TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md). This is our lane only; do not mutate #1444 YM-owned science.

**New HIL06/HIL07 selected native published RP compiler:** `TSVFOriginalR445PublishedWilsonRPWordWeldExact.agda` reuses the repository's Osterwalder–Seiler/Menotti–Pelissetto `BalabanClayOSWilsonReflectionPositivityExact.wilsonPositivityAtAnySeparationParity`; for every *admissible gauge-invariant positive-time finite word* it transports the published nonnegative reflected expectation through an explicit **same-original-Wilson-source equality**, then through `TSVFOriginalR445ReflectedAllWordGramExact.originalFineOSPositiveTransfersToNativeR445` onto the actual R445 coarse positive word form. It does NOT prove the physically missing source equality, fine reflection/block geometry, continuum OS or observer Hilbert identification. This is a new non-safe physical regression proof, checked through `parallel_checker` as a candidate; no Agda/kernel receipt yet.

## HIL07 source M2b repair: actual single reflection, no collapsed cylinder algebra (6 November 2026)

The previous `TSVFOriginalForwardToNativeWilsonWordGramExact.OriginalSameSourceMeasurement` required `originalCylinderReflectionIsOperatorAdjoint` **for every arbitrary function** `reflection : Observable → Observable`. This is not a valid physical OS premise: choosing two constant maps forces `cylinderOperator F ≡ cylinderOperator G` for **every** pair of observables, collapsing any nontrivial physical instrument's observable representation.

**Now repaired in the original source owner:** `OriginalSameSourceMeasurement.selectedPhysicalReflection` is ONE physically selected gauge/clock-compatible reflection, and its adjoint compatibility is asserted only for that chosen map. All original `originalAllWordReflectedProductIsObserverStar`, forward-vs-native R445 word cross-Gram, fine Wilson cross-Gram and actual selected cyclic ket cross-Gram theorem statements have been recut to **derive from exactly the same selected reflection**, no extra reflection parameter permitted at call sites. `TSVFOriginalMeasuredFiniteSpanR445Exact` consumes that field and transports the SAME choice through its real finite span and BIDI Gram quotient.

**Golden negative theorem:** `TSVFOriginalArbitraryReflectionCollapseNoGoExact` proves by applying hypothetical universal-adjoint compatibility to constant maps that all cylinder operator images coincide; with any two distinguishable images the universal property yields contradiction. The no-go source is checked as a safe candidate. Its purpose is to forbid reintroduction of a logically overstrong observer/OS interface.

**Still physical:** selecting/constructing the reflection on actual gauge-invariant positive-time cylinders, its involution, support and native-block intertwining, complex conjugation/star, M1 physical same-instrument measured readout, complex OS/GNS and continuum remain obligatory. Merely choosing a field does not construct the physical reflection.

## Native Bishop-complex HIL08 algebraic finite-span completion (6 November 2026)

The existing selected observer-to-Wilson readout is only real-valued. **It is not legitimate to identify its equality with a complex Hilbert Gram.** The new `TSVFBishopSetoidComplexCyclicSpanGramExact` imports `DASHI.Analysis.BishopSetoidComplexExact` directly (the real Murray/Bishop setoid and native complex `conjugate`, `_+C_`, `_*C_`, `_≈C_`), and proves by two nested finite inductions that every *finite complex coefficient* cyclic pairing `Σ_iΣ_j conjugate(a_i) * b_j * Gram(w_i,w_j)` is setoid-equivalent across observer and OS when their genuine all-word complex Gram values match. It proves the diagonal as a corollary and **both directions of finite-span Gram-indistinguishability** on the OS image.

This is constructive **finite sesquilinear coefficient transport**, not an abstract arbitrary-real or propositional complex equality. It reuses Bishop/Murray/Csimma code and carries no new primitive analytic axiom itself; the non-safe Bishop import/transitive dependencies are checked in the separate physical/Bishop regression and must receive a full trust audit.

**The exact HIL07/HIL08 wall is now sharper:** construct the *actual complex* original TSVF star/reflection state and same-source equality with the independent YM OS gauge-test complex Gram (real-part cylinder calibration M1/M2 is insufficient by itself); then a positive complex null ideal, completed GNS, dense onto complex-linear isometry, Stone spectral/domain same-source. The finite algebraic span portion is source-written, not independently kernel accepted.

**Cross-domain K05-PRODUCT:** this constructive Bishop complex finite sum-product/setoid congruence machinery is reusable as a donor. The actual **signed-factorial Cauchy convolution limit and triangle/rectangle summation** have NOT been constructed by this proof; neither `K04d-LOG`, `K05-PI` nor `K04d-CONTINUITY` is promoted.

## HIL07/HIL08 actual source-to-finite-span bridge (6 November 2026)

- `DASHI.Physics.Foundations.TSVFOriginalCyclicFiniteSpanGramExact` is a **safe** structural induction proof: one original source `MatchedPhysicalCyclicWords.allWordGramMatches` extends to **all pairs of arbitrary finite real-weighted cyclic word combinations** and their diagonal pairings. It also supplies a formal OS-image map for the finite spans. This is not a claim that complex Hilbert superpositions or positive OS norm already exist.
- `DASHI.Physics.Foundations.TSVFOriginalMeasuredFiniteSpanR445Exact` is the non-safe **actual-source specialization**: consumes `TSVFOriginalForwardToNativeWilsonWordGramExact.originalMeasuredAllWordCrossGramEqualsNativeR445`, whose original physical observer is the selected forward ket and whose native YM source is the actual R445 Wilson-Gibbs fine/pushforward measure. It constructs a concrete `MatchedPhysicalCyclicWords` from the genuine source theorem (not an invented all-Gram field), then derives `originalMeasuredFiniteRealSpanEqualsActualNativeR445`, the diagonal identity, and **bidirectional finite-span Gram-indistinguishability transport**. These are finite real formal span theorems; physical M1/M2 instrument/source readout, complex star/sesquilinear Gram, OS positivity, null quotient completeness, dense image, Stone and all limiting conditions remain explicit physical producers.
- **Ownership:** #1444 now owns original native finite YM `YMClayOriginalR445ReflectedAllWordGramExact` and `YMClayOriginalR445PublishedWilsonRPWordWeldExact`; #1460 finite spans are **observer-specific external comparison** and must not be introduced as prerequisites into #1444's standalone R443→R333 proof. Duplicate child-side finite YM modules are historical donor implementations; the preferred YM source authority is the parent.
- **Verifier:** `run_tsfv_unification_maxcut_20261106.sh` enumerates the safe finite-span compiler and the physical instantiated source separately under `parallel_checker`. No exact-head Agda kernel acceptance or original physical existence has been obtained by merely writing these modules.

## 6 November 2026 — current exact max-cut / ownership and evidence

**40 named** source-producing OBS/HIL/KK/BIDI obligations (10+12+10+8) are now fully inventoried and crosswalked to the existing 48 phased deliverables and 186 canonical source IDs. Audit: `scripts/check_tsfv_40_physical_producer_inventory_20261106.py`. **This is an exact inventory, not a proof that the 40 physical statements have been fulfilled.**

**Source-written child proof progress:** [x] original finite TSVF intervention and ordered commutator; [x] original selected forward-ket conditional normalization/additivity/homogeneity and (A^\dagger A) norm; [x] exact native original Wilson R445 all-word and now **reflected all-word real Gram** pushforward; [x] original QuantumSurface singleton nonpromotion and positive-Gibbs-weight/not-necessarily-OS-RP no-go; [x] nonflat sourced AdS4×S1 Einstein–scalar test and original selected KK horizontal identity *conditional on observer measurement*. All remain **KERNEL_OPEN** unless an exact-head `parallel_checker` record is produced.

**Latest independent YM donor #1444 (do not mutate):** actual original two-plaquette marked source, whole normalized native Wilson R445 pushforward, interacting 64-pair/896-spectator fibre effective source, original native Wilson OS **reflected quadratic** pullback (which specifically still requires original fine Wilson RP and geometric reflection compatibility). These remove duplicate finite calculus problems but **not** same-source CMP119/122 ghost/boundary E/R/B/V, CMP116 cutoff/volume-uniform localization or OS continuum.

**Highest Pareto physical producer leaves, in strict dependency order:** 
1. `OBS01→OBS05→OBS06→OBS07→OBS08→OBS09`: actual selected physical unitary/observer instrument and local response Kubo kernel, calibrated signal cone/dimension four/Lorentz measured principal symbol (O01–O11).
2. `HIL01→HIL02→HIL04→HIL05`: physically instantiate inner product/star/operator/positive real state, construct complete noncollapsed observer GNS and strongly continuous unitary/Stone; in parallel YM must construct original Wilson fine RP/complete OS.
3. `HIL06→HIL07→HIL08→HIL09→HIL10→HIL11`: match original observer state with independent YM OS *all-word reflected* Gram, null quotient and dense onto isometry, both real-time groups, full spectral calculus and Wick.
4. `KK01→KK02→KK03→KK04→KK05→KK06→KK07→KK08`: original observer-linked smooth five-metric and Einstein–gauge–matter solution; reduce to **independently measured** original OBS08 4D bilinear (K01–K08), not chosen AdS4 control.
5. `BIDI01→BIDI02→BIDI03→BIDI04→BIDI05→BIDI06→BIDI07→BIDI08`: original physical source key across all branches, UV/IR/KK/history/OS commuting limits, independent falsification and exact-head trust/physical receipts (B01–B08).

**Acceptance policy:** source-written/conditional ≠ kernel acceptance ≠ selected physical theorem; this status must remain fail-closed in all three ledgers. Neither mathematical exact reduction nor source syntax alone can stand in for independently measured causal geometry, physical reflection positivity, nonzero continuum OS sectors, or uniform CMP116 exponential decay.

## Extended source implementation completed in one pass — 6 November 2026

- [x] **HIL01:** `TSVFOriginalForwardCyclicCrossGramExact` proves all original source operator cross-pairings `omega_E(A†B)=<A psi_E,B psi_E>`, with actual `TSVF.forwardState E`, using only the selected physical source adjoint/compose laws rather than an independently assumed Gram.
- [x] **HIL02:** `TSVFOriginalForwardCyclicActionQuotientExact` proves original cyclic-action kernel congruence for left composition, addition, scalar multiplication and identity. It does NOT assume right-ideal/complete-Hilbert positivity.
- [x] **Concrete original HIL01:** `TSVFOriginalComplexFiniteForwardNormalizedDiagonalExact` uses the actual `TSVF2017OriginalComplexABLSelectedExact.finiteComplexQuantum`: its forward ket is `(1,1)`, norm **2**. Constructs a correctly normalized physical-source real-diagonal state with exact identity, complex-coordinate composition, self-adjointness and `omega(A†A)>=0` from rational square positivity; not the full noncommutative/continuum algebra.
- [x] **HIL07/S10:** `TSVFOriginalForwardToNativeWilsonWordGramExact` compiles the same original forward source to actual Wilson/R445 fine and pushed real **all-word** cyclic Gram. The full pairing equality is DERIVED from independently auditable M1 single-cylinder original real readout match, M2a cylinder multiplication and M2b reflection/adjoint, not a global all-pair Gram premise. **Still PHYSICAL_OPEN** until the selected instrument supplies M1/M2 and independent YM complete complex OS.
- [x] **KK10:** `TSFVKKFourMetricVerticalProbeFullReconstructionExact` proves complete KK5 bilinear reconstruction from the same g4, fifth-circle radius and mixed connection probes using native 5D metric. Selected original measured probes/5D solution remain PHYSICAL_OPEN.
- [x] **Independent exact control:** `scripts/check_tsfv_original_complex_diagonal_kk_tomography_20261106.py` passed 1,443 Fraction equivalence/reference cases. It now runs before the pinned `parallel_checker`.
- [x] Both Golden-safe and axiomatic physical R445 regressions/selected source arrays updated without touching YM #1444 and without creating alternate Wilson measures.
- [ ] **S08/HIL02–HIL05:** selected full complex noncommutative GNS, positive null-ideal quotient, complete Hilbert, strongly continuous physical Stone group.
- [ ] **S09/HIL06–HIL11:** original physical observer Born/Wilson cylinder map M1, product/adjoint M2a/M2b, full complex Schwinger/OS all-word state, onto unitary, self-adjoint generator and Wick.
- [ ] **S01–S04/OBS01–OBS09:** original nontrivial measured Kubo, uniform propagation, independent 4D Lorentz cone/clock.
- [ ] **S05–S06/KK01–KK08:** actual original 5D Einstein–matter solution and its reduction to independently measured g4; neither symbolic AdS4×S1 control nor algebraic tomography is the physical source.
- [ ] **S10/BIDI01–BIDI04:** same complete CMP119/122 effective Wilson source, genuine selected uniform CMP116 localized estimates and physical UV/IR/history/KK/OS limits.
- [ ] **S11/BIDI07:** exact-head `parallel_checker` zero-error compile and full transitive trust audit; 1,443 reference cases alone are NOT kernel acceptance.

**OBS04/OBS05/OBS07 source-specific negative control:** `TSVFOriginalComplexFiniteClockPropagationNonpromotionExact` consumes the ACTUAL `TSVF2017OriginalComplexABLSelectedExact.finiteComplexQuantum` (rather than a hypothetical singleton Q) and proves its original Time is Unit, all time coordinates are equal, and original `evolveKet/evolveBra` are identities. Its existing nontrivial complex ABL and record amplitudes do not contain a physical retarded propagation clock or dimension-four manifold. A new nontrivial original continuous, spatially located physical dynamics must be built to discharge OBS05–OBS09; this is a mathematically proven source boundary, not an extra YM dependency.

## Actually completed source and integration work this round

- [x] Reconcile #1444 physical-cube PCUBE/CMP116 donor into #1460 through [#1470](https://github.com/chboishabba/dashi_agda/pull/1470), merge SHA `1f71c1d58cc2d231a0fdc42c50b0c9969d35e49b`. Pin donor source head; later parent updates require a new sync.
- [x] Source-write `TSFVAcousticLocalImpulseThirdDerivativeExact`, actual selected nearest-neighbour kick (q'''(0)=-L\delta_0), all six first-neighbour response coefficient (c^2/a^2), outside-first-ball zero and mass blindness.
- [x] Source-write `TSFVAcousticMassInverseBidiNoGoExact`; selected (3,1) principal does not identify mass, whereas complete frequency response determines squared mass at the zero Fourier point.
- [x] Import/export both from original child `DASHI.Unified.TSFVUnifiedRegression`, preserving separate YM and TSVF/KK/OS owner roots.
- [x] Execute 2,764 equivalent exact Fraction checks of coupling/response/mass inverse BIDI; commit `scripts/check_tsfv_acoustic_impulse_mass_bidi_20261106.py`. This is a reference, NOT Agda.
- [x] Preserve 186 canonical IDs + 186 status entries; write 48-task five-phase execution crosswalk to 101 original canonical lemma IDs, inspect all IDs against the live original ledger.
- [x] Implement `scripts/run_tsfv_unification_maxcut_20261106.sh`, canonical Agda29 `parallel_checker` `--safe` source proof candidates, original YM/TSVF/combined roots, and CI source/reference/48-ledger checks.

## Exact remaining physical max-cut (do not mark complete)

- [ ] **S01** physically selected original microscopic TSVF pointer/environment with actual Born/ABL/non-signalling recorded observables (O01–O04).
- [ ] **S02** measured observer-local retarded response on the ORIGINAL source; the chosen oscillator impulse is only a control (O05–O06).
- [ ] **S03** independently produce a dimension-four continuum and a causal interval-volume estimate rather than assuming a cubic spatial graph (O07–O08).
- [ ] **S04** construct original hyperbolic propagator/null cone, unique selected timelike axis and calibrated spatial principal quadratic (O09–O12).
- [ ] **S08** genuinely complete and noncollapsed original complex observer Hilbert, Stone group, dense invariant core and self-adjoint Hamiltonian (H01–H05).
- [ ] **S09** source-state-preserving onto unitary from observer Hilbert to physically reconstructed YM/OS Hilbert; actual same H/domain, spectral projections, real/imaginary-time continuation and Wilson observables (H06–H12, B07). S07 original physical OS producer remains #1444 worker dependency.
- [ ] **S05** actual selected positive-radius smooth five-dimensional Einstein–gauge–matter action/solution, nonzero source stress or controlled matter-free scope, scalar/radion dynamics and KK modes (K01–K06).
- [ ] **S06** horizontal reduction equals the **independently measured** original observer metric, with observable/field/stress calibration and limits (K07–K09).
- [ ] **S10** full reverse/forward same-source BIDI, noninjectivity controls, cutoff/volume/history/KK limit commutation and quantitative comparisons (B01–B08).
- [ ] **S11** actual pinned-head Agda compiler and zero-meta/transitive trust reports, independent analytic proofs and physical measurement receipts (V01–V06). GitHub Actions has reported no runs for the #1460 branch; a workflow file is not acceptance.
- [ ] **Parent synchronization** on future #1444 commits: compare pinned donor head and repeat conflict-aware parent→child integration, never child→parent without independent YM owner's review.

**Required command via repository parallel_checker:** `AGDA_JOBS=4 bash scripts/run_tsfv_unification_maxcut_20261106.sh`. The wrapper invokes `scripts/run_agda29_parallel_check.sh` and manages its own compiler/cache/stdlib; do not invoke Nix or Agda directly. All files above have source GitHub readback but no actual Agda compiler receipt in this turn. The terminal full E1 theorem and Clay endpoint remain OPEN.
