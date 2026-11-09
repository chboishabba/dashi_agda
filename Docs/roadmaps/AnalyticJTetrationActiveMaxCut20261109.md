# Active max-cut: analytic Kneser × Bishop q × modular j × fine observers

**Controlling ledger:** 2026-11-09. **Branch:** `chatgpt/analytic-j-tetration-abel-transport`; **PR:** [#1478](https://github.com/chboishabba/dashi_agda/pull/1478). **Priority:** reuse source theorem → kernel proof → actual selected instance → numerical receipt. This page is the concise current cut; older progress chronology and complete declaration inventories remain in [AnalyticJTetrationAbelModularTransportRoadmap.md](AnalyticJTetrationAbelModularTransportRoadmap.md).

## Accepted evidence policy

- **Source-written** = declaration committed, **not** a typechecking certificate. Every new module from this PR currently falls into this class.
- **Locally executed rational Python** = exact finite arithmetic; not proof of a Bishop analytic identity.
- **Vendor/source-native existing Agda theorem** = a reusable declared proof, still not a fresh exact-head kernel receipt for #1478.
- **Original instantiated analytic gate** = inhabitant/proof on the actual Bishop complex / Kneser domain, **not** a record with assumed fields or a terminal model.
- **Complete** may be used only with exact Agda 2.9 head SHA, compiler invocation and exit receipt, and independently checked scientific/numerical inputs when required. No such receipt for #1478 has been observed.

## P0. Source integrity and compilation (first blocking gate)

| ID | Exact deliverable / lemma | Status | Original owner and acceptance criterion |
| --- | --- | --- | --- |
| P0.01 | `originalCurrentHeadGoldenKernelReceipt` | **OPEN** | Agda 2.9 safe-check complete import chain for new modules and all dependencies; record SHA/errors and repair them |
| P0.02 | Bishop (q)-series limit uniqueness API correction | **SOURCE-WRITTEN repair** | `AbelBishopQSeriesSetoidPeriodTransportExact.originalComplexSeriesLimitExtensional` now reuses vendored `BishopFiniteSeriesExtensionalityExact.termwiseEquivalentSeriesHaveEquivalentLimits` (commit `c2fdf65e`) |
| P0.03 | Bishop trajectory limit API correction | **SOURCE-WRITTEN repair** | `AbelBishopKoenigsTrajectoryDifferenceLimitExact.originalBishopKoenigsDifferenceConverges` now provides explicit limit/convergence pairs to `Sequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀` (commit `37ec86cc`) |

**P0 static source correction (2026-11-09):** discovered and repaired an invalid import form in five newly authored E8 modules. `Agda.Builtin.Equality` only supplies `_≡_`/`refl`; `sym`, `trans` and `cong` must come from `Relation.Binary.PropositionalEquality`. Patched `AbelE8HalfOddShellInvolutionExact`, `AbelE8ThetaParityProjectorExact`, `AbelE8RootE4FirstCoefficientExact`, `AbelE8RootTriadic243CountComparisonExact`, and `AbelE8GeneratedRootNormTwoExact`. Commits `e4a197df`, `3cf3e23c`, `d056195b`, `08b8af91`, `fdbc2267`. This removes a real static import error but does **not** constitute a kernel acceptance receipt.\n\n## P1. Local Schröder/Koenigs (highest-alpha analytic producer)

| ID | Exact remaining theorem | Status / dependencies |
| --- | --- | --- |
| P1.01 | `originalBishopPrincipalLogOnSeries` | **OPEN.** Construct actual principal log on a cut-avoiding Bishop-complex disk, not `PrincipalComplexLog` authority fields |
| P1.02 | `originalBishopLogInverseDiskIteration` | **OPEN.** Show original Bishop log is a self-map/contraction of rational disk, fixed point, and derivative/remainder bound |
| P1.03 | `originalBishopKoenigsIncrementMagnitude` | **OPEN.** Actual `p^n(Log^n(z)-p)` increment norm bounded by `(69/50)(311/1000)(552/625)^n|z-p|²` |
| P1.04 | `originalBishopKoenigsComponentAbsoluteSummabilityInstance` | **OPEN instance.** Existing `AbelBishopKoenigsGeometricAbsoluteExact` consumes quantitative component bounds and invokes vendored `Sequence.proposition-3-5` |
| P1.05 | `originalBishopKoenigsUniformCauchy` | **OPEN.** Instantiate existing native Cauchy-completion/telescoping/trajectory-limit source over entire selected disk with a **common** modulus |
| P1.06 | `originalSchroederHolomorphicLocalLinearization` | **OPEN.** Local uniform holomorphic limit, nonzero derivative/inverse and genuine Schröder equation |

Already source-written: original Bishop exponential↔series carrier and finite iterates, complex Cauchy completion, geometric absolute-summability compiler, increment-prefix telescoping and trajectory convergence. Exact rational interval/Koenigs-tail scripts passed in preceding turns, but their analytic premises must be proven on original Bishop complex.

## P1b. Abel and P1g. Global Kneser

| ID | Exact remaining theorem | Status / key donor |
| --- | --- | --- |
| P1b.01 | `originalPuncturedSectorLogBranchCocycle` | **OPEN.** Source-native nonzero χ and log branches, integer-valued winding, overlap corrections and actual Abel coordinate |
| P1b.02 | `originalSelectedAbelSemiconjugacyInstance` | **OPEN.** Instantiate existing `AbelSchroederLogCocycleTransportExact` on real χ/Log/multiplier; an abstract record is not the goal |
| P1g.01 | `originalKneserConjugatePairGlobalNormalization` | **OPEN.** Conjugate fixed-point pair, fundamental regions, analytic continuation, monodromy, real normalization and uniqueness |
| P1g.02 | `originalKneserSourceSelectedInverse` | **OPEN.** Nonconstant analytic tetration inverse satisfying `F(z+1)=exp(F(z))` and selected `F(0)=1` |

Reuse `OggPrimeFourierWindingExact` (#1140), `TernaryPantsRecursiveWreathActionExact` (#558), `RadixValuationStageBridge` (#1139) for **finite phase/branch/refinement tracking only**. Finite C3 winding does not prove integer analytic logarithm monodromy. Puncturing the modular Eisenstein lattice does not construct the punctured analytic Abel sector.

## P2. The actual Bishop q → E4/E6 → j path (parallel with P1)

| ID | Exact remaining theorem | Status / donor |
| --- | --- | --- |
| P2.01 | `originalBishopMachinQuarterConcreteTrigIdentification` | **OPEN.** `BishopMachinQuarterAngleBranchExact` already gives `4θ_M≈π_M`, `3/4<θ_M<11/14`, rational tangent `1`; need the **same sine/cosine** addition/tangent semantics |
| P2.02 | `originalBishopRound11MachinPiTrigPeriod` | **OPEN.** Prove `sin_B(2π_M)≈0`, `cos_B(2π_M)≈1` from P2.01. `BishopRound11ClassicalTrigObjectWeldExact` is itself conditional, not a theorem of this identity |
| P2.03 | `originalBishopComplexExponentialAddition` | **OPEN.** Original Bishop exp real Cauchy-product exists; derive complex exp addition using genuine Bishop trig addition and ring normalisation |
| P2.04 | `originalBishopQAtTPeriod` | **OPEN.** `q(τ)=exp_C(2π_M iτ)`, establish `q(τ+1)≈Cq(τ)` via P2.02/03 |
| P2.05 | `originalBishopQAtNormSquareRadius` | **OPEN.** Relate genuine original `exp_C(2π_M iτ)` norm square to existing `qRadius`, construct original `BishopUnitDiskQ` |
| P2.06 | `originalBishopQSeriesTPeriod` | **SOURCE-WRITTEN Round11 instance; analytic inputs OPEN.** `AbelBishopRound11QPeriodInstanceExact` fixes the actual Bishop `q(τ)` and `Tτ=τ+1`; P2.04 source q-period and P2.05 disk witnesses still unpaid |
| P2.07 | `originalBishopPuncturedFourierSameObject` | **OPEN.** Existing punctured `SL₂(ℤ)` lattice reindexing and normalized Eisenstein identity; original absolute sum, constants and q↔lattice Fourier correspondence still unpaid |
| P2.08 | `originalBishopJFromE4E6` | **OPEN.** Δ nonvanishing, inverse/quotient in same Bishop complex and j T-period; correct standard/Klein-j normalization |
| P2.09 | `originalRendererAbelWeldInstance` | **OPEN cross-path.** Same selected original Kneser Abel values must be valid upper-half-plane modular τ and same original renderer j object |

**New exact reusable bridge:** `AbelBishopMachinQuarterToQPeriodExact.agda` (2026-11-09): `originalBishopTwoPiEqualsEightMachinQuarter`, `originalRound11SelectedTwoPiIsEightMachinQuarter`, `originalRound11QPiIsActualMachin`, and literal original Bishop q source equality. **Source-written, no kernel receipt.** It removes constant-choice duplication, **not** the trig period problem.

Existing owners: `BishopMachinQuarterAngleBranchExact`, `BishopMachinPiArchimedesWindowExact`, `BishopRound11MachinSetoidComplexInstanceExact`, `BishopRound11ClassicalTrigObjectWeldExact`, `JInvariantBishopTrigUnitPhaseExact`, `JInvariantBishopUpperHalfPlaneEisensteinFromUnitPhaseExact`, `JInvariantBishopPuncturedLatticeEisensteinCompilerExact`, `JInvariantBishopUnitDiskEisensteinCompletionExact`.

## P2e. Original E8 theta → Bishop E4 (new cross-PR reuse)

**Important distinction:** E8 is the exceptional rank-eight root lattice; its theta series is a **weight-4** modular form and satisfies the classical identity `Θ_E8=E4`. It is *not* the weight-eight Eisenstein series `E8(τ)` (classically `E8=E4²`). The ordinary `E6` is weight six. Do not conflate the rank label E8 with a modular-form weight.

Original source owners found:
- `DASHI/Algebra/Trit/E8RootEnumeration.agda`: **actual generated** indexed 112 integer-shape + 128 even-sign half-shape root lists; executable duplicate/disjointness/parity checks, complete for its specified shape predicates; residual native E8 lattice-membership/norm/theta series still explicitly open.
- `DASHI/Physics/Closure/LilaE8ThetaJBridgeSurface.agda`: explicitly names `thetaE8EqualsE4`, q-normalization, lattice carrier and j identity as **unpaid** promotion leaves.
- `DASHI/Moonshine/JInvariantEisensteinIncrementCoefficientBoundExact.agda` and `JInvariantEisensteinBishopSetoidSeriesExact.agda`: genuine original `E4(q)=1+240σ3(1)q+...` coefficient source, original Bishop complex series.
- `DASHI/Moonshine/EisensteinDiscriminantWeight12Exact.agda` / `DeltaNormalizedWeight12SameObjectExact.agda`: already prove weight-twelve discriminant **transport** from original all-SL₂(ℤ) lattice Eisenstein transformation; `Δ=η²⁴` has an external pinned Lean closure, not the internal Agda same-Bishop-object lift.

**New source-written bridge:** `DASHI/Moonshine/AbelE8RootE4FirstCoefficientExact.agda` (commits `18283296`, `85d2adf5`). It consumes the original *generated list length* rather than the expected count as an assumed parameter and targets the first exact coefficient of the literal Bishop E4 source.

| ID | Exact remaining theorem / deliverable | Status |
| --- | --- | --- |
| P2e.01 | `originalE8GeneratedRootCount`: source E8 generated 240-element list | **SOURCE-WRITTEN**, reuses original `combinedIndexedRootsLengthIs240`; kernel pending |
| P2e.02 | `originalBishopE4FirstCoefficientIs240`: calculate source `e4IncrementCoefficient zero` | **SOURCE-WRITTEN**, relies on executable reduction of source divisor kernel; kernel pending |
| P2e.03 | `originalE8RootListEqualsE4FirstCoefficient`, `originalBishopE4FirstCoefficientMatchesE8RootCount` | **SOURCE-WRITTEN**, Agda kernel pending |
| P2e.04 | `originalE8NativeNormTwoRootsComplete`: all native E8 norm-two vectors correspond exactly to generated root list and no extra vectors | **OPEN**; shape completeness alone is not the native lattice characterization |
| P2e.05 | `originalE8ThetaCoefficientAllN`: construct native lattice theta `Σ_{v∈E8}q^{⟨v,v⟩/2}` and prove shell count `r_{E8}(2n)=240σ₃(n)` for **all n**, or use a genuinely same-source modular-forms dimension-one theorem | **OPEN** |
| P2e.06 | `originalBishopThetaE8EqualsE4`: transport the full analytic equality to the **same original Bishop unit-disk q carrier** | **OPEN**; matching first coefficient is necessary, not sufficient |
| P2e.07 | `originalBishopWeightEightE4Square`: only if the separately requested modular weight-eight `E8` is desired, prove `E8=E4²` on the same Bishop q carrier; **not** supplied by the E8 root-lattice first-shell calculation | **OPEN** |
| P2e.08 | `originalE8ThetaJDiscriminantWeld`: combine genuine theta/E4, existing E6 and original normalized Delta/j with nonvanishing, so the original E8/J carrier and renderer match | **OPEN** |
| P2e.09 | Pin Agda 2.9 acceptance of first-shell owner and transitive sources; no compiler receipt currently | **OPEN** |

**Revised P2 max-cut:** Bishop π/trig period → original q(τ) with unit-disk evidence → existing Bishop E4/E6; **parallel** native E8 theta identity (P2e.04–06) plus existing weight-12 discriminant → nonzero Δ and original same-object j → fine-level/Abel observer weld. E8 does not unblock P1 local Koenigs/Kneser itself. The existing generated 240 roots gives a **valuable first-coefficient negative control**, not the entire theta series.

### P2e continuation — finite native norm-two and higher-shell receipts (2026-11-09)

**P2e.04a SOURCE-WRITTEN, NOT KERNEL ACCEPTED:** `DASHI/Moonshine/AbelE8GeneratedRootNormTwoExact.agda` builds the explicit coordinate norm
`doubledSquaredNorm([d₁,...,d₈]) = Σ (2dᵢ)²`, with values `4,1,0,1,4` on `HalfTritIndexed`. It establishes:
- `allNormEightCheckSound`: any passing exact Boolean checker has an inductive `AllDoubledNormEight` witness for every root in the supplied list.
- `generatedE8NormEightCheckIsTrue` and `generatedE8RootsAllHaveNormTwo`: all actual 240 *generated* indexed roots have norm square exactly 2 (doubled norm 8).
- `integerGeneratedE8NormTwoShellCountIs112`, `halfGeneratedE8NormTwoShellCountIs128`, `generatedE8NormTwoShellCountIs240`: computes **actual norm-filtered shell sizes**, not just list lengths.
- `generatedNormTwoShellMatchesOriginalE4FirstCoefficient`: original filtered theta-root coefficient equals `JInvariantEisensteinIncrementCoefficientBoundExact.e4IncrementCoefficient zero`.

**P2e.04b FINITE EXACT ARITHMETIC REGRESSION (executed PASS):** `scripts/check_analytic_j_tetration_e8_theta_shells.py` independently enumerates the integer and half-integer E8 lattice coordinates by a finite DP constrained by `Σ dᵢ²=8n`, congruence `Σdᵢ ≡ 0 mod 4`, and coordinate parity. It verifies full shell coefficients **n = 0..8 only**, without floating point:

| n | Integer vectors | Half-integer vectors | Theta coefficient | E4 coefficient |
| --- | ---: | ---: | ---: | ---: |
| 0 | 1 | 0 | 1 | 1 |
| 1 | 112 | 128 | 240 | 240 |
| 2 | 1136 | 1024 | 2160 | 2160 |
| 3 | 3136 | 3584 | 6720 | 6720 |
| 4 | 9328 | 8192 | 17520 | 17520 |
| 5 | 14112 | 16128 | 30240 | 30240 |
| 6 | 31808 | 28672 | 60480 | 60480 |
| 7 | 38528 | 44032 | 82560 | 82560 |
| 8 | 74864 | 65536 | 140400 | 140400 |

**Remaining minimum mathematical cut (not replaced by finite checks):**
1. **P2e.04c** `originalE8GeneratedRootsExhaustNativeNormTwoLattice`: prove every original E8 norm-two vector is represented by the same 240-indexed enumeration, with actual lattice integrality and parity. Shape-completeness alone is insufficient.
2. **P2e.05a** `originalE8ThetaFunctionOnBishopUnitDisk`: construct the genuine original Bishop complex theta series for the full E8 lattice with convergence, transformation law and compatible `q(τ)`, not only generated roots.
3. **P2e.05b** `originalBishopWeightFourModularFormsDimensionOne` **or** `originalE8ThetaCoefficientAllN`: prove modular uniqueness `M₄(SL₂ℤ)=⟨E₄⟩` in the same original analytic carrier or a genuine all-n shell-count theorem. The repository search did not identify a completed owner for either.
4. **P2e.06** `originalBishopThetaE8EqualsE4`: *then* deduce global analytic equality, matching actual normalization, not just sampled coefficients.
5. **P2e.09** Kernel-check new Agda norm module on exact head. No Agda compiler available here; a successful executable DP is not an Agda receipt.

**Highest-alpha decision:** next P2e mathematical producer is the **native norm-two lattice exhaustion** and then the full theta modular transformation/dimension-one theorem. The 240↔243 count comparison is independent of that analytic proof.


### P2e highest-alpha all-shell theta parity cut (2026-11-09 continuation)

**New source-written owner** `DASHI/Moonshine/AbelE8ThetaParityProjectorExact.agda` (commits `6cc02621`, `71b2154e`).

The actual E8 lattice is the union of the integral even-sum and half-integral even-sum cosets. For each fixed theta coefficient index `n`, partition the integer vectors by doubled-coordinate sum residues `0`, `2` mod 4 (`I₀,I₂`) and the half vectors similarly (`H₀,H₂`). Parity projection gives
[
    r_{E8}(2n)=I₀(n)+H₀(n),quad
    [q^n]θ₃^8=I₀(n)+I₂(n),quad
    [q^n]θ₄^8=I₀(n)-I₂(n),quad
    [q^n]θ₂^8=H₀(n)+H₂(n).
]
The half-family involution reversing the first odd doubled coordinate `d₀↦−d₀` preserves squared norm and toggles residue class mod 4. Hence mathematically `H₀(n)=H₂(n)` for every n. The **formal Agda source** currently takes this equality as a field of `E8ShellParityCounts`; it has **not yet proved the involution on the actual Bishop/E8 unbounded lattice shell**.

Given that specific equality, new `e8ThetaSignedJacobiProjectorAllN` proves the subtraction-free exact Nat identity
[
  2r_{E8}(2n)+I₂(n)=
  ig(I₀(n)+I₂(n)ig)+I₀(n)+ig(H₀(n)+H₂(n)ig).
]
This is equivalent to the classical Jacobi theta decomposition
[
 Theta_{E8}=	frac12(artheta_3^8+artheta_4^8+artheta_2^8),
]
**only once** the genuine shell-count functions/series and sign interpretation have been instantiated. The source does not assert this analytic equation as proved.

- [x] **P2e.10** `thetaParityProjectorArithmetic`: all-Nat 3-variable ring identity via existing `Data.Nat.Solver`; **source-written, Agda 2.9 unchecked**.
- [x] **P2e.11** `e8ThetaSignedJacobiProjector` and `e8ThetaSignedJacobiProjectorAllN`: an all-index algebraic coefficient projector consuming an explicit half-parity-cancellation witness; **source-written, unchecked**.
- [~] **P2e.12** `originalE8HalfOddParityInvolution`: source-written **all-n involution and explicit two-sided maps between parity-selected half-shell types** in `AbelE8HalfOddShellInvolutionExact`: `flipFirstOddPreservesNorm`, `flipFirstOddReversesParity`, `flipSelectedHalfOddShell`, `evenHalfShellToOdd`, `oddHalfShellToEven`, `evenHalfShellTwoSidedOnCoordinates`, `oddHalfShellTwoSidedOnCoordinates`. These use unbounded odd doubled-coordinate magnitudes, NOT only norm-two roots. Still OPEN: original E8 coordinate equivalence, finite cardinality transfer `H₀(n)=H₂(n)` as selected count functions, and Agda acceptance.
- [ ] **P2e.13** `originalE8ThetaJacobiCoefficientSameSource`: define the actual `I₀,I₂,H₀,H₂` from the source lattice, prove their identification with the literal `θ₂^8,θ₃^8,θ₄^8` coefficients, and instantiate P2e.11 without axioms.
- [ ] **P2e.14** `originalBishopThetaJacobiE4Identity`: prove the selected Bishop theta constants and their quartic/eighth-power identities and normalizations match the source's `E4=1+240Σσ₃(n)q^n`; equivalently provide a source-native weight-four modular-form one-dimensionality theorem. This is the final true analytic identity leaf.
- [ ] **P2e.15** `originalE8ThetaConvergesAndReindexes`: justify infinite E8 lattice/theta sum convergence and the parity reindexing in **original Bishop complex** semantics, not only coefficientwise finite calculations.
- [ ] **P2e.16** Kernel-check the above new Agda source and exact-source independent theta regressions.

**Independent regression extended**: `scripts/check_analytic_j_tetration_e8_theta_shells.py` now checks exact θ₂/θ₃/θ₄ parity projections against E8 shell counts for `n=0..8` in addition to `240σ₃(n)`. I independently executed this calculation with the same parity/coordinate recurrence; nine indices passed. The new repository script was pushed but has not been executed via the pinned Agda acceptance harness here. Do **not** call any of these finite checks an all-n analytic theorem.

**Maximum cut improvement:** There is now an explicit binary choice for P2e: (A) pay the native E8 half-coordinate involution + Jacobi theta identities and convergence, or (B) prove actual theta modularity plus `dim M₄=1`. Avoid claiming both routes are independently required. The original Bishop Koenigs/Abel/Kneser and P2 q-period gates remain independently OPEN.


## P2f. Actual generated E8 root count 240 versus triadic 243

**Audited actual prior-art owners** (not inferred numeral analogies):
- `DASHI/Algebra/Trit/E8RootEnumeration.agda`: generated E8 indexed root lists, exactly 112+128=240 and shape-completeness/no-duplicate bridges.
- `DASHI/Moonshine/JInvariant369RHAtomicTriadicCoefficientCrossPollinationExact.agda`: `fourTritCountIs81`, `puncturedFourTritCountIs80`, `fiveTritCountIs243`, `twoFortyIsThreeTimesPuncturedFour`, plus a distinct RH primitive coefficient `kernelOIs243`. Its source explicitly forbids a non-proven T⁹→T⁵ marginal.
- `DASHI/Reasoning/Trialectic369DyadicLocalComplementFactorizationExact.agda`: actual *two-sided* 3×3 observer-matrix rechart into four local trits × five complementary trits. Its 243 complements are not E8 roots.
- `DASHI/Foundations/TernaryGolay/PuncturedPerfectCode.agda`: **different** independently proven appearance of 243: radius-two Hamming sphere size in the punctured ternary Golay code, yielding 729 × 243 = 3¹¹. Do not treat Golay error patterns, the five-trit observer and E8 root set as identical carriers.

**New original-source exact count lemma owner:** `DASHI/Moonshine/AbelE8RootTriadic243CountComparisonExact.agda`, commit `dd3a7bdc`:
- [x] **P2f.01** `originalE8GeneratedRootCountIs240` consumes actual *generated list length*, not a typed expectation.
- [x] **P2f.02** `originalFiveTritCountIs243`, `originalPuncturedFourTritCountIs80` reuse paid original source.
- [x] **P2f.03** `originalE8RootCountIsThreeTimesPuncturedFourTrit`, `originalE8RootCountPlusThreeIsFiveTritCount`, `originalFiveTritMinusThreeEqualsGeneratedE8Count` are exact cross-source Nat arithmetic.
- [ ] **P2f.04** `originalE8RootToFiveTritComplementEmbedding`: only if substantively needed, define an explicit 240-element subset of Kernel 5 (including the *selected three excluded* states), prove injection, exact image and a source-compatible inverse. **No such map is currently provided.**
- [ ] **P2f.05** `originalE8RootTriadicActionCompatibility`: to assert real E8/triadic geometry, exhibit and prove an action/symmetric form/inner-product-compatible map, not merely equality of cardinalities.
- [ ] **P2f.06** Pin Agda 2.9 --safe checker receipt for this module. Source-written only.
- [ ] **P2f.07** Full original `Θ_E8=E4` and Bishop `j` same-object remains **P2e.04–P2e.08 OPEN**, not closed by matching counts 240, 243 or 240σ₃(1).

**Implementation note (2026-11-09):** `AbelE8HalfOddShellInvolutionExact.agda` uses unbounded signed odd doubled coordinates `±(2m+1)` and proves the sign flip of the first coordinate is an involution, preserves `Σdᵢ² = 8n` and toggles the half-shell residue bit for every n. This is not limited to the 240 norm-two roots or n=0..8. The remaining cardinality equality is a finite-bijection/count bridge on the genuine E8 shell, not a fresh analytic assumption. Commits `ed248756`, `fd495b46`. **Source-written, no Agda kernel receipt.**\n\n**Additional implementation** commit `e8cdbb3d`: explicit `SelectedHalfOddShell n parity` and inverse parity-reversing maps, proving both composites recover the **exact original coordinate vector**. This is stronger than merely establishing a fixed-point-free sign flip; no arbitrary `H₀=H₂` field is needed on this constructed coordinate carrier. The next dependency is a true source-selected lattice-to-coordinate equivalence and finite-shell enumerator/cardinality transport.\n\n**Highest-alpha consequence:** the numerical bridge offers a finite negative-control consistency check across the E8 and 369 hyperfabric domains; it does *not* discharge the analytical Koenigs increment bound, all-shell E8 theta identity, or the Abel-to-modular fine-point lift. Avoid diverting the maximum cut to a forced 240↔243 bijection.

## P3. Relative-fine modular observers and refinement/RG

| ID | Exact remaining theorem | Status / donor |
| --- | --- | --- |
| P3.01 | `originalKneserToModularLevelLift` | **OPEN.** Original Abel point → true modular level-27 fine-point lift, not a finite label substituted for analytic point |
| P3.02 | `originalMovingLevelAbelWeldInstance` | **OPEN.** Apply original `JInvariant369CanonicalLevelObserverTowerExact` 27→9→3 translation law to P3.01 |
| P3.03 | `originalCoarseFineAnalyticRefinementNaturality` | **OPEN.** Commute the same analytic action with `CoarseFineRelativeFibreExact` and `RecoverableObserverRefinementTowerExact`, retaining relative-fine residual |
| P3.04 | `originalRGObservableTCompatibility` | **OPEN.** Instantiate `RGObservableInvariance` for a genuine modular action; observer-level compatibility need not mean fine-state equality |

Existing donors `JInvariantAnalyticJCoarseFineObserverExact`, `JInvariant369CanonicalLevelObserverTowerExact`, `JCoarseFineConsumerReductionBridgeExact`, `CoarseFineRelativeFibreExact`, `ObserverRefinementLatticeExact`, `RecoverableObserverRefinementTowerExact`. Their finite/abstract results are real prior art, not the original analytic fine-point instance.

## P4. Certified Kouznetsov comparison

| ID | Exact remaining theorem | Status |
| --- | --- | --- |
| P4.01 | `originalKouznetsovContourIntegralEvaluator` | **OPEN.** Actual published construction, branch and contour choices |
| P4.02 | `originalKouznetsovCertifiedNumerics` | **OPEN.** Interval/truncation/rounding/phase error bounds and critical locus exclusions |
| P4.03 | `originalKouznetsovRendererCalibration` | **OPEN.** Source-selected normalisation, observable and comparable contours; finite 369 colouring cannot replace analytic phase |

## Deliverables and acceptance

1. **D0 — Kernel-certified source**: exact PR head, pinned Agda 2.9 `--safe` checks, all altered declarations and imports; repair failures. **OPEN**.
2. **D1 — Original Bishop log/Koenigs**: P1.01–P1.06 nonconstant holomorphic chart. **OPEN**.
3. **D2 — Global Kneser and Abel**: P1b/P1g proofs. **OPEN**.
4. **D3 — Original modular q/j**: P2.01–P2.08 true same-Bishop-carrier source identities. **OPEN**.
5. **D4 — Fine/refinement compatibility**: P3.01–P3.04 true source-level lift. **OPEN**.
6. **D5 — Published contour certification**: P4.01–P4.03. **OPEN**.

**No silent promotion:** all phases remain open until their direct owner theorem exists, passes exact-head Agda, and their empirical dependencies (where applicable) are checked. The **highest-alpha simultaneous producers** are P1.01/P1.03 (actual Bishop log and Koenigs increment bound) and P2.01/P2.02 (same-source Machin-quarter trig identity). Mere wrappers or re-labeling existing conditional records are not progress on those leaves.

## Latest source implementation / verification delta

- Commit `c2fdf65e`: repaired original Bishop E4/E6 series-limit uniqueness by directly invoking the proven native finite-series extensionality theorem.
- Commit `37ec86cc`: corrected original Koenigs trajectory convergence transport to pass the explicit `(limit, convergence)` evidence required by Murray/Bishop `Sequence`.
- Commit `41598b59`: `AbelBishopMachinQuarterToQPeriodExact` proves the *selected same-source Bishop-real* `2π_M ≃ 8θ_M` from the existing `4θ_M ≃ π_M` theorem and pins the original Round11 `q` to that source; analytic period still OPEN.
- Commit `90357fc4`: `AbelBishopRound11QPeriodInstanceExact` specializes the earlier E4/E6 T-period compiler to `Tτ := τ +_C 1_C` and literal `round11MachinQAtForSeries`. No arbitrary q-valued map is admitted. The **two precisely unpaid inputs** are `periodEvidence` for the actual original q and `diskEvidence` on the upper half-plane; these are P2.04/P2.05. Source-written only.
- Commit `4005f4f7`: `scripts/check_analytic_j_tetration_golden_local.sh` runs fail-closed source hygiene then delegates to the repo's own pinned `scripts/run_agda29_parallel_check.sh --safe`. No local Agda or Nix executable available in this environment; it has **not** returned a kernel-green receipt.
- Source audit: `AbelOriginalMovingLevelObserverTransportExact` references real names/compatible result types from `JInvariant369CanonicalLevelObserverTowerExact` and `JInvariant369ModularLevelCuspObserversExact`. This is a static signature review, **not** formal typechecking nor a genuine Abel/modular point weld.


## 2026-11-09 continuation — norm-two exhaustion mathematical proof (commit 590d937a)

**New proof owner:** [E8NativeNormTwoExhaustionProof20261109.md](../proofs/E8NativeNormTwoExhaustionProof20261109.md).

**Mathematical result established for the standard E8 coordinate model:** norm-two vectors are **exhaustively** the 112 integral two-unit-coordinate vectors and 128 half-integral even-negative-sign vectors. This is an all-vector argument using integrality and the sharp lower bound on eight half-coordinate squares, not a finite coefficient regression. Exact cardinality: 240.

**Status: mathematical proof documented, original-source Agda weld OPEN.** The mathematical proof does not establish that the independently selected Agda E8 carrier is definitionally this coordinate model or that its generated list is complete for the native carrier. It is therefore **not** P2e.04c kernel closure. The immediate named proof obligations are:
1. \`originalNativeE8MembershipIffDoubledParityAndSumModFour\`.
2. \`originalIntegerNormEightImpliesTwoUnitCoordinates\`.
3. \`originalHalfNormEightImpliesAllUnitCoordinates\`.
4. \`originalHalfLatticeSumEvenIffEvenNegativeSigns\`.
5. \`originalE8GeneratedRootsExhaustNativeNormTwoLattice\`.
6. \`originalE8NativeNormTwoRootsComplete\` — derive original-carrier 240 count by the preceding lemmas.

**Already source-written in #1478:** \`AbelE8HalfOddShellInvolutionExact\` has an all-index norm-preserving parity-flipping involution, and \`AbelE8ThetaParityProjectorExact\` supplies the all-index coefficient algebra. Do not reopen the abstract H0/H2 cancellation as a new axiom. The decisive next P2e cut after source E8-carrier welding is actual finite cardinality transport into the Jacobi theta coefficients, Bishop analytic convergence/reindexing, and Jacobi-to-E4 or weight-4 modular uniqueness.

**Acceptance:** no new Agda module was compiled or claimed complete in this continuation. Pin a fresh exact-head Agda 2.9 \`--safe\` receipt before upgrading any P2e code status. P1 original logarithm/Koenigs, P2 source q-period/Delta nonvanishing, P3 actual level-27 lift, and P4 certified contours remain OPEN.


### P2e carrier correction — finite roots are not the infinite theta lattice

Direct audit of \`DASHI/Algebra/Trit/E8RootEnumeration.agda\`: \`E8IndexedRootCarrier = Vec HalfTritIndexed 8\` with coordinates restricted to the five symbols \(-1,-\frac12,0,\frac12,1\). It is a **finite norm-two root enumeration carrier**, not the unbounded coordinate lattice of the analytic theta series. The former may be equivalent to the **norm-two shell** of the latter, but cannot be equivalent to the entire lattice. Correct the proposed first lemma name to \`originalUnboundedE8LatticeMembershipIffDoubledParityAndSumModFour\` and separately define \`originalNativeNormTwoShellToFiniteIndexedRootEquivalence\`. Do not redefine the infinite theta sum as a polynomial over 240 root vectors. This correction is incorporated in the proof owner (commit \`b84a6015\`).


## 2026-11-09 P1 highest-alpha continuation: one-series producer, not E8 diversion

**Original deliverable remains** Kneser-normalized holomorphic tetration for the ordinary exponential, the original Bishop modular \`j\` observable, and analytic fine-observer compatibility. P2e E8/240/243 is an auxiliary route and does **not** outrank P1/P2.

**Committed mathematical proof:** [AnalyticKoenigsLogSeriesProducer20261109.md](../proofs/AnalyticKoenigsLogSeriesProducer20261109.md). On the actual original complex fixed-point disk, once \`Log(p)=p\`, \(|p|>137/100\) and the source-local branch identity are established, *the same* absolutely convergent \`log(1+w)\` series proves
\[
|Log(p+t)-p|\le(100/127)|t|<(4/5)|t|,\quad
|Log(p+t)-p-t/p|\le(5000/17399)|t|^2.
\]
The direct geometric majorant replaces the derivative-integral proof requirement. The corresponding Koenigs tail is bounded by \((4312500/1270127)(552/625)^N|z-p|^2\). These are exact rational constants, **not** computational substitutes for Bishop analytic premises.

**Exact new source dependency chain:**
1. \`originalBishopLogOnePlusPowerSeriesOnDisk\`: actual series and branch identity.
2. \`originalBishopLogOnePlusSeriesGeometricBound\`: majorant, actual setoid inequality.
3. \`originalBishopLogOnePlusSeriesQuadraticBound\`: majorant of k≥2 tail.
4. \`originalBishopLogInverseDiskIteration\`: instantiate contraction for actual Log and selected original fixed point.
5. \`originalBishopKoenigsIncrementMagnitude\`: instantiate the existing \`OriginalBishopGeometricComponentBounds\` with genuine component bounds.
6. \`originalBishopKoenigsUniformCauchy\`: consume existing \`AbelBishopKoenigsGeometricAbsoluteExact\`, \`FiniteTelescopingExact\`, \`TrajectoryDifferenceLimitExact\`; do not rewrite them.
7. \`originalSchroederHolomorphicLocalLinearization\`: holomorphic convergence, derivative 1, inverse and local Schröder equation.

**Interface audit:** \`DASHI/Analysis/PrincipalComplexLog.agda\` defines a \`PrincipalComplexLogBranch\` *record with supplied fields*, and \`PrincipalComplexLogRealization.agda\` constructs it from a \`PrincipalPolarAuthority\` *record*. Neither is by itself a new source-native proof of the \`log(1+w)\` expansion in the Bishop-complex series carrier. \`DASHI/Analysis/PowerSeriesTranscendentals.agda\` does have real exp/trig series convergence and functional laws but does not discharge this original complex log lemma. An adapter from either authority record is not acceptable evidence for gate 1 without constructing its original analytic inhabitant.

**Status:** ordinary-complex mathematical lemma documented; **Agda implementation/verification remains OPEN**. The critical next action is to prove the complex \`log(1+w)\` source identity and componentwise geometric domination using the vendored Bishop power-series and limit APIs. P1b winding and P1g global Kneser remain separately unpaid, as do original P2 q-period/Delta/j and P3/P4.


### P1 proof receipt and local checker integration (2026-11-09)

Added \`scripts/analytic_j_tetration_koenigs_log_series_majorant.py\` and invoked it from \`scripts/check_analytic_j_tetration_golden_local.sh\`. The equivalent exact rational test was run in this session and passed: \(100/127<4/5\), \(M=5000/17399<311/1000\), \(\beta=552/625\), and \(C=4312500/1270127\). The repository's newly committed version has **not** independently been executed in a checked-out exact-head environment; pinned Agda acceptance is OPEN. These arithmetic receipts test bounds conditional on the original analytic source identity; they cannot construct it.

**Next mandatory formal producer:** \`originalBishopLogOnePlusPowerSeriesOnDisk\` with the genuine principal-log same-object branch identity. Only after it is constructed should \`originalBishopLogInverseDiskIteration\`, \`originalBishopKoenigsIncrementMagnitude\` and the existing Cauchy/limit pipeline be promoted. No additional E8 numerical coincidences should preempt this cut.


## P1 implementation delta — native source term sequence (2026-11-09)

New Agda owner: \`DASHI/Moonshine/AbelBishopLogOnePlusOriginalSeriesExact.agda\`, added to the fail-closed pinned local acceptance target list. It now defines the actual **original Bishop-series-carrier** coefficients
\[
a_n(w)=(-1)^n\,\frac{w^{n+1}}{n+1},
\]
with positive denominator \`suc n\`, explicit alternating parity, real scalar multiplication of actual complex powers, setoid congruence, canonical componentwise series limit **when absolute convergence is provided**, and uniqueness of that limit via the existing Bishop convergence backend.

**What this closes at source-written level:** the identity of the exact intended coefficient sequence; it does not replace the analytic logarithm by an arbitrary selected map, and it fixes the denominator-minus-one pitfall in raw \`mkℚᵘ\` by using standard \`_/_\` with nonzero denominator. It reuses existing Bishop complex powers and limit machinery, not a new formal authority.

**What remains genuinely OPEN and highest priority:** prove \`originalBishopLogOnePlusAbsoluteConvergenceOnDisk\` (original componentwise domination of these exact coefficients), \`originalBishopLogOnePlusPrincipalBranchIdentity\` (the series limit agrees on the actual cut-avoiding disk with the selected original principal logarithm), and \`originalBishopLogOnePlusSeriesQuadraticBound\` (original Bishop norm/order majorants). These then supply actual Koenigs increment bounds for \`AbelBishopKoenigsGeometricAbsoluteExact\`; derive uniform convergence, derivative and local Schröder chart from the existing backend. P1b/P1g global branch and Kneser gluing are still open. P2 authentic q/Delta/j and P3 observer weld remain separate original-task gates.

**Verification:** source written to PR #1478; no Agda binary or local Nix environment was available in the execution container. The new Agda module is **not yet kernel-accepted**; potential compile errors require the pinned Agda checker, and must not be concealed.


### Exact P1 convergence reuse: no new norm-power induction

For \`originalBishopLogOnePlusAbsoluteConvergenceOnDisk\`, reuse \`DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact.powerEnvelopeFromNormSquare\`, with the actual \`w=t/p\` and \`normSqC(w) ≃ ratio²\`, and \`DASHI.Foundations.BishopPolynomialGeometricDominationConvergenceExact.scaledGeometricSeriesConvergent\` plus the existing \`Sequence.proposition-3-5\` comparison proof. The power-envelope already gives both componentwise \`|re(w^(n+1))| ≤ ratio^(n+1)\` and \`|im(w^(n+1))| ≤ ratio^(n+1)\` from one norm-square certificate. The *specific remaining source inequalities* are (a) \`|(-1)^n/(n+1)| ≤ 1\` in Bishop reals, (b) componentwise scalar-product order transport for \`originalBishopLogOnePlusTerm\`, (c) original \`w=t/p\` reciprocal/norm-square witness, and (d) \`ratio<1\` on the selected disk. Once these are paid, the existing \`BishopComplexSeriesConvergenceExact.complexSeriesLimitConvergence\` constructs the actual series limit, and uniqueness is already source-written in the new module. The principal-branch identity remains a **separate**, nontrivial analytic result. No extra authority record or independent theta construction is required for P1.


## P1 direct convergence producer — 2026-11-09 19:11+10 continuation

**Implemented source:** \`DASHI/Moonshine/AbelBishopGeometricPowerSeriesExact.agda\` (PR #1478). For the *actual* original Bishop complex power sequence \`powC w (suc n)\`, with independently proved \`Unit.BishopUnitIntervalRatio ratio\` and \`normSqC w ≃ ratio²\`, the module reuses \`BishopComplexNormSquarePowerEnvelopeExact.powerEnvelopeFromNormSquare\` to establish pointwise **both-component** bounds by \`ratio^(suc n)\`. These are transported through the existing \`OriginalBishopGeometricComponentBounds\` and \`BishopPolynomialGeometricDominationConvergenceExact.scaledGeometricSeriesConvergent\`/Bishop comparison to supply \`ComponentwiseAbsoluteSeriesConvergent\`, a canonical complex series limit and a convergence certificate. A definitional theorem \`originalBishopLogPowerTermSameSource\` identifies the *power factor* of the alternating-log terms with this very sequence; no parallel complex carrier is introduced.

**Status: source-written / exact-head Agda unverified**, added to \`scripts/check_analytic_j_tetration_golden_local.sh\`. The source does **not** yet establish the absolute convergence of \`(-1)^n w^(n+1)/(n+1)\`; that additionally requires \`originalBishopLogCoefficientMagnitudeAtMostOne\` and \`originalBishopLogCoefficientScalarMagnitudeMono\` for original Bishop reals. The former should derive from rational \(0<1/(n+1)\le1\), not from a free property field; the latter uses Bishop \`∣x*y∣≃∣x∣*∣y∣\` and multiplication order. Then instantiate \`AbelBishopKoenigsGeometricAbsoluteExact.originalBishopKoenigsComponentAbsoluteSummability\` on the literal log coefficients.

**Remaining analytic obstruction, not to be hidden by convergence alone:** prove the original principal branch identity \(\operatorname{Log}(p+t)-p=\sum_{n≥0}(-1)^n(t/p)^{n+1}/(n+1)\) in the selected Bishop complex, with selected \(p\), an actual inverse and cut-avoiding domain; then derive contraction and remainder, Koenigs limit, Abel winding, global Kneser normalization. The separate true Bishop \(q\)-period and \(E_4/E_6/\Delta/j\) remain on the original objective's parallel route.


## P1 progression — original Bishop logarithmic-series convergence source-written (2026-11-09)

**New direct owner:** \`DASHI/Moonshine/AbelBishopLogOnePlusCoefficientDominationExact.agda\`. Its \`originalBishopLogCoefficientMagnitudeAtMostOne\` reuses the already-existing source lemma \`DASHI.Foundations.BishopNegativeExponentialInterlacingExact.unitReciprocalBelowOne\` (plus source reciprocal nonnegativity and the Bishop absolute-value/negation laws) to prove **for the literal alternating coefficient** \(|(-1)^n/(n+1)|\le1\) for every \`n : Nat\`.

**New composition:** \`originalBishopScalarMagnitudeAtMostOne\` uses the Bishop absolute-product law, nonnegative multiplication order, and unit identity. \`originalBishopLogRealComponentBelowGeometric\` and \`originalBishopLogImagComponentBelowGeometric\` turn the **actual** \`originalBishopLogOnePlusTerm w n\` into geometric majorants using the independently source-defined power envelope. Thus \`originalBishopLogOnePlusAbsoluteConvergenceOnUnitDisk\` has no caller-supplied coefficient inequality, and derives \`Complex.ComponentwiseAbsoluteSeriesConvergent\` under a **genuine norm-square unit-disk certificate**. Canonical Bishop logarithmic *series limit* and convergence are then constructed; the exact function name is \`originalBishopLogOnePlusCanonicalLimitOnUnitDisk\`. **Source-written; Agda kernel acceptance pending.**

This is **real progress on P1.01b**, not on P1.01c. The principal-branch identification \`originalBishopLogOnePlusPrincipalBranchIdentity\` remains OPEN: it must prove that the constructed series is the selected original principal \`Log(1+w)\` on a cut-avoiding disk, not name it \`Log\`. The further original fixed point / inverse \(w=t/p\) / contraction / Koenigs increment and holomorphic limit are still OPEN until source-instantiated. No Kneser global continuation, Bishop \(q\)-period / \(\Delta,j\), level-27 observer or Kouznetsov contour gate has been closed.

**Verification:** source committed to PR #1478 and pinned local Agda checker target list amended; no exact-head Agda 2.9 \`--safe\` acceptance has been obtained in this session. This proof must be marked SOURCE-WRITTEN, not kernel-complete, until checked.


### P1 branch-independent highest-alpha route (2026-11-09 continuation)

Inspecting \`DASHI.Analysis.InverseLogarithmFromExponential\` and \`DASHI.Analysis.PrincipalComplexLogRealization\` confirms these are **authority-parametric** (the former for positive real exp, the latter for polar complex log); they do not pay the concrete original Bishop-complex principal branch. We can avoid making an independent principal-log construction a *prerequisite* for local Koenigs as follows:

1. Take the now source-written absolutely convergent actual series \(L(w)=\sum_{n\ge0}(-1)^n w^{n+1}/(n+1)\) for a genuine unit-disk radius certificate. **OPEN \`originalBishopLogOnePlusExpInverseOnUnitDisk\`:** derive \(\exp_C(L(w))≈_C1_C+w\) by the actual power-series derivative/Cauchy-product recurrence and Bishop limit transport, not a record asserting inverse.
2. **OPEN \`originalBishopLocalLogAtSelectedFixedPoint\`:** for the actual fixed point \(p\), source-construct a nonzero inverse \(p^{-1}\) and let \(g(z)=p+L((z-p)/p)\) on \(D(p,1/10)\); prove \(\exp_C(gz)≈_Cz\) using original Bishop exp addition and \(\exp_C(p)≈_Cp\). This supplies a *local inverse* without first identifying a global principal Log.
3. **OPEN \`originalBishopSelectedLocalLogBranchIdentifiesPrincipal\`:** only when a principal-branch claim is requested, show that this \(g\) has the selected strip/continuation normalization and hence agrees with original principal Log. This is a later uniqueness/branch-selection seam, not a prerequisite for local Schröder if the local inverse suffices.
4. The existing norm bounds and Koenigs geometric/Cauchy/telescoping machine can consume the resulting original \(g\). Still prove the fixed point, reciprocal/radius certificate, uniform holomorphic limit and inverse function theorem on the Bishop carrier.

This is a genuine dependency reduction, not a claim that \(\exp_C L(w)=1+w\) has been formalized. An analytic inverse identity remains essential; a record with fields \`expLog\`/ \`logExp\` is not a substitute. All P1b/P1g global Kneser, P2 original modular \(q/\Delta/j\), P3 moving observer and P4 contours remain open.
