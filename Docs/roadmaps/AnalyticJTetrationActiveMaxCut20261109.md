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

## P1. Local Schröder/Koenigs (highest-alpha analytic producer)

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
