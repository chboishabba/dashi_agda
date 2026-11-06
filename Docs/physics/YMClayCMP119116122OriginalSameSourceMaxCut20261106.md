## 6 November — YM-only all-word R445/OS and published Wilson RP (source implementation)

Two pre-existing, source-written finite Wilson results on the separate #1460 branch have been adapted as **YM-owned** Agda sources on #1444, with no dependency on TSVF/observer/KK:

1. `YMClayOriginalR445ReflectedAllWordGramExact.agda`: `actualNativeR445AllReflectedWordGrams` proves that the *original 1,024-bond fine Wilson-Gibbs measure* and its exact non-Abelian R445 pushforward give the same real reflected pairing for **any two finite coarse-observable words**. `originalFineOSPositiveTransfersToNativeR445` transports a nonnegative original pairing to the same native coarse pairing.
2. `YMClayOriginalR445PublishedWilsonRPWordWeldExact.agda`: `originalPublishedWilsonRPYieldsNativePositiveWord` invokes the existing `BalabanClayOSWilsonReflectionPositivityExact` published Osterwalder–Seiler / Menotti–Pelissetto owner, to infer positivity of the original R445 reflected word **under the literal original-to-published Wilson reflected-expectation identity, gauge invariance, positive-time admissibility and scalar order interpretation**.

Both are imported by `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda`; original donor/provenance retained.

**Do not promote a named imported theorem as a concrete Wilson RP instantiation:** the published owner is a `WilsonReflectionPositivityData` record of theorem premises, not a literal constructed analytic continuum Wilson measure. Source-specific `sourceIdentifiesActualWilsonReflection`, reflection plane/support, real-to-complex OS star and positivity under physical cutoff/volume limits still need proof. All-word pushforward is **not** CMP116 decay or an OS mass gap.

M.01 actual closed `refl` kernel candidates remain in `YMClayNativeClosedThreeEqualitiesCandidateExact`, not a compiler receipt. M.02 original CMP119/122 complete-density equality, M.03 selected differentiated uniform CMP116 estimates, M.04 literal physical reflection/RP/limits, and M.05 nontrivial R4 OS reconstruction and strictly positive physical gap remain *unpaid*. This change neither resolves the Clay theorem nor imports any observer/KK theorem.

**Verification:** GitHub source commit/readback only; exact-head Agda `parallel_checker` receipt not obtained.

---
## 6 November — finite ORIGINAL Wilson reflected cross-Gram transport (new source theorem)

The existing original same-source native R445 OS pullback has been strengthened to **two different real observables**, not merely the quadratic diagonal. New declarations in `YMClayOriginalWilsonNativeOSPullbackExact.agda`:

- `originalFineOSCrossGram`: original fine Wilson reflected bilinear expectation `E_mu[(Theta_f f) g]`.
- `actualR445CoarseOSCrossGram`: original weighted R445 pushforward expectation `E_B*mu[(Theta_c F) G]`.
- `originalR445CrossGramIsFineWilsonCrossGram`: exact finite equality for all coarse real tests `F,G` when the *literal* native block intertwines the selected reflections.

This is derived by the same existing Haar cylinder congruence, unchanged Wilson density and unchanged partition, using the actual native non-Abelian block. It does **not** assume a separate covariance, a bare coarse Wilson weight, or isolated CMP122 crossing-fragment positivity.

**Status:** source-written; not Agda-kernel accepted. `NativeBlockReflectsExactly` is still an explicit premise, as are the selected ordered Haar laws. Full fine Wilson RP, positive-time support preservation, complex adjoint transport, physical CMP119/122 whole-form identification, cutoff/volume limits, CMP116 localization and the same continuum OS spectral gap remain unproved for the selected original family. No such gate is marked closed by this finite Gram identity.

**Next strict max-cut:** instantiate native reflection geometry and fine Wilson RP on the original gauge-invariant positive-time algebra, then transport the full Gram matrix through the complete CMP119/122 source/continuum; in parallel complete M.01 kernel receipt and M.02/M.03 selected-source and uniform-rate applications. Keep the pure 4D YM chain independent of TSVF/KK/observer claims.

---
## 6 November correction: same ORIGINAL R445 reflected OS form, no per-polymer PSD tax

New physical-source Agda owner `DASHI/Physics/YangMills/YMClayOriginalWilsonNativeOSPullbackExact.agda` defines the real two-point reflected quadratic forms **from the exact original fine 1024-bond Wilson–Gibbs normalized expectation and its exact R445 native weighted pushforward**, not from independent fine/coarse reflection forms.

- `originalR445ReflectedQuadraticIsFineWilsonQuadratic` proves the **literal whole-form equality** `Q_coarse(F) = Q_fine(F ∘ B)` using the existing original product-Haar weighted cylinder congruence and the single selected same-source partition.
- `originalR445OSReflectionPositiveFromSameFineWilson` derives `Q_coarse(F)≥0` from the original selected Wilson fine reflection positivity and the physical block's positive-time support and reflection-equivariance properties. This is restricted to the chosen **real** gauge-invariant test algebra; a general complex OS statement must also transport its adjoint.
- **Reuse already present:** `BalabanClayExactOSPullbackRecombinationExact`, `BalabanClayOSPullbackBlockingBridgeExact`, `BalabanReflectionPositiveCoarseGrainingTransportExact`, and `ReflectionPositiveBlocking`. Their general RP transport does NOT demand each separately labelled CMP122 crossing-polymer term be positive.
- **Exact unpaid geometry/source:** establish for the *literal native R445 ordered two-link block* that `NativeBlockReflectsExactly` holds at the selected OS plane and that coarse positive-time observables pull back to fine positive-time observables, together with original real Wilson fine RP (standard imported finite Wilson theorem). Then prove equality of the FULL reconstructed CMP119/122 reflected OS form with this original coarse pullback after recombination, including crossing terms. An Eq.1.100 absolute crossing bound alone neither proves nor disproves whole-form RP.

**Revised M.04:** do not require an unnecessary separate PSD theorem for each crossing-polymer summand if the selected entire original OS form is reflection-positive by exact source pullback. The genuinely new quantitative tasks remain the cutoff/volume-uniform CMP116 marked bound and physical RG/T5/OS limit.

**Acceptance:** source-written / no Agda kernel receipt / original exact field and selected reflection semantically uninstantiated; no Clay promotion.

---

## 6 Nov latest max-cut: ORIGINAL TWO-PLAQUETTE MARKS / WHOLE R445 SOURCE / F19 EFFECTIVE FIBRE

**Implemented on PR #1444 (source-written; Agda kernel unverified; no CI claim):**

1. `YMClayOriginalWilsonTwoPlaquetteMarkedSourceExact.agda` derives `originalPlaquetteMarkGaugeInvariant` and `originalPlaquetteMarkPointwise` directly from the *actual* periodic SU(N) plaquette holonomy and real trace. The marked source `actualOriginalTwoPlaquetteNormalizedSource` has an original-gauge-invariance proof `actualTwoPlaquetteSourceIsGaugeInvariant`, the exact normalized moment-polynomial theorem `originalTwoPlaquetteActualMomentPolynomial`, and the original real-Wilson covariance `originalTwoPlaquetteMixedJetIsActualWilsonCovariance`. This works on **every changing finite cutoff n**, not just the fixed 1,024-link side-four sample. Local insertion traces and real Haar are still typed physical inputs, not a constructed Borel SU(N) matrix implementation.
2. `YMClayOriginalWilsonNativeMarkedPushforwardExact.agda` proves for the actual side-four native 1,024-link full Gibbs family that `fineWilsonMarkedPartitionIsNativeR445Pushforward` and `fineWilsonNormalizedMarkedIsActualR445Normalized`: these are equalities of the **entire two-variable original marked partition**, not merely its mixed coefficient. `originalMarkedR445IsSameFiniteMomentPolynomial` composes existing exact real-division/numerator laws; `originalNativeR445MarkedSourceGaugeInvariant` retains the original native coarse-gauge law. No fictitious bare coarse Wilson density.
3. `YMClaySUNOriginal64Pair896MarkedEffectiveSourceExact.agda` specializes **existing** full noncommutative weighted fibre disintegration F17/F18/F19 to the entire two-marked polynomial on the actual 64 original disjoint ordered link pairs **plus all 896 spectators**. `originalFullTwoMarkedFibreEqualsActualEffectiveDensity` proves the fully interacting fine/true effective density equality; `originalSamePartitionNormalizedMarkedSource` uses the **same** partition on both sides; `originalSelectedEffectiveMarkedDensityStrictlyPositive` derives strict positivity from the original positive fine weight and existing Haar laws. This all-arbitrary-weight theorem still needs the native 1024-bond codec/reordering witness to identify the interleaved F19 carrier with literal original Wilson coordinates.

**Exact finite bridge now completed at source level:** full marked source on selected native Wilson -> its genuine R445 weighted pushforward -> existing R320 covariance; literal positive plaquette marks on every finite original cutoff; F19 64+896 effective density with an arbitrary coupled interacting weight. Generic source differentiation already exists in `YangMillsClayPinnedCMP119RealTwoJSourceExact`, `BalabanObservableIndexedT5SourceMeaningRound403Exact`, `BalabanCMP116SelectedJCommonDomainRound327Exact`, and the bounded finite compact-SU(N) analytic proof in `YMClayR320BoundedMarkedSourceLemma20261106.md`. It is *not* a fresh research lemma.

**True selected physical cut, exact owner obligations:**

| ID | Original theorem to produce | Reuse | Current status |
| --- | --- | --- | --- |
| `M.01` | Selected 1,024-link permutation program equality reorders the **actual** original positive-bond decoder into the 64 native ordered block pairs and 896 spectators, with same Haar product and full Wilson weight | `YMClayNativeClosedThreeEqualitiesCandidateExact`; `YMClayNativeSideFourPairSpectatorSortProgramExact`; F17/F18/F19 | Agda candidate, kernel not confirmed |
| `M.02` | Exact original selected 4D continuous SU(N) Borel Haar, normalized trace and finite matrix interpretation, original CMP119/122 **full** E/R/B/V/ghost/background `rho_k = T_k e^{-S_k^{eff}}` and selected R-operation integral equals native weighted Wilson pushforward at every physical scale, including reflection supports | `SUNMatrixCarrier`; `YMClaySUNVariablePhysicalCutoffFamilyExact`; `BalabanCMP119Section2CompleteDensityDictionaryExact`; `BalabanCMP119Section2FiniteDensityEvaluationExact`; CMP122 Eq.1.100 | **Physical same-source theorem**, not supplied by the finite algebra |
| `M.03` | Actual marked plaquette/loop insertions and root/time/support on the **same renormalized** CMP119/122 density are admissible CMP116 coordinates; published selected CMP116 differentiated localized response inequality applies to them uniformly | `BalabanCMP116SelectedTwoSourceLocalizationRound454Exact`; R327, R342, R344, R467; literal WEXT; new two-plaquette owner | **Decisive analytic application**, not another `D^2\log Z=Cov` rule |
| `M.04` | Original differentiated shell envelope with physical units and `a\to0,L\to\infty` quantitative tails; whole-form OS pullback through a reflection-compatible native block, not positivity of each CMP122 crossing summand | `BalabanStepVMarkedSourceDirectClusteringProducerCurrentExact`; R445/T5/Bishop; `BalabanCMP122ROperationReflectionSupportCutExact` | **Physical uniformity/reflection** |
| `M.05` | Noncollapsed, non-Gaussian 4D OS reconstruction of **that same continuum source**; local density/cyclicity, original self-adjoint H, strictly positive physical mass gap and full externally selected compact-simple group scope | R479/R482, R333, `YMClayRGLossBudgetToNonGaussianExact`, OS endpoints | **Continuum/Clay endpoint** |

**Important falsifiers:** a formal 2-J jet does not prove spatial decay; a bounded analytic plaquette source does not prove CMP116 localization; a one-step weighted pushforward need not be bare Wilson; F19 interleaved pairs do not automatically equal the original native 1024-bond vector; an absolute crossing-polymer bound does not imply reflection positivity; an OS gap on a mismatched Hamiltonian is not a Clay mass gap. Treat each as BIDI-negative unless the original physical source equality is proved.

---

### Native original finite-source implementation (6 November follow-on)

`DASHI/Physics/YangMills/YMClayOriginalWilsonAffineMarkedPartitionExact.agda` now defines the *actual unnormalized* variable-cutoff original SU(N) Wilson product-Haar marked source, not an independently supplied response oracle, and source-writes:

\[
Z^{\mathrm{aff}}_{n}(s,t)
=\int \rho_n(U)(1+sF(U))(1+tG(U))\,dH_n(U)
= Z_n+sN_n(F)+tN_n(G)+stN_n(FG).
\]

The source terms `originalAffinePartitionIsExactNumeratorPolynomial` and `originalNormalizedAffineIsLiteralMomentPolynomial` derive the corresponding unnormalized and normalized polynomial equalities from the pre-existing actual original product-Haar integration laws and real-division algebra. Thus, where the selected real division has its **standard positive-denominator field laws**, the actual finite normalized source has coefficients \(1,E_nF,E_nG,E_n(FG)\). The already existing normalized-cumulant proof then derives \(\partial_s\partial_t\log Z(0,0)=\mathrm{Cov}_{\mu_n}(F,G)\). For a bounded *exponential* marked source the same Taylor coefficients follow by the finite compact-Haar dominated-convergence proof already given above. No fresh source-independent calculus or "finite derivative mystery" is required.

This is not the full CMP116 *localized renormalized* source application: CMP119/122's E/R/B/V/ghost/background effective density, exact selected polymer root/support, uniform marked localization, physical-rate calibration, RG crossing positivity and continuum/OS limit still require the source-specific proofs. Source-written Agda is not a green kernel receipt.

## 6 November 2026 correction — the FINITE analytic-J identity is NOT a new Clay leaf

The previously reported "formal jet -> actual analytic mixed derivative" should not be presented as an independent, unproved *mathematical* theorem for bounded finite original Wilson marks. The rigorous finite continuous-compact-Haar proof was already written in [YMClayR320BoundedMarkedSourceLemma20261106.md](../physics/YMClayR320BoundedMarkedSourceLemma20261106.md): for each finite original Wilson Gibbs law and bounded local marks F,G, M(s,t)=E_mu exp(sF+tG) is holomorphic on a uniform nonzero neighbourhood, and (d_s d_t log M)(0,0)=E_mu(FG)-E_mu(F)E_mu(G). For |F|,|G|<=2, |s|+|t|<log(2)/2 is sufficient. Uniform *analyticity* is not uniform *spatial clustering*.

**New genuine same-source finite integration proof:** `YMClayOriginalWilsonAffineMarkedPartitionExact.agda`, with `originalAffinePartitionIsExactNumeratorPolynomial`, directly constructs the ORIGINAL unnormalized Wilson product-Haar marked integral
`Z_aff(s,t)=int exp(-S)(1+sF)(1+tG) dH`
and proves equality to `Z_0+s N(F)+t N(G)+st N(FG)` using the EXISTING integration/numerator linearity theorems. The two source marks are the actual Wilson observables, not a second J oracle. Consequently the affine and exponential source have the same first and mixed derivatives at zero by elementary bounded analytic differentiation. The existing `YMClayOriginalWilsonFiniteTwoSourceJetExact`, `BalabanObservableIndexedT5SourceMeaningRound403Exact`, `NormalizedTwoSourceConnectedCumulantExact` and `BalabanCMP116SelectedJCommonDomainRound327Exact` already own the coefficient, covariance, observable-index and common-domain compilers. **Status:** original integral polynomial equality SOURCE-WRITTEN, not Agda-kernel-accepted; bounded exponential derivative analytic theorem proved in source-facing mathematical dossier, not yet a native Bishop/Agda differentiability proof.

**Do not retain finite derivative calculus as a new independent physical gap.** The next source-specific mathematical obligation is different: identify the COMPLETE renormalized CMP119/CMP122 effective density and exact selected marked insertion with the actual original Wilson source at each scale (including E/R/B/V, boundary/ghost normalization), then instantiate CMP116's published *localized* mixed-source estimate on those precise original supports, with a cutoff- and volume-uniform physically calibrated distance/rate. An arbitrary compact plaquette has a bounded analytic source; that alone says nothing about decay between two distant plaquettes. Existing R342/R344/R467/R482 and literal two-Wilson quarter-dyadic authors compile the subsequent bound/gap only after those physical estimates and limit semantics are supplied.

**Remaining maximal physical cut:**
- `Y.01/R445`: original Wilson positive-Haar/Gibbs source ↔ actual CMP119/CMP122 complete E/R/B/V/ghost/background density and RG pushforward, including reflection-compatible crossing R-terms, all changing cutoffs/volumes.
- `Y.02/R320`: select the original two local/loop insertions as admissible CMP116 analytic marks of *that same renormalized density* with exact root/support and source-time calibration. The generic finite mixed derivative is ALREADY accounted for.
- `Y.03/T5`: pay original cutoff/volume-uniform connected rooted-shell response, quantitative physical RG drift/defect tails and the same expectation limits; reflection positivity through the physical R-operation.
- `Y.04/R333/Clay`: reconstruct one noncollapsed four-dimensional Euclidean/OS theory with same H, dense local physical sector, strict positive gap in real units, nontriviality and the externally prescribed compact simple gauge-group scope.

No independent abstract J calculus, generic new KP/RG proof or artificial coarse Wilson measure is an admissible replacement.

---

## 2026-11-06 follow-on: finite original Wilson two-source jet (Y.01/Y.02)

**Golden source:** `DASHI/Physics/YangMills/YMClayOriginalWilsonFiniteTwoSourceJetExact.agda`, in parent [PR #1444](https://github.com/chboishabba/dashi_agda/pull/1444). **Independent exact reference:** `scripts/check_ym_original_wilson_two_source_jet_reference.py`. Canonical TOE import, dedicated physical root `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda`, and targeted Agda CI now name the two finite source owners. The physical root is deliberately not `--safe`, because the legacy real/Haar analytic authorities are a transitive proof boundary. No Agda kernel or transitive trust receipt has been observed.

| Exact ID | Source term | Status and remaining physical payment |
| --- | --- | --- |
| `Y.FIN.01` | `originalWilsonDensityIsSelectedWilson`, `originalWilsonPartitionIsSelectedProductHaar`, `originalWilsonFiniteIntegrationLaws`, `originalWilsonUnitNumeratorIsPartition`, `originalWilsonInsertionNumeratorAdd`, `originalWilsonExpectationOfUnitIsOne` | Source-written: literal changing-cutoff SU(N) Wilson/Gibbs density and partition are anchored to the *same* previously constructed finite product-Haar measure; finite numerator additivity and unit partition follow from existing cylinder algebra. The unit-normalization proof additionally takes an explicit positive-denominator division-cancellation law; one-link compact Borel Haar realization is still an explicit input. |
| `Y.FIN.02` | `originalWilsonMomentAlgebra`, `originalWilsonNormalizedJet`, `originalWilsonLiteralJetDirections` | Source-written: define the formal two-source coefficients directly from one original finite Wilson normalized expectation; no independent moment/covariance object. The *analytic derivative* of the actual continuous-Haar source functional is not inferred. |
| `Y.FIN.03` | `originalWilsonMixedJetIsSameFiniteCovariance`, `originalWilsonMixedJetIsOriginalConnectedCumulant` | Source-written: literal finite formal mixed-log jet equals the same Wilson connected covariance by the original cumulant compiler. Kernel acceptance pending. |
| `Y.FIN.04` | `check_ym_original_wilson_two_source_jet_reference.py` | Exact rational BIDI reference: 19,683 exhaustive three-state cases and six simultaneous relabelings; changed-measure negative control rejected. This is not an SU(N) Haar integration or Agda check. |

| `Y.FIN.05` | `YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact.originalVariableN3IsNativeR445FineMeasure`, `originalN3CumulantIsNativeBlockedFineCovariance`, `originalN3LiteralMixedLogJetIsNativeBlockedCovariance`, `originalN3LiteralMixedLogJetIsActualR320PushforwardCovariance` | Source-written: at actual side-four n=3 the variable-cutoff Wilson measure is definitionally the original R445 1024-link fine Gibbs law. Both source marks pull back along the original non-Abelian native block; the finite jet equals the actual *weighted* R445→R320 pushforward covariance. No bare-coarse Wilson-law assertion or analytic CMP116 source bound. Kernel pending. |

**Revised original physical max-cut (do not promote from Y.FIN):** `Y.01` identify the entire real Wilson/gauge-fixed E/R/B/V/ghost/counterterm source with the selected CMP119/122 density/physical T-operation at every renormalization scale, not just the original finite Wilson action. `Y.02` prove that selected positive-time gauge-invariant local/loop insertions are admissible CMP119/116 analytic J directions, identify the genuine differentiated `log Z` with this formal jet, and preserve root/distance/normalization. `Y.03` derive *actual* cutoff/volume-uniform source decay, RG/continuum tails and reflection-compatible limits. `Y.04` construct the same limiting OS Hilbert/Hamiltonian and quantitative nontriviality/Clay scope. Reuse the CMP119/122/116, R344/R467/R482, Bishop/T5 and original Wilson–Gibbs owners rather than copying them.

**Acceptance:** new formal theorem = `SOURCE_PENDING_AGDA`; reference arithmetic = `VERIFIED_REFERENCE`; original CMP116 source applicability and physical estimates = `OPEN_PHYSICAL`. CI is a checker command, not a green receipt. Parallel-checker exact-head execution and transitive axiom audit remain required.

---

## 6 November follow-on: the LITERAL TWO-WILSON half-power donor is already source-owned

Further source audit found `BalabanLiteralTwoWilsonQuarterDyadicCompletionExact.agda` (not an abstract common-J envelope). Its **already existing** `literalTwoWilsonEmbeddedQuarterDyadicDecay` proves, for a `QuarterDyadicTwoWilsonSource` on the exact selected finite T5 covariance,

```text
embed |Cov_(mu_{a,L})(W_left,W_right)|
  <= embed ((1/4) * (1/2)^euclideanTime)
```

by composing the original literal two-Wilson marked expansion, the selected R429 mixed log, connected-support geometry, residual dyadic physical calibration, a rational-real ring embedding and the source amplitude `<= embed(1/4)`. **This is an important stronger specific donor than a new generic KP proof.** It still requires the actual original continuous Wilson/Haar generating functional, physical support and uniform selected amplitude inputs, not a mere type-matching change of carrier.

The source-first route has two competing real code producers:
- **R344 shared marked Hessian** -> literal R342 -> R467 -> R482, with selected J, source-time equality, hessian (C_H<=1).
- **Literal two-Wilson quarter-dyadic** -> existing finite T5 physical covariance bound, with original two Wilson insertions, R429/trace/source ring embedding, physical separation and (A_{\rm src}<=1/4). After verifying *same covariance carrier and same physical selected time*, use existing R479/R482 continuum/OS consumers, not a substitute transfer kernel.

No independent generic exponential source estimate or physical-q assumption should be added on top of either. The BIDI comparison must identify the original two Wilson source and R344's selected analytic J pair as the same generating functional, or explicitly record them as different test families.


---


### 6 November R344 finding: the canonical CMP116 q=1/2 shell is ALREADY source-implemented

`BalabanCMP116SharedMarkedDirectCalibrationRound344Exact` does not need a second generic exponential-carrier construction. Its existing `SharedMarkedDirectCMP116Source` gives the physical selected two-J/Hessian source with
\[
\text{markedAnalyticShell}(d)\le\tfrac14 C_H\,2^{-d},
\quad C_H\le1,
\quad d_{\rm source}=t_{\rm selected},
\]
and the selected spectrum's `quarter*halfPower(time)` envelope. **These are input fields to instantiate on the actual Wilson measure, not a new externally verified continuum rate.** The module already constructs `R342.LiteralTrajectoryCMP116Source` directly from R344. Its explicit selected physical source-facing leaves are (a) `literalSelectedDifferentiatedLocalization`, (b) `selectedSourceDistanceIsTime` with calibrated physical units, and (c) `hessianAnalyticConstantAtMostOne`.

New terms appended to `YMClayCMP119122116SelectedProducerWeldExact.agda`:
- `sameOriginalSharedMarkedHalfRateFiniteDecay`: **R344→R342→R467**, exact finite connected covariance upper, without invented q;
- `sameOriginalSharedMarkedHalfRateYieldsGap`: **R344→R342→R467→R482**, selected transfer gap with rate-based positive-energy semantics and selected-limit closure, no independent positivity token.

These are **SOURCE-WRITTEN, AGDA KERNEL UNVERIFIED** and preserve selected physical q/time as proof-relevant input. They do **not** magically establish the full physical rate at arbitrary lattice spacings: `d_source=t` must mean the appropriate physical time calibration, and the actual original same-Wilson marked source must supply the R344 assumptions. The local source crosswalk checker now audits **12 owners and 6 new proof terms**. This is a stricter, lower-debt completion route than generic block-Dobrushin q if Y.01/Y.02's actual original-source identification is proved.


---

# CMP119 + CMP116 + CMP122 on ONE original Wilson source: exact max-cut audit
**6 November 2026 • YM parent PR #1444 • Golden Agda owners • source-head audit at 191590060b56b19644662fc3e0a9421238082bb3**

## Correction to the earlier max-cut
Do **not** start by proving fresh CMP119 RG, CMP122 nonlinear UV stability, CMP116 cluster/localization, KP summation, or normalized-log/covariance algebra. The repository already has source-indexed owners for all these, much of it with precisely the source-first arguments required. Build the *original Wilson–Gibbs specialization* to their hypotheses, then project their existing results. A published theorem authority and a `machineChecked` compiler under a record premise are not the same as a source-specific witness to that premise.

The literal Agda core of the new source-conserving wiring is `DASHI/Physics/YangMills/YMClayCMP119122116SelectedProducerWeldExact.agda`:

1. `cmp119122BetaAndCMP116PotentialSameSource`: from ONE `BetaDrivenCompleteDensityInputs` and its actual `BetaDrivenLocalizedEffectiveActionFamily`, constructs the **conjunction** of the literal beta-history coupling identity and the CMP109/116 localized component-sum equality for that exact CMP119 density. It does not introduce a second density or new mass-gap measure.
2. `sameLiteralR342SourceFiniteCovarianceDecay`: existing `R342.LiteralTrajectoryCMP116Source` → `asPublishedLiteralSelectedLocalization` → **literal R467 original selected connected-covariance physical envelope**.
3. `sameLiteralR342SourceYieldsR479TransferGap`: the SAME source, plus the already-owned selected limit and energy semantics, gives the R479 positive transfer-gap core without an independent R467 record.
4. `sameLiteralR342AndLocalRateYieldsGap`: uses R482/R301 to *derive* candidate positivity from the SAME reconstructed spectrum's local rate, avoiding the extra arbitrary positive-gap token.

These are **source-written proof terms awaiting Agda kernel acceptance**, and still require the actual R342 input on the selected Wilson family. They are intended to delete duplication from the proof graph, not to promote a conditional source to the Clay endpoint.

## Exact source-producer and consumer audit

| Source / owner | Already source-written or standard imported | Narrow actual source-specific equation to instantiate |
|---|---|---|
| `Balaban1989BetaDrivenCompleteDensityFlowExact` | `betaDrivenCompleteDensityFlow`, coupling identity and smallness from original finite beta history | `WilsonDensityAt(a,L) = selected CMP119/CMP122 densityAt(k)` including Wilson trace, gauge fix/ghost, full E/R/B/V and Jacobians when the source action uses them |
| `BalabanPublishedUVStabilityNonlinearRGCoreExact` + `BalabanCMP122PublishedFourDimensionalUVStabilityExact` | published nonlinear UV stability/active Section-2 invariant under the selected source hypotheses, not a new generic one-step stability theorem | physical chosen Wilson/ghost/Haar/background and exact effective-density `ActiveEffectiveDensityFlow` representation, including CMP119↔CMP122 carrier dictionary |
| `BalabanCMP119PhysicalTOperationWeldExact` | assembled density equals physical localized T-operation on a typed input; nonnegativity and finite slow field realizers derived | original source assembled density = selected physical T-operation and strict positive support on original same density |
| `BalabanCMP119AnchoredNormalizedExpectationSourceExact` | published anchored numerator/denominator cancellation + localized normalized expectation (CMP119 Sect. 3) | actual renormalized Wilson/local physical insertion belongs to that very analytic anchor class |
| `BalabanCMP119CMP122BoundaryReinjectionSourceExact` | CMP119 boundary analytic/localized terms; CMP122 large-field R-operation reinjection preserves the source class | literal periodic polymer/boundary/domain dictionary; **do not re-prove published boundary mechanism** |
| `BalabanCMP116119NormalizedExpectationDerivativeRound281Exact` | published differentiated normalized expectation + mixed log/connected covariance adapter | selected physical two insertions map to the source's exact two J coordinates, root and support distance |
| `BalabanCMP116SelectedJApplicabilityRound309Exact` | source theorem vs selected T5 J-applicability split, not artificial covariance | actual original gauge-invariant local test pair is an admissible CMP116 marked pair on SAME density |
| `BalabanCMP116LiteralTrajectorySourceRound342Exact` → `BalabanCMP116LiteralTrajectoryToPublishedLiteralR467Exact` | common-domain/selected marked-source pipeline; R342→R467 compiler already source-written | `literalSelectedDifferentiatedLocalization` for that original pair AND physical envelope `sourceEnvelopeBelowSpectrumEnvelope` with a cutoff-/volume-uniform positive physical decay rate |
| `BalabanCMP116PublishedLiteralRateToGapRound482Exact` | R467 plus selected local energy/rate semantics constructs positive transfer gap, avoiding arbitrary positive-energy token | actual OS spectral generator, physical time units, density of selected local modes, no invisible lower-energy sector |
| `BalabanCMP122ROperationReflectionSupportCutExact` | literal positive/negative/crossing source polymer classification, equation (1.100) envelope on crossing | **actual crossing-kernel reflection-positivity theorem**: mere exponential bound is not PSD |
| `BalabanClayT5TypedContinuumDefectCauchyExact` | explicit dyadic defect telescope and fast-Cauchy real already exists | same original Wilson-renormalized observable at adjacent cutoffs, actual defect bound, signed telescoping and physical measure representation |
| `BalabanClayT5BoundedWeakCompactnessRound439Exact` + `BalabanClayT5SameFamilyContinuumRecoveryRound425Exact` | Markov/Prokhorov/full selected convergence and same-family OS compilation under exact source premises | literal physical compact-containment witness, determining weak-test algebra, actual expectation topology and RP-preserving limit |
| `BalabanClayPlaquetteNoncollapseContinuumCalibrationExact` + `BalabanClayT5CumulantLowerBoundNontrivialityExact` | explicit positive OS norm and uniform cumulant survival implications | same original Wilson lower certificates and counterterm/tail losses with verified sign/units |
| `YangMillsDirectSourceOSSameHGapExact` | explicit same-OS-H and gap attachment, physical distinction admitted | instantiate the selected original continuum source and the physical same-H + local sector/density, not a second abstract Hamiltonian |

**Prioritization correction:** the source-native marked-pair CMP116 path is the default B route. The supplementary Dobrushin/Perron physical-cube path is an alternate *sufficient* route, not an extra mandatory assumption. The CMP119 anchored expectation route is already better aligned with the one-step UV defect needed for the T5 Bishop real than an invented generic Lipschitz estimate.

## Four genuine same-object proof cuts remaining after imported mathematics

### Y.01. Original finite Wilson→CMP119/CMP122 exact carrier + action
For all selected cutoffs, volumes, field configurations and legal source gauges establish an explicit original equality (or a correctly measured gauge-fixed change of variables)
\[
\mathbb E_{\mu_{a,L}^{\rm Wilson}}[F] =
\frac{\int F_{\rm selected}\, e^{-S_{119/122}(A,E,R,B,V)}\,d\nu_{\rm phys}}
{\int e^{-S_{119/122}(A,E,R,B,V)}\,d\nu_{\rm phys}}.
\]
Do not pretend `RealAnalysisAxioms`, a `OneLinkProductHaar` record or two equal types prove this. For original compact SU(N), verify actual Borel Haar, measurable gauge factors, original decoder, partition positivity and noncommutative blocking; reuse the already implemented 1,024-link C3/64-pair/896-spectator code. If gauge fixing includes ghosts, demonstrate determinant/BRST/Ward compatibility, not an independent gauge-fixed measure assumption.

### Y.02. Literal selected insertions→published CMP119/CMP116 mark class
Construct the functions `sourceJLeft`, `sourceJRight`, `sourceRoot`, `supportDistance` from the actual physical local/loop observable. Prove the selected two derivatives are those of **the same original partition function** and source estimates. Reuse R281, R309, R342, R467 and the current new R482 direct compiler. This is an equality of source, coordinates and physical support—not only a name match.

### Y.03. Quantitative UV/IR *physical* tail and reflection compatible limit
Derive source-specific anchored expectation defects (sum_k epsilon_k(F)<\infty) and two-marked source envelope (C_F e^{-m d_{\rm phys}}), both with constants independent of cutoff/volume and explicit operator renormalization. Boundary reinjection and large fields must be included in the source density. The companion typed T5 defect theorem already turns defects into Bishop fast Cauchy, while R467/R482 consumes literal CMP116. Separately prove the **crossing** R-operation contributions preserve positivity of the reflected Gram form. Convergence of a positive matrix of source labels is insufficient without the same physical reflected test algebra.

### Y.04. Continuum noncollapse + OS/Clay semantics
From SAME selected source show a lower OS norm and a nonzero signed fourth cumulant, actual weak/Schwinger limit and Euclidean invariance, local field/test space, stress/Ward, OS same generator and full local spectral density. Derive (H_G|_{\Omega^\perp}\ge m_G I) in physical units and prove the group-indexed construction for the prescribed compact simple gauge groups. This is not delivered by a source `ProofLevel = machineChecked` under uninstantiated fields.

## BIDI acceptance and falsifiers
- **FWD 119/122→116:** a selected physical density and two legal source J coordinates must reproduce the exact original mixed second log derivative, connected covariance and source envelope.
- **BWD 116→119/122:** every marked source root/domain appearing in the supposed physical bound must trace to the selected Wilson density/physical T-operation and *the same* beta history, with no ungrounded source-independent envelope.
- **FWD 122→OS:** every reflected finite Gram matrix stays PSD after selected RG/blocking and cutoff limit; test crossing R-polymers explicitly.
- **BWD OS→122:** every physical OS local insertion and its RG predecessor must lie in the claimed CMP119/116 analytic family with correct renormalized normalization.
- **Control:** a real symmetric 2×2 kernel with entries $\begin{bmatrix}1&2\\2&1\end{bmatrix}$ has all positive entries but a negative quadratic for (v=(1,-1)); pointwise positive/decaying weights alone do not imply reflection positivity.
- **RG:** require actual original nonperturbative `q<1` or CMP116 two-marked physical rate at fixed physical `ell`. Stagewise q<1 and a bare-link high-temperature bound do not suffice.

## Verification/phase status
New three-way bridge source is **AGDA_SOURCE_PENDING** and is wired to `DASHI/Unified/BalabanRGTOERegression.agda` and `.github/workflows/ym-native-maxcut-exact-agda.yml`. No Agda binary/Nix is available in this runtime and no kernel green receipt is claimed. The finite source same-object 1,024-link goals are separate. The physically original Y.01–Y.04 source-witness obligations are nontrivial; the published CMP119/116/122 theorem operators and existing formal adapters should NOT be rewritten as new subprojects.

**Attribution:** Bałaban CMP119 (1988), CMP116 (1988), CMP122 (1989); Kotecký–Preiss; Menotti–Pelissetto; Osterwalder–Schrader; repository donors as listed above. This dossier is a new source-conserving assembly and acceptance cut, not a claim to have proved their original theorems or the Clay endpoint.
