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

## 6 November 2026 — CMP119/CMP116/CMP122 source-first ORIGINAL-WILSON maximum cut

**Canonical deep audit:** [CMP119/116/122 same-original-source and BIDI dossier](../physics/YMClayCMP119116122OriginalSameSourceMaxCut20261106.md). **New golden code:** `DASHI/Physics/YangMills/YMClayCMP119122116SelectedProducerWeldExact.agda`. **Static readback contract:** `scripts/check_ym_cmp119116122_same_source_contract.py` (11 existing golden owners, 4 new source-written proof terms, source-drift/CI/conditional-status checks). The repository has substantial CMP119, 116 and 122 machinery already: do not re-prove Bałaban's general source theorems, normalized covariance algebra, KP, beta history, Prokhorov or OS implications.

| Exact gate | The actual source-wide equality / analytic witness | Direct prior owner | State |
|---|---|---|---|
| **Y.01 original density** | Selected *continuous original* Wilson/Gibbs/Haar block field, full E/R/B/V/ghost/source action and selected coupling equal source-native CMP119/CMP122 finite density/physical T-operation on every cutoff; actual Borel and gauge change-of-variables | `Balaban1989BetaDrivenCompleteDensityFlowExact`, `BalabanPublishedUVStabilityNonlinearRGCoreExact`, `BalabanCMP119PhysicalTOperationWeldExact`, `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact` | Original-physical equality **OPEN**, beta-source + localized-potential conjunction **SOURCE-WRITTEN** |
| **Y.02 literal marks** | SAME original selected gauge-invariant observables, analytic CMP119 anchored insertions, CMP116 J_L/J_R, support/root distance and exact normalized mixed-J log derivative | `BalabanCMP119AnchoredNormalizedExpectationSourceExact`, `BalabanCMP116119NormalizedExpectationDerivativeRound281Exact`, `BalabanCMP116SelectedJApplicabilityRound309Exact` | Original mark dictionary **OPEN**, existing analytic theorem **REUSED** |
| **Y.03 physical rate & limit** | Instantiate R342 literal localization and physical envelope on the selected Wilson family at arbitrary UV cutoff/volume; CMP122 boundary reinjection and actual R-operation crossing reflection positivity; selected T5 Bishop fast-Cauchy/weak measure identification | `BalabanCMP116LiteralTrajectorySourceRound342Exact`, `BalabanCMP116LiteralTrajectoryToPublishedLiteralR467Exact`, `BalabanCMP116PublishedLiteralRateToGapRound482Exact`, `BalabanCMP122ROperationReflectionSupportCutExact`, `BalabanClayT5TypedContinuumDefectCauchyExact` | R342→R467→R482 **SOURCE-WRITTEN**; original localization/rate, crossing RP and physical measure **OPEN** |
| **Y.04 one nontrivial OS/Clay theory** | Original same-limit OS generator and dense local sector, noncollapsed plaquette norm and nonzero cumulant, true Euclidean invariance/locality, correct full group quantifier and uniform physical gap | `BalabanClayT5SameFamilyContinuumRecoveryRound425Exact`, `BalabanClayPlaquetteNoncollapseContinuumCalibrationExact`, `BalabanClayT5CumulantLowerBoundNontrivialityExact`, `YangMillsDirectSourceOSSameHGapExact` | Conditional implication **SOURCE-OWNED**, physical witnesses **OPEN** |

**Four code terms:** `cmp119122BetaAndCMP116PotentialSameSource`, `sameLiteralR342SourceFiniteCovarianceDecay`, `sameLiteralR342SourceYieldsR479TransferGap`, `sameLiteralR342AndLocalRateYieldsGap`. Each is an actual composition of existing Agda theorem owners; no new independent mass-gap Hamiltonian/constant. For the stronger R482 pathway the energy-positivity token is NOT a separate premise; it follows under the source's selected local energy/rate semantics. **Agda kernel receipt pending**.

**P0 execution focus:** kernel-accept the actual original 1,024-bond C3 and pair/spectator proof candidates and this new source bridge; prove Y.01/Y.02 original action/mark dictionaries; then pay selected CMP116 **physical** rate and CMP122 crossing RP in Y.03. Dobrushin q<1 is an optional parallel sufficient route, not mandatory when CMP116 direct rate is available. Source-published CMP122 UV stability is not itself the selected 4D continuum Clay construction. Never upgrade `standardImported` + uninhabited `conditional` fields into `VERIFIED_PHYSICAL`.

---


**2026-11-06 D2/D3 precise Bishop interface:** `YMClayRGLossBudgetToNonGaussianExact` distinguishes rational `charge : Nat→ℚ` **lower enclosures** from the true physical `actualFiniteCumulant : Nat→Scalar`. The source theorem demands `selectedFiniteChargeLower : embed charge(n) ≤ actualFiniteCumulant(n)` and `actualCumulantConverges` in the actual completed real/Bishop carrier; cannot promote rational toy data to a physical Gibbs expectation. `referenceRGUniformNoncollapse` is the new derived mathematical lemma, `asOriginalT5Nontriviality` compiles the real selected T5 nonGaussian consumer (kernel still pending).


---

## 6 November 2026 — same-original-Wilson constructive 4D continuum steelman / BIDI max-cut

**Primary theorem proposal:** [YMClayConstructive4DContinuumSteelman20261106.md](../physics/YMClayConstructive4DContinuumSteelman20261106.md). It explicitly derives the hypothetical nontrivial 4D continuum from ONE original compact-simple-G Wilson family, not six unrelated records, and proposes source-specific bounds for same-observable UV Cauchy limits, IR/crossing tails, literal CMP116 mixed-J decay, OS reconstruction and non-Gaussian survival. The existing R443/R445/R320/R333 owners are reused; unification #1460 remains downstream.

**New golden producer:** `DASHI/Physics/YangMills/YMClayRGLossBudgetToNonGaussianExact.agda` (source-written, **Agda kernel pending**): `finiteRGLoss`, `referenceChargeBelowCurrentPlusLoss`, `referenceRGUniformNoncollapse` from a reference `eta+B≤c0` and actual `c_n≤c_{n+1}+δ_n`, `sum_{k<n}δ_k≤B`; `asOriginalT5Nontriviality` instantiates the EXISTING T5 uniform fourth-cumulant lower theorem with this **derived** finite bound; `continuumRGChargeIsNonzero` imports existing T5 nonzero result. This does not construct the original source-specific charge/limit, and cannot assign a fictitious fourth-cumulant sign.

**Physical RG insight to test, not assert:** after actual 4D marginal and source renormalization, an original Wilson/CMP119/122 one-step residual may obey `δ_n≤A/((n+1)(n+2))+C 2^{-(n+1)}+h_n`, `Σ h_n≤H`; this gives `q≤q0+A+C+H<1` via the *existing* `YMClayPhysicalRGDriftToUniformInfluenceExact`, while bare O(g²) harmonic sums diverge. The actual Ward cancellation/marginal subtraction and full large-field/marked-J source error remain to be proved.

**Executed independent exact rational BIDI controls** (all illustrative, NOT physical): 192-step RG noncollapse, 64 exhaustive bounded charge configurations and 5 negative cases; 4×4 transfer Hankel Gram PSD, 128-step noncollapse and 7 false-positive negative controls; the UV rational n^-2+geometric+holes sum checked at depths 1,2,4,8,16,64,256,512, with a divergent harmonic control. The fixture `q0=1/4, A=1/16, C=1/32, H=1/64` gives `q=23/64`; NO Wilson measurement or Agda acceptance is inferred. New scripts `check_ym_rg_noncollapse_steelman.py`, `check_ym_clay_continuum_bidi_controls.py`, `check_ym_marginal_subtracted_uv_tail.py` committed and targeted by CI. Golden TOE root imports the new Agda module.

**Exact deliverable IDs (do not rename; promote only with physical proof receipts):**
- `CLAY4.F1`
- `CLAY4.A1`
- `CLAY4.A2`
- `CLAY4.A3`
- `CLAY4.B1`
- `CLAY4.C1`
- `CLAY4.C2`
- `CLAY4.D1`
- `CLAY4.D2`
- `CLAY4.D3`
- `CLAY4.E1`
- `CLAY4.E2`
- `CLAY4.E3`

**Status:** `CLAY4.D2` source-written mathematical compiler, Agda pending; `CLAY4.D3` derived conditional transport to T5, Agda pending; `CLAY4.F1` source-written original closed 1024-label candidates, kernel pending. `CLAY4.A1/A2/A3/B1/C1/C2/D1/E1/E2/E3` are physical same-source analytic or semantic construction work, NOT realized original continuum theorems. No CLAY endpoint acceptance claimed.

**Highest alpha execution order:** original one-step marked source/Dyadic Cauchy `A1/A2` and two-marked physical CMP116 shell `B1/C1/C2` in parallel, then one fixed-scale nonGaussian `D1/D2/D3`, exact original RP/OS/E(4) `E1/E2` and per-G `E3`; native `F1` kernel independently. Fail on unproved physical input rather than selecting a toy model.

---

## 2026-11-06 — executable finite and RG-drift implementation / acceptance audit

**YM-owned branch:** #1444 only. #1469 parent reconciliation was merged; #1460 remains observer/KK/OS unification and is not imported into the parent. The other worker's separate physical-observer results do not pay any YM continuum or R443–R333 theorem. Keep all original Wilson/Fubini/Haar/CMP116/UV owners.

### F1: three real closed Agda computations (not merely Set aliases)

New `DASHI/Physics/YangMills/YMClayNativeClosedThreeEqualitiesCandidateExact.agda` contains actual proof attempts:
- `originalC3SelectabilityClosed : Decide.originalC3SelectableBooleanGoal` by normalized `refl`;
- `originalC3CanonicalLabelsClosed : C3Sort.constructedNativeC3CanonicalLabelGoal` by previously source-written structural sort correctness and first proof;
- `originalPairSpectatorLengthClosed : PairSort.originalPairSpectatorLengthGoal theory` by normalized `refl` on selected original 64-pair/896 spectator list;
- `originalPairSpectatorSelectabilityClosed : Decide.originalPairSelectableBooleanGoal theory originalPairSpectatorLengthClosed` by normalized `refl`;
- `originalPairSpectatorCanonicalLabelsClosed : PairSort.originalPairSpectatorCanonicalLabelGoal theory originalPairSpectatorLengthClosed` using the same native original structural sorter.

**There are exactly three original equality targets:** C3 canonical-vector, pair/spectator length and pair/spectator canonical-vector (two separate Boolean selection prerequisites). These candidate proof terms are imported into `DASHI/Unified/BalabanRGTOERegression.agda` and demanded by `.github/workflows/ym-native-maxcut-exact-agda.yml`. The actual original 1024-bond Python reference and 5914 exhaustive smaller permutations PASS; no Agda kernel/typecheck receipt is present, so status remains **SOURCE_CLOSED_CANDIDATE_UNVERIFIED**, not `VERIFIED_AGDA`. The `refl` candidates may fail or time out; if so fix against compiler diagnostics, never suppress the certificate.

### Physical R445/R320: derivation of a uniform q from UV RG error budget

**New** `YMClayPhysicalRGDriftToUniformInfluenceExact.agda`: defines `finiteRGDrift`, `SelectedPhysicalRGInfluenceBudget` and proofs `selectedRGInfluenceBelowFiniteDrift`, `selectedRGInfluenceUniformPhysicalUpper`, `selectedRGInfluenceUniformStrictMargin`. It implements exact induction for:

```text
kappa_0 <= q0
kappa_(n+1) <= kappa_n + delta_n
sum_(k<n) delta_k <= B  for ALL n
q0+B < 1
---------------------------------
for ALL n: kappa_n <= q := q0+B < 1 .
```

`YMClayRGDriftOriginalGibbsInstantiationExact.agda` then *constructs* an indexed finite conditional family `Cube.OriginalPhysicalCubeConditionals` with common `q=q0+B` by proof transport through the preexisting rational normalized-row Dobrushin owner. No independent global q field is chosen in this constructor. Source is **AGDA_UNVERIFIED and PHYSICALLY_CONDITIONAL**.

The exact original physical obligation now decomposes into three non-interchangeable proofs:
1. `UV.P01`: selected actual full SU(N) Wilson (continuous Borel Haar) Gibbs pushforward and regular conditionals on the SAME original chosen physical cube. **Current rational finite-fibre record does not itself encode equality to the original continuous measure.** Build a genuine physical measure-to-conditional kernel weld or a valid approximation with cutoff-uniform TV error.
2. `UV.P02`: bound `kappa_0<=q0` for that physical source at reference fixed physical `ell`; establish `kappa_(n+1)<=kappa_n+delta_n` on the SAME conditional family for every cutoff and volume. A β(a) bare-link perturbation that grows cannot silently inhabit this premise.
3. `UV.P03`: derive `sum_(k<n)delta_k<=B` uniformly in n (and L), e.g. a source-proved geometric-polymer envelope `delta_k<=A theta^k` with `0<=theta<1` gives `B=A/(1-theta)`; check strict `q0+B<1`.

**Exact rational independent fixture (NOT the Wilson source):** `q0=1/3`, `A=1/12`, `theta=1/2`, so `B=1/6`, `q=1/2`. `scripts/check_ym_rg_drift_budget_reference.py` executed 128 exact Fraction refinements, exact geometric partial-sum equality and 5 negative controls PASS.  No source-Gibbs/OS interpretation or compiler receipt is inferred from this fixture.

**Critical distinction:** `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact` constructs a selected original weighted *positive functional*, not a regular conditional probability or a density on a continuous measurable carrier. `YMClaySUNWeightedDisjointPairFibreReparamExact` supplies weighted finite fibre identities under one-link Haar algebraic prerequisites, not a full SU(N) Borel measure. `BalabanCMP116PublishedLiteralSelectedRound467Exact` provides the correct literal source ABI, but its `literalSelectedCMP116Localization` and `sourceEnvelopeBelowPhysicalClusteringEnvelope` are physical fields without constructed original-source witnesses.

### OS and Clay endpoints (same source, NOT promotional bookkeeping)

Even if UV.P01–03 establish actual conditional q at fixed physical `ell`, the inference `m >= -log(q)/ell` requires a **separate selected physical** local-support-to-OS-time bound, positive transfer semigroup, dense relevant local vectors, continuum limit, original same-`H` and no inaccessible sectors; these are in existing `BalabanCMP116PublishedLiteralToGapRound479Exact`, `BalabanClayT5ClusteringToTransferGapExact`, and `YangMillsDirectSourceOSSameHGapExact`. Nontrivial axiomatic 4D continuum for every compact simple G remains unproved. Do not claim Clay completion.

**Verification in this tool environment:** no `agda`/Nix binary; no green associated PR-triggered workflow receipt. Python exact-reference and source/GitHub readback only. The deadline for `VERIFIED_AGDA` status is an actual pinned Agda return code, no metas and audited transitive authorities, not a GitHub PR link.

---

## 6 November 2026 — priority physical-cube max-cut, stronger than bare-link Dobrushin

**New rigorous quantitative strategy / source implementation:** [YMClayPhysicalCubeDobrushinCMP116Transport20261106.md](../physics/YMClayPhysicalCubeDobrushinCMP116Transport20261106.md). It audits the actual original Dobrushin, CMP116, Wilson/Haar/Gibbs, Perron/Doob, physical RG/UV and OS owners, and retains distinct 2D/3D/4D/5D semantics. The 2D/3D/5D donor does NOT independently prove 4D.

**Source-written:** `DASHI/Physics/YangMills/YMClayPhysicalCubeDobrushinFromGibbsExact.agda` reuses original `BalabanFiniteBoundaryConditionedDobrushinExact` and `BalabanP33RationalQuaternionNormSquaredExact`; explicit `physicalCubeCellLength (cubeSideInCells a) (latticeSpacing a) ≡ physicalCubeSide`, one `0≤q<1` across all UV cutoffs/volumes, same original normalized Gibbs conditional fibre, `originalConditionalRowsUniformlyContract`, `originalConditionalObservableUniformlyContract`. **These are SOURCE/CONDITIONAL, Agda kernel pending**; actual uniform influence estimates remain to be produced. No bare `Set` field for physical cube calibration.

**Reference:** `scripts/check_ym_physical_cube_perron_certificate.py` implements exact rational weighted Perron `Cw≤q w`, positivity, exact fixed-physical-cube calibration, 12+ power checks and negative controls. It **refuses physical proof admission even if metadata is supplied**, because authentic physical source claims cannot be verified by strings. Independently checked the 4×4 illustrative matrix with exact fractions through 101 powers, max weighted row `5/12`, `q=1/2`, 5 refinements; not evidence of any actual Wilson measure.

| Physical-cube ID | Exact missing theorem/source producer | Definition of done |
|---|---|---|
| PCUBE.P01 | Construct selected `B_{a,ell *}μ_{a,L}^{Wilson}` conditional kernels from original continuous Haar/Gibbs and exact R445 same-object maps | Kernel proof and Borel conditional integration with same action/decoder |
| PCUBE.P02 | Fixed `ell` across physical lattice spacings `a→0`, `b(a)a=ell` or certified ceil interval | Original lattice geometry/units, not fixed block in lattice units |
| PCUBE.P03 | Selected all-scale physical reflection-halfspace compatibility for actual blocking | Reflective transfer and OS-positive-time sigma-algebra mapping |
| PCUBE.P04 | Actual cutoff/volume independent weighted influence `C^{a,L}w≤q w`, `0≤q<1` | **Core new nonperturbative estimate**, actual SU(N) conditionals; either direct relative, averaged Dobrushin–Shlosman, or CMP116 rooted-polymer route |
| PCUBE.P05 | Selected direct R467 `literalSelectedCMP116Localization` and envelope `≤ C_F q^{t/ell}` on actual source/continuum family | One original same-J witness and common physical source norm, no unproved field |
| PCUBE.P06 | Same limiting OS H, strong semigroup and dense local modes, gap `m≥-log(q)/ell` | Physical units, no spectral pollution or invisible subgap states |
| PCUBE.P07 | Nontrivial continuum and all prescribed compact simple groups | Actual physical OS/Wightman theory and full Clay interpretation |
| PCUBE.F01–F03 | `physicalCubeCellLength`, `originalConditionalRowsUniformlyContract`, `originalConditionalObservableUniformlyContract` | Source written; require Agda exact-head/typecheck and actual PCUBE.P01/P04 inputs |
| PCUBE.F04 | Weighted Perron checker | Python exact rational algebra and negative controls only, no physical promotion |

**Max-cut order:** prefer original CMP116 rooted-shell estimate if source-native, otherwise selected **weighted** physical-block Dobrushin matrix, rather than bare-link `18 tanh(12 beta)`. If pointwise raw-weight influence fails, the weaker averaged block criterion remains admissible. This does **not** duplicate existing published 4D CMP122 RG theorem. Any strict `q` at fixed physical `ell` gives `m=-log(q)/ell>0` for the same OS Hamiltonian IF all selected physical continuum/OS/spectral premises are actually proved. `q<1` for fixed LATTICE step with changing `a` is not the same theorem.

---


### Phase-1 constructive decision procedure — 6 November

**New original source:** `YMClayNativeOriginalSortDeciderExact.agda` adds `decideNativeMember`, `decideAllSelectable`, `isYes`, `proofFromYes`, `originalC3SelectableBooleanGoal`, `originalC3CanonicalFromBoolean`, `originalPairSelectableBooleanGoal`, and `originalPairCanonicalFromBoolean`. A successful *closed* computed Boolean membership trace now implies the existing exact native C3 or pair canonical-label equality without assuming an entire 1,024-vector equality. The two Boolean equalities and the pair-length equality **still require closed Agda proof terms and kernel acceptance**; `decideAllSelectable` is not a physical or analytic theorem. This source is imported by `DASHI/Unified/BalabanRGTOERegression.agda` and targeted by `.github/workflows/ym-native-maxcut-exact-agda.yml`, which uses the repository's existing Nix Agda shell. New workflow creation is not a green CI receipt. 

# Yang–Mills #1444 — execution phases, concrete deliverables and exact lemma acceptance queue
**Snapshot:** 6 November 2026. **Owner:** independent 4D Yang–Mills PR #1444. **Unification #1460 is NOT a prerequisite.**

## Purpose: stop repeating the six-gate inventory

This file is the **executable completion plan**. The canonical [exact lemma ledger](YMClayCurrentExactLemmaLedger20261103.md) supplies historical IDs, and [ClayYMProofRoadmap](ClayYMProofRoadmap.md) retains full historical context. Do not add another generic Wilson plaquette, Fubini theorem, trivial parametric record, or cosmetic compiler while an existing exact source theorem covers the statement. Each change MUST provide (1) selected original owner, (2) exact goal type or analytic proposition, (3) produced term/bound, (4) kernel or independent receipt, (5) transitive assumptions, and (6) status change if any.

**Immutable facts:** 219 original submission field *names* are all bare `Set` types, not 219 proved statements. The Round78 five-input compiler and its 15 carriers, 34 predicates and 13 fields are conditional on physical interpretation. Neither a machine-declared `ClayYangMillsSolution` with trivial vocabulary nor a finite-grid spectrum is an external Clay proof. Do not backfill statuses from search hints.

## Phase 0 — exact-head proof harness (TRUST.K01–K03)

| ID | Deliverable | Acceptance | Status |
|---|---|---|---|
| V00 | Pin Git SHA, Agda/compiler/stdlib and `DASHI/Unified/BalabanRGTOERegression.agda` root | Repeatable exact-head clean typecheck, no open metas, no fake `--safe` claims | OPEN: this run has GitHub readback and Python, but no local Agda binary or checkout |
| V01 | Trust/axiom DAG | Report every imported `postulate` including `RealAnalysisAxioms`, any unsafe flags and exact mathematical external authorities | OPEN |
| V02 | Regress original physical owners | Run native six-plane, signed-Wilson, finite Fubini, selected C3, blocking, full 219-field drift audit; record exact receipts | REFERENCE / kernel OPEN |

## Phase 1 — three finite exact equalities (R443.F07; R445.F16/F21)

| ID | Exact source-native term | Reused owner | Next proof step | State |
|---|---|---|---|---|
| F1.0 | `originalSortToTargetCorrect` with explicit valid-target/permutation membership | `YMClayNativeC3AdjacentSortProgramExact.originalSortToTarget`, `YMClayFiniteProductHaarPermutationExact.permuteLinks` | Prove bubble-head lemma, residual-subset/permutation invariant, induct on vector length; **not** quadratic closed reduction | OPEN |
| F1.1 | `constructedNativeC3CanonicalLabelGoal` | `YMClayNativeC3SingleVectorPermutationCertificateExact`, original C3 bond inverse | Instantiate F1.0 with original canonical label bijection | OPEN; 1024 labels / 46,592 swaps pass independent exact reference |
| F1.2 | `originalPairSpectatorLengthGoal` | `YMClayNativeSideFourPairDistinctCertificateExact` original 64 coarse, 128 distinct fine and 896 complement | Prove disjoint partition/length on original enumerated bonds, not arbitrary 1024 distinct placeholders | OPEN; exact reference passes |
| F1.3 | `originalPairSpectatorCanonicalLabelGoal` | `YMClayNativeSideFourPairSpectatorSortProgramExact` | Instantiate F1.0 from original partition; preserve pair orientation | OPEN; 41,792 swaps pass reference |
| F1.4 | All-value vector transport, original matrix links and product Haar permutation | `singleVectorC3ImpliesAllVectors`, `productHaarPermutationInvariant` | Apply only after F1.1, F1.3 and true one-link measure | CONDITIONAL existing |

**Phase-1 exit:** all three exact closed equalities typecheck against the same source head; originals retain exact canonical vector and no substitute carrier. A Python hash alone does not pass.

## Phase 2 — finite selected continuous-SU(N) Wilson/Gibbs integration (R443/R445)

| ID | Decisive producer | Already existing reusable donor | Acceptance | State |
|---|---|---|---|---|
| W2.0 | Native 6-plane spatial C3 action and density on original same SU(N) links | `YMClaySUNMatrixNativeSixPlaneC3FromInverseTraceExact` + `YMClaySUNMatrixSpatialC3RealFubiniExact` + `YMClaySUNNativeSixPlaneFullC3FromInverseTraceExact` | Original `Variable.periodicSUNGibbsDensity` decoder equality; **distinguish full CMP119 E/R/B/V terms** | SOURCE/KERNEL PENDING; CMP119 full OPEN |
| W2.1 | Actual compact complex/real SU(N) matrix group and normalized Borel Haar on explicit integrable algebra | `SUNMatrixCarrier`, `YMClaySUNVariablePeriodicProductHaarExact` | Construct measure + positivity/Fubini/translation on the original observable class; no assumption disguised as proof | OPEN |
| W2.2 | Selected actual 1024-link weighted effective-density identity | `YMClaySUNWeightedHaarPairFibreDisintegrationExact`, `YMClaySUNWeightedDisjointPairFibreReparamExact`, `YMClayNativeSideFourTwoLinkPairSameObjectExact` | Prove original `Codec.decodeOriginalBonds 4` link permutation, spectator disintegration, equality for arbitrary selected coarse cylinder F **on the original fine `e^{-S}`** | CONDITIONAL on F1/W2.1 |
| W2.3 | Coarse action honesty | `YMClayFiniteRGPushforwardNonBareWitnessSafeExact` | Distinguish `S_eff=-log ρ_eff` from pure bare Wilson; prove counterterm identity if needed, never assume it | OPEN physical |

**Phase-2 exit:** physically instantiated continuous compact SU(N) Haar and exactly same original finite Wilson source, normalized physical Gibbs pushforward and source-native action, with any remaining CMP119 terms named separately.

## Phase 3 — analytically uniform R445/R320 producers

| ID | Exact mathematical target | What a receipt must show | Status |
|---|---|---|---|
| A3.0 | Same physical selected `a_n, L_n, β(a_n)`, all-scale blocked gauge/reflection mapping | Original Wilson–Gibbs `μ_{a,L}`, compatible reflection/time slices and selected RG map; no fixed side-4 masquerading as continuum | OPEN |
| A3.1 | Uniform physical moments / tightness and continuum/thermodynamic subsequential extraction | Constants, units, original insertion/test class, dependence on `a,L`, existence and local nontriviality | OPEN |
| A3.2 | Genuine mixed-J differentiated `log Z_{a,L}(J)` on original CMP116 marked observables | Common source domain, differentiation and exact covariance identity; bounded plaquette result alone handles only restricted marks | OPEN full; finite bounded-mark mathematical sublemma documented separately |
| A3.3 | Uniform rooted-shell exponential decay `|D_FD_G log Z_{a,L}(0)| ≤ C_{F,G}e^{-m d_phys(F,G)}` | Physically appropriate positive `m`, uniform `C`, no hidden cutoff/volume dependence, same original source | OPEN — core analytic discovery |
| A3.4 | Continuum marked-correlator transport | Same state, same limit, O(4)/Euclidean time, reflection-compatible transfer to reconstructed OS test class | OPEN |

**Phase-3 exit:** proofs of original physical uniform estimates and selected limits, not just finite covariance identities or numerical fits.

## Phase 4 — R333 same-Hamiltonian physical spectral gap

| ID | Exact target | Acceptance | Status |
|---|---|---|---|
| S4.0 | Original Wilson-Gibbs reflection positivity and preservation through actual R445 blocking/limit | Nonnegative full reflected Gram matrices for original observable class; positive scalar density alone insufficient | OPEN |
| S4.1 | Physical OS null quotient, Hilbert completion, strong semigroup and `H_OS` | Same selected limiting physical measure, domains and physical time units | OPEN |
| S4.2 | Wilson transfer / spectral operator identification | Same operator for correlators, transfer matrix, OS semigroup; no independent fake gap carrier | OPEN |
| S4.3 | `H_OS|_{Ω^⊥} ≥ Δ I` with `Δ>0` | Strict physical-unit, volume/cutoff-uniform gap, full relevant Hilbert subspace, exclusion of undetected sectors | OPEN |
| S4.4 | Limit survival and nontrivial excitation | Both limits + vacuum uniqueness + local non-Gaussian or other nontrivial witness | OPEN |

## Phase 5 — external Clay scope and semantics

| ID | Target | Condition | Status |
|---|---|---|---|
| C5.0 | 219 original-field proof-relevance crosswalk | For each used field, selected physical type + theorem witness + same-object/trust graph; explicit redundancy for omitted fields | OPEN |
| C5.1 | 15 carriers, 34 predicates, 8/9/11 Clay requirement meaning | Real `R⁴`, accepted OS/Wightman QFT, O(4)/Poincaré, gauge-invariant local fields, positivity and nontriviality; prevent trivial-model endpoint | OPEN |
| C5.2 | `LiteralClayStructuralBase`, `UVToContinuumYM`, `SameHamiltonianPhysicalMassGap`, `SameFamilyLocalFieldsOPEStressWard`, `StandardSameHGaussianNontrivialityConsequence` | Physically selected witnesses fed to existing T78 compiler; not just record parameter fields | OPEN |
| C5.3 | Prescribed compact simple group scope and independently checked Clay statement | Actual all-G transport or independent per-G construction, not SU(N)-only or empty domain | OPEN |

## Mandatory receipt per change

`{head_sha, producer_id, original_owner, exact_goal, output_path, proof_status, python_reference, agda_command, agda_exit, transitive_postulates, physical_same_object, negative_controls, remaining_leaf}`

**Status taxonomy:** `VERIFIED_AGDA` only with pinned compiler/kernel receipt; `VERIFIED_REFERENCE` only for exact finite executable check; `SOURCE_PENDING` for new Agda terms without typecheck; `CONDITIONAL` for proved implication lacking a physical hypothesis; `OPEN_MATH` for unsolved analytic producer. Never translate `SOURCE_PENDING` into `VERIFIED_AGDA`.

**Immediate work order:** F1.0 generic sorter invariant → F1.1/F1.2/F1.3; in parallel W2.0 actual action/decoder and W2.1 continuous analytic Haar. Then W2.2, A3.0–A3.4, S4.0–S4.4, C5.0–C5.3. The finite cut does *not* establish or shortcut the analytic mass-gap problem.
