## 2026-11-06 follow-on: finite original Wilson two-source jet (Y.01/Y.02)

**Golden source:** `DASHI/Physics/YangMills/YMClayOriginalWilsonFiniteTwoSourceJetExact.agda`, in parent [PR #1444](https://github.com/chboishabba/dashi_agda/pull/1444). **Independent exact reference:** `scripts/check_ym_original_wilson_two_source_jet_reference.py`. Canonical TOE import and targeted Agda CI now name the file. No Agda kernel or transitive trust receipt has been observed.

| Exact ID | Source term | Status and remaining physical payment |
| --- | --- | --- |
| `Y.FIN.01` | `originalWilsonDensityIsSelectedWilson`, `originalWilsonPartitionIsSelectedProductHaar` | Source-written: literal changing-cutoff SU(N) Wilson/Gibbs density and partition are anchored to the *same* previously constructed finite product-Haar measure; one-link compact Borel Haar realization is still an explicit input. |
| `Y.FIN.02` | `originalWilsonMomentAlgebra`, `originalWilsonNormalizedJet`, `originalWilsonLiteralJetDirections` | Source-written: define the formal two-source coefficients directly from one original finite Wilson normalized expectation; no independent moment/covariance object. The *analytic derivative* of the actual continuous-Haar source functional is not inferred. |
| `Y.FIN.03` | `originalWilsonMixedJetIsSameFiniteCovariance`, `originalWilsonMixedJetIsOriginalConnectedCumulant` | Source-written: literal finite formal mixed-log jet equals the same Wilson connected covariance by the original cumulant compiler. Kernel acceptance pending. |
| `Y.FIN.04` | `check_ym_original_wilson_two_source_jet_reference.py` | Exact rational BIDI reference: 19,683 exhaustive three-state cases and six simultaneous relabelings; changed-measure negative control rejected. This is not an SU(N) Haar integration or Agda check. |

**Revised original physical max-cut (do not promote from Y.FIN):** `Y.01` identify the entire real Wilson/gauge-fixed E/R/B/V/ghost/counterterm source with the selected CMP119/122 density/physical T-operation at every renormalization scale, not just the original finite Wilson action. `Y.02` prove that selected positive-time gauge-invariant local/loop insertions are admissible CMP119/116 analytic J directions, identify the genuine differentiated `log Z` with this formal jet, and preserve root/distance/normalization. `Y.03` derive *actual* cutoff/volume-uniform source decay, RG/continuum tails and reflection-compatible limits. `Y.04` construct the same limiting OS Hilbert/Hamiltonian and quantitative nontriviality/Clay scope. Reuse the CMP119/122/116, R344/R467/R482, Bishop/T5 and original Wilson–Gibbs owners rather than copying them.

**Acceptance:** new formal theorem = `SOURCE_PENDING_AGDA`; reference arithmetic = `VERIFIED_REFERENCE`; original CMP116 source applicability and physical estimates = `OPEN_PHYSICAL`. CI is a checker command, not a green receipt. Parallel-checker exact-head execution and transitive axiom audit remain required.

---


## 6 November — canonical R344 shared marked CMP116 half-rate direct weld

The *existing* `BalabanCMP116SharedMarkedDirectCalibrationRound344Exact` proves the shared-Hessian shell's conditional geometric $\frac14 C_H 2^{-d}$ bound, with selected physical source distance/time and (C_H≤1) as proof inputs. Two new terms `sameOriginalSharedMarkedHalfRateFiniteDecay`, `sameOriginalSharedMarkedHalfRateYieldsGap` (R344→R342→R467→R482) are source-written in `YMClayCMP119122116SelectedProducerWeldExact.agda`, Agda unverified. The actual original Wilson-Haar marked J applicability, uniform physical rate and OS limit are not derived from a name match. Exact four-cut Y.01–Y.04 is in `Docs/physics/YMClayCMP119116122OriginalSameSourceMaxCut20261106.md`. Source contract audit now 12 donor owners / 6 bridge proof terms.


---

## 6 Nov 2026 — CMP119/116/122 source archaeology upgraded to exact reuse

**Do not regenerate Bałaban's mathematics.** Existing repo already owns CMP119 beta-driven full density + anchored *normalized* expectation, CMP122 complete-density UV/boundary reinjection, CMP116 finite differentiated/selected two-J localization, and R342→R467→R479/R482 positive transfer-gap compilers. New `YMClayCMP119122116SelectedProducerWeldExact.agda` imports and composes these on one source: beta coupling + localized CMP116 potential, R342→R467 finite same-selected covariance, and R342→R482 positive-gap rate without independent positivity token. No Agda compiler receipt or physical Wilson instantiation claimed. Source-owned statements are distinguished from original SU(N) Wilson, gauge/ghost physical density, original marked-J dictionary, source uniform physical rate and reflection-positive *crossing* R-operation.

Four actual same-Wilson physical payments **Y.01–Y.04** are specified in [CMP119/116/122 source max-cut](../physics/YMClayCMP119116122OriginalSameSourceMaxCut20261106.md) and [current phases](YMClayExecutionPhasesDeliverablesExactLemmas20261106.md). New fail-closed source/CI contract: `scripts/check_ym_cmp119116122_same_source_contract.py`. The optional physical Dobrushin/Perron route is not a compulsory additional CMP116 source leaf.

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

## 2026-11-06 — YM proof-source / RG budget supplement

See [phase-specific exact update](YMClayExecutionPhasesDeliverablesExactLemmas20261106.md). F1 three original 1024-link equality proof attempts source-written, **no Agda receipt**. New original physical-cube RG arithmetic derives q=q0+B, with 128-step exact rational reference but actual continuous SU(N)/CMP116/OS physical coefficients and compact-group coverage OPEN. Files: `YMClayNativeClosedThreeEqualitiesCandidateExact.agda`, `YMClayPhysicalRGDriftToUniformInfluenceExact.agda`, `YMClayRGDriftOriginalGibbsInstantiationExact.agda` and `scripts/check_ym_rg_drift_budget_reference.py`. #1460 remains separate physical observer/KK lane; no child import. Full source contracts in `Docs/physics/YMClayPhysicalCubeDobrushinCMP116Transport20261106.md`.

---


---

## 6 November 2026 — physical-cube CMP116/Dobrushin/Perron steelman, not generic bare-link repetition

**Primary new implementation and physical theorem spec:** [Docs/physics/YMClayPhysicalCubeDobrushinCMP116Transport20261106.md](../physics/YMClayPhysicalCubeDobrushinCMP116Transport20261106.md), wired into [phases/deliverables](YMClayExecutionPhasesDeliverablesExactLemmas20261106.md). The prior finite 1024-label C3/pair selection proofs remain open for kernel acceptance; this physical lane runs in parallel. Key genuine theorem is `PCUBE.P04`: find one (0≤q<1), independent of a,L, for weighted conditional Dobrushin matrix of the SAME original blocked compact SU(N) Wilson Gibbs state at fixed physical `ell`; source-native CMP116 marked-J / rooted-polymer is the competing route, and R467 source specialization already exists. Existing direct R479/T5 same-H spectral compiler should be reused. `YMClayPhysicalCubeDobrushinFromGibbsExact.agda` formalizes the exact conditional row/observable transport; no new coarse probability law is declared. No proof of the strict actual physical `q` or continuum mass gap is claimed.

---

# 6 November 2026 — canonical active execution queue (replaces repeated six-gate summary)

**ACTIVE PHASES, DELIVERABLES, ACCEPTANCE AND EXACT LEMMAS:** [YMClayExecutionPhasesDeliverablesExactLemmas20261106.md](YMClayExecutionPhasesDeliverablesExactLemmas20261106.md). This file's historical milestones remain preserved below. Do not mistake original source-written owners for kernel acceptance or proof of the full mass gap.

**P0 actual execution:** new `YMClayNativeOriginalSortMembershipCorrectExact.agda` contains source-written (1) membership-indexed `bubbleDesiredHeadWhenMember`, (2) inductive `AllSelectable` and (3) `originalSortToTargetCorrect`, on the actual original sorter. The next unproved original-target producers are C3 selectability and pair/spectator selectability+length. Exact native Python reference has passed 5,914 exhaustive distinct small permutations, all 1,024 original C3 and blocking steps, 46,592/41,792 swaps, both negative invalid-target controls; **not Agda**. `scripts/check_ym_sort_selectability_reference.py` recorded. Agda not installed in current local runtime; this source is **UNTYPECHECKED**.

**P1 finite source:** reuse original positive/signed Wilson plaquette, finite real Fubini, weighted Haar fibre laws F17–F22. Native SU(N) 6-plane C3 source composition exists. Still need original `Variable.periodicSUNGibbsDensity` same-decoder equation and separate selected CMP119 E/R/B/V action; true compact measurable Haar remains open.

**P2 physical:** R445 physical scaling, reflection compatibility, uniform estimates/continuum, R320 actual CMP116 differentiated mixed-J rooted-shell decay, R333 selected RP/OS same H positive gap, and external Clay all-compact-simple-group solution are **OPEN MATHEMATICS**. Original 219 field names remain bare Set, not 219 proved witnesses. No six-gate status was falsely decremented.

---

## 2026-11-05 — R443 original weighted Wilson–Gibbs spatial C3 and SEM.P02 nonvacuous group scope

- **R443.F09 SOURCE / KERNEL PENDING:** `YMClayOriginalWilsonC3WeightedHaarTransferExact.agda` defines the density with the **same original** `Variable.periodicSUNGibbsDensity`, the canonical 1024-positive-bond decoder and the original one-link product Haar. Its conditional source theorem derives **weighted** spatial C3 numerator and normalized expectation invariance from the ONE closed native C3 label equality **and** literal physical action density C3 covariance. It additionally constructs selected `Constructed.actualPeriodicProductMeasure` and proves the actual original physical cylinder numerator is the original 1024-vector numerator, and physical partition/normalized expectation are the same (source-written, using original `mulOneʳ` and `Congruence.productIntegralCongruent`). Thus no second Gibbs/partition is introduced. **Still OPEN:** kernel-accept the original C3 equality, prove the selected physical CMP119 E/R/B/V action C3 equality, genuine continuous SU(N) Borel Haar on the correct integrable tests, real scalar/trace instantiation, uniform RG/CMP116/OS/Clay.
- **SEM.P02 SOURCE / KERNEL PENDING:** `YMClayCompactSimpleScopeBidiNoVacuitySafeExact.agda` supplies a standalone `--safe` mathematical firewall: the selected internal group universe cannot be empty/one arbitrarily chosen group and claim all externally specified compact simple G. It requires a physical external group witness, bidirectional index map, exact group/equivalence and actual physical predicate meaning for both all-group implication directions. **Actual compact-simple classification/physical all-G transport OPEN.**
- **Independent local exact noncommutative reference executed:** original (4^4\) torus/1024 positive links with Q8 subgroup of SU(2); 32 original Wilson action C3 invariances, 32 independent local gauge invariances, 32 C3-cubed, 32 exact C3-symmetric weighted-orbit numerator equalities PASS. All 32 deliberately anisotropic-weighted C3 symmetry assertions FAIL, furnishing the correct negative control. `scripts/check_ym_original_c3_weighted_wilson_q8.py`. This does **NOT** verify full selected CMP119 E/R/B/V, continuous Haar or Agda.
- **Agda source audit correction:** original §proof-relevant Set-anchoring§ record's universe changed to `Set₁`, because equality between `Set`-valued propositions lives in `Set₁`; source-written and GitHub readback, **exact-head typecheck still pending**.
- Ledger currently **67 producer entries** (prior 66 + R443.F09). Original 219 named `Set` fields and 521 hint edges are unchanged, **0 individual physically interpreted field proofs promoted**. `Docs/roadmaps/YMClaySteelmanBidirectionalExactRemainingMaxCut20261104.md` carries full steelman/bidi. No writes to #1460 or ESD.

## 2026-11-04 — exact Yang–Mills 219-field / Clay-vocabulary semantic firewall and steelman-bidi

**Source/connector audit PASS (not Agda):** original 219/219 field declarations literally have type `Set`, i.e. a chosen proposition rather than proof of that proposition. Original owner blobs are pinned and unchanged; all 219 individual physical proof statuses remain `NOT_AUDITED`. The new bidirectional audit index `Docs/roadmaps/YMClay219ProofRelevantBidirectionalAudit20261104.json` contains **521 invertible candidate-gate hints** (R443 68, R445 188, R320 104, R333 105, CLAY 56), **66 unique producer rows** (original 63 plus SEM.P01–P03), no fabricated lemma witness.

**New Agda source:** `YMClayProofRelevantFieldAnchoringSafeExact` proves the general no-promotion/anchoring transport for a physically fixed selected predicate; `YMClayOriginalCMP109NamedSetNoPromotionExact` demonstrates the actual original five CMP109 names can choose uninhabited types without providing physical proofs; `YMClayParametricVocabularyNoClayPromotionExact` constructs a deliberately trivially satisfiable parametric `ClayYangMillsSolution` record, illustrating why the **15 selected carriers / 34 semantic predicates / 13 data fields** must be externally physically anchored. This is a negative semantic countermodel, absolutely NOT an actual Clay or YM theorem. New source has no local holes/postulates; exact-head Agda/kernel and transitive trust remain PENDING.

**Exact remaining / steelman / bidi:** `Docs/roadmaps/YMClaySteelmanBidirectionalExactRemainingMaxCut20261104.md` gives 39 prioritized mathematical producer statements spanning the original 1024 C3/bond proofs, physical compact SU(N) measurable Haar, exact 1024 Wilson-weighted effective-density same-object weld, reflection-compatible all-scale RG, CMP116 uniform differentiated J-rooted-shell control, same OS reconstructed physical H and gap, all compact-simple group scope, and external Clay physical semantics. Six independent exact finite negative controls passed (positive weight not RP; finite gap not uniform; selected observable decay not full spectral gap; constants not measure equality; C3 Haar not weighted action invariance; one gauge group not all groups). Preferred T78 five-input compiler is conditional sufficiency only, **NOT an iff** or official external proof.

**Next physical work remains open:** one closed R443 C3 vector equality + two closed R445 pair/spectator equations, exact typechecking, true measurable Borel SU(N) Haar and selected integrands, full original Gibbs source/effective density equality, uniform UV/IR RG and CMP116 source estimates, RP/OS/same-H positive gap and nontrivial all-group 4D QFT. None is discharged by this audit.

## 2026-11-04 — R443.F08 and R445.F17–F22 weighted effective-density/native permutation max-cut

**Actual work on #1444 only; #1460 unification untouched.** [New original YM weighted effective-density dossier](../physics/YMClayOriginalNativeWeightedEffectiveDensityMaxCut20261104.md).

- `YMClaySUNWeightedHaarPairFibreDisintegrationExact` F17: source-written **actual original SU(N) group operation** plus original one-link right Haar, Fubini, linearity prove the **weighted** noncommutative pair equality `∫dUdV w(U,V)F(UV)=∫dW [∫dV w(WV^-1,V)]F(W)`, the SAME fine/coarse partition and normalized pairing, plus conditional strict coarse density positivity. Arbitrarily coupled fine weights, no bare Wilson promotion.
- `YMClaySUNWeightedDisjointPairFibreReparamExact` F18–F19/F22: finite induction constructs the original all-pairs `Uj,Vj ↔ Wj,Vj` weighted measure reparam, Fubini groups all coarse variables before **all** fibre variables, and an **explicit all-pairs** derived effective coarse density / weighted pushforward numerator. Full arbitrary spectator dependence is retained, with selected original numerical arities **64 pair-links + 896 spectator links**. Strict positive original one-link integration plus positive weight prove pointwise derived effective density and coarse partition strictly positive; no new coarse positivity axiom.
- `YMClayFiniteNativeAdjacentWordInverseExact` F20: original typed adjacent swap, ordered original `LinkPermutation` word compiler and **two-sided inverse**, source-written on arbitrary original link vectors.
- `YMClayNativeC3AdjacentSortProgramExact` R443.F08: construct the actual original 1024-link C3 target **program** from original bond labels; **one CLOSED canonical-label equality remains kernel-open**, not filled by fake `refl`. The original F06 theorem transports a future certificate to all SU(N) links.
- `YMClayNativeSideFourPairSpectatorSortProgramExact` F21: original F15/F16-selected 128 fine-link labels plus the full 896 original spectator complement; reuse the same original bubble-sort `LinkPermutation 1024` generator, with precisely TWO finite closed Agda goals (length and equality). Their acceptance would enable original 1024-link product Haar reindex into the derived F19 effective density *when physical one-link Haar is established*.

**Executed exact independent tests:** 1800 weighted pair + 1800 spectator-coupled cases + non-bare control; 117 all-pair reparam cases / 1,184,769 original fine rows; 81 all-pair derived density/partition cases; original 46,592 C3 swaps, original 41,792 side-four pair/spectator swaps, original inverse/C3³/digest/negative controls. All PASS in local Python reference. **Not Agda kernel acceptance;** one F17 parenthesis syntax issue was discovered and repaired via static audit. New files have no local postulate or hole; inherited `RealAnalysisAxioms` axioms and selected physical continuous compact Borel Haar remain OPEN.

**Physical maximum cut remains:** accepted original C3/side-four native closed equalities and correct 1024 decoder with real SU(N) Borel Haar → selected actual **weighted Wilson–Gibbs** effective coarse density/disintegration → reflection-compatible all-scale changing-cutoff RG and uniform analytic estimates → same-source differentiated mixed-J CMP116 rooted-shell decay → physically reconstructed same-H OS strict gap/ H6/Clay. Nothing in the present finite F17–F22/ F08 source upgrades Clay or resolves R320/R333. Canonical ledger now R443.F01–F08 and R445.F01–F22, 63 producer rows; original 219 field inventory individually unaudited.

### 2026-11-04 — F15/F16 actual original selected side4→side2 pair and canonical reindex frontier

`YMClayNativeSideFourTwoLinkPairSameObjectExact` proves the **actual original** `Block.nativeBlockedPositiveLinks {m=1} {l=1}` is the literal right-associated 2-link ordered product of original fine-bond values at the original fine-block origin and its positive successor. Only the original `Bond.identityRight` is used to remove the empty-path identity. Specializations select the **identical original SU(N)** `SUNBlock.nativeSUNBlockLinks` and the **actual selected weighted Gibbs** `Push.actualBlockedLinkMap`. This removes a specific pointwise same-object bridge, not the global original 1024-coordinate reindex.

`YMClayNativeSideFourPairDistinctCertificateExact` reuses original `Codec.originalPositiveBondFinite` for 64 selected coarse bonds and 1024 fine bonds plus original `Torus.productDecidableEquality`; a concrete 128 selected fine-label duplicate-decision and `refl` closed count/distinctness goals are SOURCE-WRITTEN but **Agda kernel evaluation pending**. Independent `scripts/check_ym_native_1024_pair_spectator_reindex.py` executed: 1024 native labels → 128 pair-selected +896 spectators, inverse, exact `41,792` adjacent swaps, digest `49b954c21ccd1649208074eb5096e5b6b63102313da773fe17e1268b67727ada` and wrong-order/duplicate controls PASS. The **next exact finite gate** is the typed original `Product.LinkPermutation 1024` and canonical label-vector proof; no finite counting reference can replace kernel acceptance. F13 unweighted Haar now covers arbitrary ordered length L and disjoint L blocks, but not continuous Haar existence, weighted effective Gibbs action/conditional disintegration, uniform CMP116 estimates or same OS strict gap. Full 219 Clay fields not audited; F01–F16 are producer rows, not a proof of Clay. Another worker owns TSVF/KK #1460.

## 2026-11-04 — R445.F13/F14 original Haar pair & actual blocked covariance (source-written)

**New same-source finite reduction:** [YM R443/R445/R320 Haar-blocked same-object dossier](../physics/YMClayOriginalHaarPairsToR445R320SameSourceMaxCut20261104.md). `YMClaySUNHaarDisjointPairBlockingExact` derives `∫dU dV F(U·V) = ∫dW F(W)` for noncommutative original SU(N) links using existing `Bilateral.oneLeftInvariant`, original one-link Haar normalization, scale and integral congruence; extends to all disjoint ordered pair-vectors plus any number of independent spectator links, no new Haar axiom. Native selected original 4D geometry reference: 1024 fine positive bonds, 64 coarse bonds, 128 distinct paired bonds, 896 spectators. Independent exact Q8 tests: 64 single-block functions, 14 arbitrary nonfactorized n≤3 disjoint-vector functions, plus all native periodic selected bonds and endpoints passed. **Source-level only; Agda kernel pending.** To apply to the full original side-four source still requires kernel-accepted exact 1024-label pair/spectator permutation, and true measurable compact SU(N) one-link Haar.

`YMClaySUNR445BlockedPushforwardR320CovarianceExact` reuses the **actual** original side-four SUN Wilson-Gibbs normalized measure and `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact.actualBlockedLinkMap` to prove definitional covariance agreement for arbitrary coarse F,G. No new coarse bare Wilson density, auxiliary measure or arbitrary covariance is postulated. Weighted Wilson interactions COUPLE spectators, so the unweighted Haar discard theorem does **not** establish effective-action density or conditional disintegration. Changing-cutoff/volume CMP116 mixed-J log partition differentiation and rooted-shell uniform decay, physical OS reflection positivity, strict R333 continuum gap and H6 nontriviality remain OPEN. No cross-writes to the separately owned TSVF/KK #1460 lane. Retains original Bałaban/Wilson source ownership. Golden claims remain blocked by transitive `RealAnalysisAxioms` and absent Agda compiler receipt.

## 2026-11-04 — R445.F12 exact existing finite pushforward/pullback/reopening weld

**Same theorem owners, no duplicate probability theory.** `DASHI/Physics/YangMills/YMClayFiniteRGExistingPushPullReopeningWeldExact.agda` applies `DASHI.Core.SectionedProjectionProvenanceBridgeExact.pullbackObservable` to the *same* projection of `BalabanFiniteProbabilityPartitionDisintegrationExact.FiniteCoarsePartition`, takes its real constructor `compileFiniteRGReopeningStep`, and uses the existing `BalabanFiniteRGObservableReopeningExact` finite expectation transport.

The source-written new proof terms are `originalKernelPullbackPointwise` (actual matches/project fibre support), `originalReopeningOfPullbackIsCoarse` (`T(f o project) = f`), `originalReopeningFibreConstant` (explicit fine-observable factorization through coarse), `originalFinitePushforwardPullbackPairing` and `originalFiniteFibreConstantExpectation` (`E_fine[f o project] = E_coarse[f]`). These are reductions on one original rational coarse-fibre partition, not a second pushforward or conditional kernel.

**Independent finite reference only:** `scripts/check_ym_existing_pushpull_reopening.py` executed on 2,400 deterministic exact-rational partitions; 22,862 fine states and 12,911 coarse fibres, all support/normalization/disintegration/pullback/expectation tests passed. Agda kernel NOT RUN, no `--safe` transitively accepted claim.

**Fail-closed physical boundary:** the selected original physical SU(N) side-four → side-two Gibbs pushforward remains in `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact`, with its own continuous matrix-link configurations, one-link measurable Haar inputs and original Wilson density. Its identification with an actual measurable conditional distribution, effective coarse Radon–Nikodym density/action and the rational finite `FiniteCoarsePartition` carrier is NOT established. Generic finite identities do not close R445.P04/P06/P07, physical OS reflection compatibility, CMP116 R320 mixed-J decay, R333 positive continuum mass gap, H6 nontriviality or Clay. R443 actual Haar and C3 witness remain. F12 is SOURCE/KERNEL PENDING and canonical producer-level ledger advances to 52 entries, with all 219 original submission fields unaudited.

## 2026-11-04 — R445.F10/F11 original all-coarse SU(N) gauge-lift on selected finite Gibbs pushforward

**Real source continuation, not a Clay promotion.** `YMClaySUNSideFourBlockedFineHaarObservableExact.agda` now source-writes the original side-four → side-two coarse-site projection and the explicit lift `liftOriginalCoarseGauge` of **any** side-two SU(N) site gauge to a side-four gauge. `selectedCoarseSiteAtBlockOrigin` uses original Bałaban M=L=2 split/unblock/site roundtrips; `blockLiftedCoarseGaugeAt` proves its restriction is the original coarse gauge. Using selected `Endpoint.sideFourSUNBlockGaugeCovariant`, it derives `selectedBlockedCoarseGaugeEquivariant` on the **actual ordered non-Abelian** link block. Via selected one-link product-Haar congruence plus the existing original fine Gibbs gauge theorem, `selectedPushforwardAllCoarseGaugeInvariant` proves that the fine pushforward expectation of any pointwise coarse observable is invariant under every coarse gauge; the original coarse Wilson action and Gibbs-density specializations are derived rather than separately assumed.

**Reference:** `scripts/check_ym_blocked_all_coarse_gauge_lift.py` exact Q8 finite test executed locally with exit 0: 3,256 identity checks for 40 deterministic noncommutative trials, and 40/40 deliberately wrong target-inverse controls rejected. This checks finite conventions only; the source-written new Agda theorems were NOT typechecked, and imported `RealAnalysisAxioms` postulates have NOT been cleared.

**All-scale reuse:** `YMClayNativeAllScaleBlockedCoarseGaugeLiftExact.agda` proves every original M×L Bałaban coarse site gauge lifts to the original fine site carrier and restricts exactly on block origins. The actual non-Abelian blocked-link coarse gauge theorem is derived **conditionally** from the unchanged all-scale `BlockEndpointCompatibility` arithmetic hypothesis; it remains OPEN. `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact` now exports selected `actualPushforwardAllCoarseGaugeInvariant` for the original weighted/normalized coarse-cylinder functional. Existing independent F08/F09 finite-functional and finite non-bare-Wilson theorem owners are retained; identifiers reconciled to F10/F11 for this contribution.

**Critical effective-action boundary:** the selected blocked expectation remains `E_fine[F(B(U))]`. Its gauge invariance does NOT prove the pushforward has a bare Wilson Gibbs density with respect to coarse Haar, or yield its full effective action, normalized conditional disintegration, preservation of OS reflection positivity under this block, running beta/spacing, uniform UV/IR estimates, R320 mixed-J CMP116 decay, R333 strict same-OS-H gap, or the Clay solution. Existing finite rational disintegration theorem owners `BalabanFiniteProbabilityPartitionDisintegrationExact` and `BalabanFiniteRGObservableReopeningExact` are reused as algebraic precedents, not falsely promoted to continuous physical SU(N) disintegration. The 219 submission fields remain individually unaudited; new current producer ledger rows are R445.F10/F11 (51 total, including independently owned F08/F09). Keep #1440 parent, #1444 physical YM, #1460 downstream TSVF/KK without circular imports. Preserve Wilson, Bałaban, Haar/Fubini and previous DASHI proof-source attribution.

## 2026-11-03 late — YM R445 same-SU(N) blocked Wilson and finite fine-Gibbs pullback (source-written)

After checking the newest open PR heads and changed files, the parent #1444 and downstream #1460 have complementary, **not interchangeable**, R445 finite results. #1460's `YMClayNativeBlockedSU2PathHolonomyGaugeExact` constructs general blocked-offset/composable rational-SU(2) paths and actual real-trace closed-loop invariance; it is downstream. Parent #1444 now has `YMClayNativeBlockedPositiveHolonomyGaugeExact` (generic original group), `YMClaySUNNativeBlockedPositiveHolonomyExact` (original all-SU(N) carrier), `YMClayNativeSideFourTwoBlockEndpointExact` (specific side-four 2x2 endpoint) and two newly added **original physical observable** owners:

1. `YMClaySUNSideFourBlockedWilsonGaugeExact.agda` builds, on the ORIGINAL side-four fine SU(N) Wilson field, the ordered two-link coarse field at side two, the selected coarse-periodic Wilson plaquette, its real trace, the six-positive-plane deficit, beta-weighted Wilson action and Gibbs density. Source-written Agda proofs derive fine-site-gauge invariance through the **same** original coarse `Variable.periodicSUNGaugeTransform` and the previously proved `Pointwise.variablePositivePlaquettePointwise`, `variableSixWilsonDeficitPointwise`, `variableWilsonActionPointwise`, `variableGibbsDensityPointwise`, and native gauge invariance. No whole-field function extensionality.
2. `YMClaySUNSideFourBlockedFineHaarObservableExact.agda` uses exactly `Constructed.actualPeriodicProductMeasure theory ... n=3 betaFine ...`, the original source fine Wilson/Gibbs density, original one-link Haar and bilateral gauge algebra, and the **same** native SU(N) block. It proves pointwise coarse observables pull back to fine pointwise observables and derives the normalized original fine-Gibbs expectation gauge theorem for generic coarse observables, plus selected coarse Wilson action and coarse Gibbs density. This is a **conditional** finite product-Haar theorem, not constructed compact measurable SU(N) Haar.
3. These are direct R445.F06/F07 source reductions, re-exported by `DASHI.Unified.BalabanRGTOERegression` and registered in [YMClayCurrentExactLemmaLedger20261103.md](YMClayCurrentExactLemmaLedger20261103.md). The current ledger now has 47 producer-level rows. The source-extracted 219-field A–I submission inventory is unchanged and still per-field `NOT_AUDITED`.

**Fail-closed distinction:** `E_{fine,betaFine}[F(B(U))]` is the **definition of a blocked-observable pushforward functional** under map B. It does NOT assert that the pushforward of the full fine Wilson Gibbs measure equals `Z_{coarse}^{-1} exp(-betaCoarse S_W(U_{coarse})) dH(U_{coarse})`: real non-Abelian RG typically generates effective multi-link interactions/counterterms. Neither finite gauge invariance nor product-Haar symmetry supplies uniform R445 moment/tail/refinement/OS reflection estimates. No imported `RealAnalysisAxioms` postulates are cleared, Agda kernel acceptance is still pending, and the R320 mixed-J physical decay, R333 physical same-H strict gap, 4D Clay existence/nontriviality remain open.

**Next exact payments:** R443.F07 Agda adjacent-swap program and single 1024-label equality; physical SU(N) Haar on the defensible measurable/integrable Wilson test algebra and selected R124 E/R/B/V; R445 all-size modular endpoint, actual nonlinear Wilson Gibbs RG pushforward/disintegration and reflection-compatible cylinders, beta(a)/volume and uniform physical limit estimates; R320 CMP116 source-differentiated exponential rooted-shell bound; R333 same-OS-generator dimensionful gap and full Clay endpoint. Credit Wilson, Bałaban, Haar/Fubini, Osterwalder–Seiler, Menotti–Pelissetto, Osterwalder–Schrader and original DASHI code owners; preserve #1460 independent worker's rational SU2 closed-path provenance.

## 2026-11-03 late — latest YM PR/branch audit + native blocked SU(N) link max-cut

**Latest live GitHub PR heads checked:** #1440 `6e9bcb01fd95ed935ee2e40ff7326df7df575f6c` (Route-S R320/R333, parent); #1444 remains current four-dimensional physical YM owner (this branch); #1460 is an independently moving downstream Lorentz/TSVF/KK OS-clock/compatibility branch, at `afe6882036ad090b284a4bb100c821a19d74a1ac` during the initial audit (subsequent head may move). Other newest repository PRs #1461–#1464 are not claimed as R443/R445/R320/R333 physical-YM theorem owners. The existing `dashi_lean4` PR #15 (`6c106f9980d98e4a1205a3b784373ac914390c93`) provides a real SU(2) Haar **donor**, but not an Agda same-carrier/kernel-accepted Haar proof.

**New genuine R445 finite physical source owner**:
- `DASHI/Physics/YangMills/YMClayNativeBlockedPositiveHolonomyGaugeExact.agda` defines the exact positive-direction `positiveSteps` and `positiveDirections` on the **original** four-torus, constructs the ordered **group-valued** `positiveHolonomy` and `nativeBlockedPositiveLinks` from the existing Bałaban 4D block origin `YMClayNativeBlockedPeriodicBondWeldExact.unblockNativeSite`. Induction proves `positiveHolonomyGaugeCovariant` under `Bond.transformedBondBase`, original `positiveHolonomyIsSelectedPath`, and pointwise-link congruence with **no unrestricted function extensionality**. A single `BlockEndpointCompatibility` arithmetic proposition isolates the all-`M×L` coarse-endpoint equality; when given, `nativeBlockedGaugeLawOnCoarse` derives the actual coarse-source transformation.
- `DASHI/Physics/YangMills/YMClaySUNNativeBlockedPositiveHolonomyExact.agda` instantiates precisely `SUN.CertifiedSUNMatrixTheory`, `Native.sunExactSignedLinkGroup`, `Variable.SUNPeriodicLinks`, `Variable.periodicSUNGaugeTransform` and `Variable.periodicSUNRealization`; the non-Abelian block field is **not** a separate toy gauge algebra.
- `DASHI/Physics/YangMills/YMClayNativeSideFourTwoBlockEndpointExact.agda` source-writes eight actual selected side-four, block-two/coarse-two finite endpoint clauses and obtains `sideFourSUNBlockGaugeCovariant` for original 1,024 fine positive links → 64 coarse positive links. Its eight `refl` terms are **Agda-kernel unverified**. All-M,L exact endpoint, blocked Wilson plaquettes/action, Gibbs pushforward and measure cylinder, reflection-compatible half-spaces, physical spacings, CMP116 mixed-J and R333 OS gap are still open.
- `scripts/check_ym_native_blocked_positive_holonomy.py` executed an independent noncommutative Q8 reference over `(M,L)=(1,3),(2,2),(2,3),(3,2),(4,2)`; original fine path/gauge cancellation, periodic coarse endpoint and deliberately bad omitted target inverse were checked. Side-four M=L=2 checks 64 coarse edges corresponding to 1,024 original fine edges. This is **reference-only** and is not a proof of a continuum SU(N) measure or Agda code.

**Current exact-lemma ledger**: [YMClayCurrentExactLemmaLedger20261103.md](YMClayCurrentExactLemmaLedger20261103.md) adds R445.F04/F05 and updates P01/P02 to source-written finite closure with separate all-scale physical/measure leaves. This does not decrement frozen physical research families A–D or discharge the 219 full submission fields automatically. The latter inventory remains [YMClaySubmission219FieldInventory20261103.json](YMClaySubmission219FieldInventory20261103.json) with all 219 individual statuses **NOT_AUDITED**.

**Still exact P0/P1 max-cut:** R443.F07 Agda adjacent-swap program + original 1,024-label equality; physical continuous SU(N) Haar/integrable Wilson class/real matrix identification and selected CMP119 E/R/B/V; R445 all-scale block-endpoint, same-Wilson action/refinement and actual Gibbs measure disintegration/OS; uniform UV/IR estimates; R320 physical selected mixed-J differentiated rooted-shell decay; R333 the SAME OS Hamiltonian in physical units with strictly positive surviving spectral gap, complete nontriviality and the full Clay Jaffe–Witten endpoint. Do not equate a TSVF branch's physical clock with OS time translation by proclamation.

**Verification:** connected GitHub file writes/readback, source/import and concrete cross-PR read checks, and local Python Q8 execution only. Agda binary unavailable here. No exact-head kernel acceptance, transitive zero-postulate clearance, physical Haar, physical Wilson RG limit or Clay mass-gap proof. Attribute Wilson, Bałaban, Haar, Osterwalder–Seiler/Menotti–Pelissetto, Osterwalder–Schrader and original DASHI theorem owners.

**Late 3 November current R445 source:** The full exact group-valued 4D blocked-link holonomy, SU(N) adapter and selected side-four block-two/coarse-two endpoint/gauge law are now source-written. The **all-size** endpoint, real Wilson Gibbs measure disintegration, RP and cutoff-uniform physical estimates are not thereby proved. See the canonical exact ledger and receipt below.

**R443.F07 executable reference update:** `scripts/check_ym_native_c3_adjacent_swap_word.py` deterministically synthesizes the selected spatial C3 adjacent-swap word; for the side-four original 1024-link list, an independent reference execution produced 46,592 adjacent swaps and verified the resulting permutation. This is a finite reference receipt, not the Agda `LinkPermutation`/`onCanonicalLabels` proof; F07 remains OPEN.

## 2026-11-03 — AUTHORITATIVE current YM exact-lemma reconciliation

**Per-field canonical inventory:** [YMClaySubmission219FieldInventory20261103.json](YMClaySubmission219FieldInventory20261103.json) now literally lists the 219 A–I source record-field names, IDs and source blob SHAs, and `scripts/check_ym_219_field_inventory.py` detects source drift. This is a verified 219-field enumeration, NOT individual theorem discharge or Clay closure. The current 43-entry producer-level R443/R445/R320/R333/Clay/TRUST lemma matrix remains in [YMClayCurrentExactLemmaLedger20261103.md](YMClayCurrentExactLemmaLedger20261103.md).



**Read this before historical append-only sections:** [YMClayCurrentExactLemmaLedger20261103.md](YMClayCurrentExactLemmaLedger20261103.md) is the canonical current *source-status* ledger for R443/R445/R320/R333/Clay. Its IDs are stable for the current max-cut: R443.F01–F07/P01–P05; R445.F01–F03/P01–P09; R320.P01–P06; R333.P01–P07; CLAY.P01–P03; TRUST.K01–K03. The older 219-field submission inventory and frozen four-family research scoreboard remain separate uncompleted formulations of the same Clay endpoint, not five additional official Clay problems.

**New actual code**: `YMClayNativeC3SingleVectorPermutationCertificateExact.singleVectorC3ImpliesAllVectors` derives the formerly universal 1024-coordinate `ExactC3AdjacentSwapWitness.matchesNativeVector` from ONE exact equality on the canonical original bond-label Vec. `YMClaySUNConstructedNativeC3SetoidHaarExact.adjacentSwapFromOneVector` and `originalNativeC3GibbsHaarInvariantFromOneVector` attach this to the **existing original native SU(N) Wilson/Gibbs Haar consumer**. R443.F07 — finding the actual `LinkPermutation 1024` program and proving the one label-vector equality — is still OPEN. Constructing genuine compact Haar remains a separately OPEN physical R443.P01–P03 input, not solved by C3 combinatorics.

**Verification**: GitHub readback only. `agda --safe` and whole-TOE kernel check NOT RUN; imported `RealAnalysisAxioms` contains postulates, including in historical locally `--safe` modules. All new Agda terms remain SOURCE (not kernel accepted). Do not infer the selected CMP116 physical mixed-J decay, same-H OS physical gap, R445 continuum, or Clay completion from the finite index equalities. #1440 is Route-S parent, #1444 is the YM implementation, #1460 TSVF/KK is downstream and **not** an OS/mass-gap premise.

## 2026-11-03 — YM R443 native C3 and R445 physical blocked-lattice max-cut (PR #1444)

**Docs → TODO → code → changelog synchronization.** Parent #1440 is the Route-S R320/R333 consumer; #1444 is the physical four-dimensional Yang–Mills construction; #1460 is a downstream TSFV/history/KK consistency and same-clock comparison only. The 2014/2017 TSVF macroscopic-robustness proposal, branch-reversal and operational time arrows **do not** provide the Osterwalder–Schrader (OS) temporal reflection, a positive Yang–Mills transfer matrix, a physical four-dimensional continuum, or an OS Hamiltonian gap by themselves.

**R443 finite C3 paid in source (Agda acceptance pending):**
- `DASHI/Physics/YangMills/YMClayFiniteNativeBondReindexingSafeExact.agda`: generic **original positive bond** Vec reindexing and pointwise lemma, with identity, composition, two inverse lemmas and triple-order law. Imports only the existing safe finite original torus/codec; no real-number/Haar/RG assumptions.
- `YMClayNativeSideFourC3VectorWeldExact.agda`: instantiates the **literal existing** `CMP119FlatSide4SpatialC3FieldCovarianceExact` axes/site `(x0,x1,x2,x3)→(x0,x3,x1,x2)` and `YMClayNativeRationalSU2Side4C3CarrierWeldExact.nativeForwardC3Bonds` on the actual original **1024 positive-bond** Vec. Constructs the forward/backward coordinate maps, their exact two-sided inverses, `bondOrderThree`, `nativeForwardIsVectorAt`, `nativeForwardEncodesExactly`, `forwardVectorOrderThree` with no global function extensionality.
- `YMClaySUNConstructedNativeC3SetoidHaarExact.agda`: supplies the old `SUNNativeSetoidBondCodec` encoding/decoding and `c3DecodeAt` from these **already constructed** finite sources. The remaining EXACT finite R443-C3 input is ONE `ExactC3AdjacentSwapWitness`: `Product.LinkPermutation 1024` and `∀v, permuteLinks program v ≡ NativeC3.forwardVector v`. This is a *finite syntactic-adjacent-swap proof*, not an additional physical C3 field or Haar invariance axiom. When supplied, the existing `nativeSUNPhysicalGibbsSetoidHaarC3` immediately transports actual real SU(N) Gibbs/C3 integrals conditionally on its one-link Haar/Fubini source.
- `scripts/check_ym_original_c3_bond_vector_reference.py` independent integer reference passes sides 1–5. At side four it finds **16 fixed positive bonds and 336 three-cycles**; all 1,024 labels are covered. Wrong-axis control intentionally disagrees. This is a reference experiment, **not** Agda/kernel acceptance or construction of the adjacent-swap proof.

**R445 genuine original blocked-lattice carrier paid in source (Agda acceptance pending):**
- `YMClayNativeCyclicFinIsoSafeExact.agda` proves the original `Torus.CyclicIndex N` ↔ stdlib `Fin N` two-way iso, without real analysis.
- `YMClayNativeBlockedPeriodicBondWeldExact.agda` composes that with the **existing** `P06FaceCubeTorusGeometry.Cube4` and `BalabanBlockedPeriodicLattice.finePoint/splitFinePoint`, obtaining exact two-sided `blockNativeSite/unblockNativeSite` and `blockNativeBond/unblockNativeBond` for the original `Torus.PositiveBond (M*L)` and the actual four-dimensional block coordinates. It never substitutes a new lattice/gauge field. Important: this is **bond-label/site geometry only**, not a link-valued path block, a gauge-equivariant Wilson coarse action, a disintegration of the physical SU(N) Gibbs measure, reflection compatibility, beta(a) calibration, or continuum stability. `scripts/check_ym_original_blocked_bond_reference.py` independent integer tests for (M,L)=(1,1),(2,2),(3,2),(2,3),(4,2) pass both roundtrips. At M=L=2, 256 fine sites and 1024 original positive links are recovered.
- New owners imported/re-exported from `DASHI/Unified/BalabanRGTOERegression.agda`. Golden `{-# OPTIONS --safe #-}` is used only on the isolated finite codec/reindex/Fin equivalence; physical adapters which depend on `RealAnalysisAxioms` are explicitly **not promoted** to an assumption-free result.

**Exact remaining active max-cut**: (P0) compile the actual 1024-coordinate C3 action into `LinkPermutation` and prove `matchesNativeVector`; instantiate *continuous compact SU(N)* normalized Haar on the selected measurable integrable test algebra (avoid the existing total-all-functions `OneLinkProductHaar` paradox), with SU(2)/matrix/Bishop real and `Integrable` compatibility, positive/linear Fubini and rigorous full-support partition positivity; (P0/P1) construct original **group-valued block edge path product** from the now proved native blocked labels and establish gauge naturality, selected Wilson/reflection-positive cylinder compatibility and genuine pushforward/disintegration for each changing fine/coarse lattice; (P1) beta(a), volume/spacing and actual physical R445 tails, moments, tightness, continuum and infinite-volume OS closure; (P1) selected CMP119 R124 E/R/B/V source and CMP116 mixed-J rooted-shell decay on the SAME measures; (P1) actual R333 same reconstructed OS Hamiltonian uniform positive spectral gap and nontriviality. The older Bałaban Gate4 UV iteration/closure record remains *conditional on one-step physical analytic inputs*. Independent lower-dimensional or KK/TSFV finite results cannot be promoted to Clay's four-dimensional pure quantum YM proof.

**Trust / verification boundary:** This is GitHub source-written and readback-checked, with independent deterministic integer references executed. Agda is unavailable locally: no exact-head Agda typecheck, full transitive `--safe` audit, or zero-postulate proof certificate was executed. `DASHI/Foundations/RealAnalysisAxioms.agda` explicitly postulates its `ℝ` and analytical facts; the native physical source chain inherits that authority, regardless of local `--safe` annotations. Original authorship: Wilson (lattice gauge action), Tadeusz Bałaban (periodic geometry/RG), Haar/Fubini, Osterwalder–Seiler/Menotti–Pelissetto (lattice reflection positivity), Osterwalder–Schrader (reconstruction), and original DASHI theorem owners.


## 2026-11-03 — YM max-cut continuation: safe finite gauge split and true moving-cutoff family

**New, reused source owners in PR #1444** (do not pull downstream PR #1460 back into parent):
- `DASHI/Physics/YangMills/YMClayNativeFiniteGaugeVectorNaturalitySafeExact.agda`. Pure finite `{-# OPTIONS --safe #-}` source, relying on the original finite torus, duplicate-free bond enumeration and generic `CompactLieGroupCore.Group`. Proves `vectorGaugeEncoded`, `vectorGaugeDecodedAt`, `originalGaugeDecodedAt`, and `encodeGaugeNatural`. Parameters are the actual finite periodic side, group laws and the original positive-bond target; no real-number/Haar/OS/RG assumptions. Existing postulate-free `BalabanFiniteEnumerationDistinctExact` and `CompactLieGroupCore` were promoted to `--safe` for this isolated chain. Source-written; compiler **not available/acceptance pending**.
- `YMClaySUNConstructedPeriodicGaugeCodecExact.agda` now imports the finite source. Its `safeVectorMatchesBilateral` identifies finite group-coordinate action with the original bilateral SU(N) one-link action; `safeNativeGaugeDecodeAt` supplies the original `OriginalPeriodicGaugeVectorNaturality.gaugeDecodeAt` field. The theorem remains a conditional physical adapter (true compact Haar not yet supplied).
- `YMClaySUNVariablePhysicalCutoffFamilyExact.agda` now constructs the actual dependent sequence `linksAt n`/ `physicalFiniteCutoffMeasure n` from the original periodic SU(N) Wilson action and **single shared one-link Haar authority**, with variable beta(n). It records exact `4(n+1)^4` link count, original same-source Gibbs density/partition, conditional partition positivity, native Wilson-action gauge invariance and normalised Wilson-deficit expectation invariance for every finite n. It does **not** force arbitrary sides into a common configuration carrier and cannot be conflated with `YMClaySUNMatrixSameFamilyR443R445Exact` (which changes beta on the fixed side-four space). The moving-family module is deliberately not declared golden because its real-analysis and Haar sources are postulated/conditional.

**Trust boundary found:** `DASHI/Foundations/RealAnalysisAxioms.agda` explicitly introduces postulated `ℝ`, arithmetic/order and other external-analysis facts. Any imported dependent physical source that passes through it cannot be described as **transitively zero-postulate Golden Agda** without an actual replacement/proof of the underlying constructive real analysis. Some existing modules have a local `{-# OPTIONS --safe #-}` pragma even though they import that source. This is an **unresolved Agda safe-import boundary**, not a kernel acceptance receipt. New `scripts/check_ym_golden_agda_trust_cut.py` traverses local DASHI imports and reports `--safe` mismatches and inherited postulates. It is a read-only **source scan**, never substitutes for `agda --safe` or the transitive kernel trust audit.

**Classical versus Euclidean quantum source:** The sourced classical equation `D_mu F^{mu nu}=J^nu` is an Euler–Lagrange/current statement. The selected 4D Euclidean Wilson path measure is `dμ ∝ exp(-S_E) ∏_b dH_{SU(N)}(U_b)`. One cannot infer the physical measure, reflection positivity or a positive mass gap from the classical equation. Clay's **pure gauge** sector does not inherit matter-source quark currents merely because an unrelated classical statement allows `J ≠ 0`. See the existing `DASHI.Physics.Closure.YangMillsFieldEquationReceipt`, `YMStrictSelectedStationarityToSourceEquation`, `BalabanP33LiteralCovariantDivergenceDifferenceExact` and Wilson/OS owners; no duplicate field equation is introduced here.

**Exact remaining P0/P1 physical cut:** instantiate actual continuous compact SU(2)/SU(N) Haar on a selected measurable/integrable test algebra (the present `OneLinkProductHaar` is total on all functions, while `CompactLieAnalyticPackage.NormalizedHaarTheory` uses an explicit `Integrable` predicate); match the selected real/matrix/carrier; construct C3 permutation witness on the actual bond Vec; align `beta(a)`, spacing, volume, CMP119 R124 E/R/B/V physical sources, original changing-lattice cylinder/refinement, uniformly bounded moments/tails and continuum. Then the original CMP116 mixed-J rooted-shell estimate, same OS Hamiltonian R333 spectral lower bound, nontriviality and Clay scope remain independently required. Older Bałaban Gate4 UV iteration still requires its one-step analytic and physical continuum/OS inputs. No 5D/KK reduction, classical sourced equation or finite reference checker proves these.

**Verification:** GitHub commits/readback for the new sources and imports; local original-bond Python rational fixture from the prior YM round. The **new** Agda modules have not been kernel-checked in this session (Agda executable unavailable), and the recursive trust scanner is not itself a proof. Attribution to Wilson, Haar/Fubini, Balaban, Osterwalder–Schrader, original DASHI owners; independent KK/TSFV worker is downstream only.

### 2026-11-03 — generic all-L positive-link counting payment

`YMClayNativePositiveBondEnumerationVectorExact` also proves `listLengthMap`, `listLengthAppend`, `listLengthCartesian`, `listLengthAllCyclic`, `originalSiteCountFormula`, and `originalPositiveBondCountFormula`. Thus the **actual canonical** original periodic configuration has exactly `((L*L)*(L*L))*4` positive bonds for every finite side `L`; the 1,024-link side-four equation is now derived from the generic count. These theorems are finite enumeration/coordinate laws, not cutoff-independent physical moment bounds. Source-written, kernel check pending.

### 2026-11-03 native finite bond codec independent exact-rational fixture

Committed `scripts/check_ym_native_periodic_bond_vec_codec.py`. The local execution of this same script (standard Python `fractions.Fraction`, no external dependencies) passed: side 2 (16 sites / 64 bonds), side 3 (81 sites / 324 bonds) and side 4 (256 sites / **1,024 bonds**); for every bond, field→vector→field, vector→field→vector, and original `(gamma_x U) gamma_y^{-1}` versus vector `gamma_x (U gamma_y^{-1})` agree exactly. Wrong target inverse disagreed on 52, 256, 820 bonds respectively, and a duplicate-label enumeration fails the vector roundtrip as expected. These diagnostics cross-check enumeration order and group-product association, **not** Agda kernel acceptance, compact Haar, all-observable integrability, R445 physical limits, CMP116 or OS.

This narrows the literal R443/R445 finite **codec + gauge naturality** from assumed record inputs to source-written canonical enumerations. Still NOT paid: the selected C3 product permutation syntax/witness, continuous compact one-link Haar and scalar-carrier weld, selected CMP119 R124 metric insertion, continuum/UV estimates and same-H gap.


### 2026-11-03 — P0 original bond codec + native gauge naturality (YM PR #1444)

**New Golden Agda source-written theorem owners:** `YMClayNativePositiveBondEnumerationVectorExact` and `YMClaySUNConstructedPeriodicGaugeCodecExact`. The first reuses the original `BalabanPeriodicTorus4Carrier.periodicTorus4Finite`, `productFinite`, and `BalabanFiniteEnumerationDistinctExact.cartesianDuplicateFree`. It constructs the ORIGINAL positive-bond list for **each actual periodic side L**, computes its length, proves duplicate-freeness and defines exact field-to-Vec/Vec-to-field codecs. `originalBondsDecodeEncodeAt` proves pointwise function roundtrip; `originalBondsEncodeDecodeExactly` proves the vector roundtrip from duplicate-free membership, without unrestricted function extensionality. `originalSideFourCountIs1024` pins the literal side-four 4×4⁴ count.

The second owner supplies the previously **uninhabited** `YMClaySUNVariablePeriodicGaugeHaarExact.OriginalPeriodicGaugeVectorNaturality` on the actual periodic SU(N) field at every n. It constructs coordinatewise `gamma(source)` and `inverse(gamma(target))` via the original bond enumeration; `actualGaugeVectorEncoded` / `actualGaugeVectorDecodedAt` match the existing finite vector gauge action with the original bond-function transform. The critical associativity step maps `(gamma(x) * U) * inverse(gamma(y))` to `gamma(x) * (U * inverse(gamma(y)))`. As a result, `actualPeriodicGaugeHaar`, `actualPeriodicGaugeNormalized` and `actualSixDeficitGaugeNormalized` reuse the selected **same finite measure** and existing bilateral one-link Haar theorem without independent decoder, global Haar invariance or gauge-vector naturality fields.

**Remaining R443 analytical inputs:** the existing abstract `CertifiedSUNMatrixTheory` needs an actual chosen compact real/complex group with normalized real trace and compatible real scalar; `OneLinkProductHaar` / `OneLinkSUNBilateralHaar` / ordered and strictly-positive integration still require an applicable *continuous compact Haar* source and measurable/integrable test algebra. The all-bond C3 permutation/selected-observable naturality is distinct from the gauge naturality constructed here. A finite Vec roundtrip is **not** physical compact Haar. **Remaining R445**: cutoff-refinement/cylinder compatibility, selected CMP119 E/R/B/V beta and metric insertions, uniform moments/tails and continuum convergence. **Remaining R320/R333**: actual physical mixed-J CMP116 rooted-shell decay, same H2/OS reconstructed continuum Hamiltonian and strictly positive uniform gap/nontriviality; the full Clay scope remains open.

**PR stack and dimensional safeguard:** `#1440` (Route-S) is the base of `#1444` (this finite YM source); `#1460` (Lorentz/TSFV/KK) is stacked on `#1444` but owns separate conditional signature and KK reductions. The downstream `YMClayFiveSectorBidiSteelmanExact` proves finite ten-plane Nat accounting and exhibits an uncancelled fifth-axis curvature example. That is a useful **negative-control requirement for any 5D→4D physical action comparison**, not an extra premise of pure 4D YM and not a proof that the KK fields decouple. Do not import downstream PR #1460 into the parent proof graph. Older Bałaban UV work (#568, `BalabanClayGate4CombinedRGUVIterationExact`, `BalabanClayConcreteUVToMassGapDependencyExact`) retains analytic one-step and OS/continuum physical inputs; no finite codec closes those.

**Verification/accounting:** Connector source readback and syntactic no-hole/no-local-postulate inspection were performed. Agda `--safe` typecheck, complete trust/axiom audit, Lean same-object acceptance and CI were **not executed**. This is a source-written *finite* closure, not a physically accepted continuum or Clay proof. Attribution: Wilson, Bałaban, Haar/Fubini, Osterwalder–Schrader, canonical DASHI enum and matrix proof owners, and the other worker's independent five-sector audit.


### 2026-11-03 — R443/R445 every-n native gauge and Haar numerator theorem

Added `YMClaySUNVariablePeriodicGaugeHaarExact.agda` atop the new variable-size product-Haar source. It reuses `YMClaySUNVariablePeriodicGibbsGaugeExact.periodicSUNGibbsDensityGaugeInvariant`, `YMClaySUNProductHaarGaugeFromOneLinkExact.productHaarNativeGaugeInvariant` and `YMClaySUNVariablePeriodicBondPointwiseExact.variableGibbsDensityPointwise`. The owner proves `periodicProductGaugeHaarInvariant`, `periodicGaugeNumeratorInvariant`, and `periodicGaugeNormalizedExpectationInvariant` for every actual periodic cutoff and every explicitly pointwise-congruent cylinder observable. It derives *whole finite product integral* local gauge invariance from one-link left/right invariance without a second independent full-lattice Haar axiom.

`OriginalPeriodicGaugeVectorNaturality.gaugeDecodeAt` remains a typed physical input **at each original positive bond**. The native vector decoder, gauge factors, measurable one-link continuous Haar and same carrier scalar transport are not yet inhabited. This result does **not** establish exact varying-cutoff cylinder refinement, CMP119 E/R/B/V selected metric insertions, uniform R445 moments, physical CMP116 R320 bounds, or R333 continuum OS spectral positivity. Preserve the Golden Agda source-written / kernel-pending boundary.


### 2026-11-03 — original variable-periodic Wilson–Gibbs product-Haar finite cut

New source-written golden owner: `DASHI/Physics/YangMills/YMClaySUNVariablePeriodicProductHaarExact.agda` (on YM PR #1444). Unlike the earlier fixed side-four family, this module is parameterized by **every actual periodic lattice size** `n` and reuses the original `YMClaySUNVariablePeriodicGibbsGaugeExact` six-positive-plane action and Gibbs density. It constructs the finite physical measure from `YMClayFiniteProductHaarPermutationExact.productIntegral` of **one** link source, without an arbitrary independent full-field integral at each n.

Source-written statements: `periodicProductHaarUnit`, `periodicActualDensityStrictPositive`, `periodicProductPartitionStrictPositive`, `periodicProductIntegrationLaws`, `periodicProductDensitySameObject` and `periodicProductPartitionSameObject`. One-link normalization/Fubini/linearity/positivity propagate to every finite product; Gibbs partition positivity follows from selected one-link *strictly positive integration* rather than assuming a nonzero partition. The corresponding exact owner is imported and re-exported by `DASHI.Unified.BalabanRGTOERegression`.

**Not paid:** `OneLinkProductHaar` is a total test-functional interface, not by itself genuine continuous SU(N) Borel Haar. The per-n native vector decoder, true native bond count/order (side four: 1024 links), full-support measurable test class, concrete SU(N)/Bishop-real/legacy real weld, selected CMP119 R124 E/R/B/V metric insertion and counterterms, cutoff-refinement/cylinder consistency, physical R445 uniform moments/tightness/limits, selected R320 CMP116 differentiated mixed-J decay and R333 same-H OS spectral separation/H6 remain open. The constructor has **no source-written cross-cutoff consistency assumption disguised as proof**. GitHub write/readback is not Agda kernel acceptance, and imported foundational postulates remain outside zero-axiom trust.

Recommended next max-cut: (P0) inhabit actual selected compact one-link Haar + side-four and variable-size original bond decoder, then propagate same Gibbs measure into the exact CMP119 selection; (P1 independent) physical R445 uniform marked moment and source compact-containment; (P2) selected CMP116 source-envelope estimate; (P3) OS physical mass gap/nontriviality.
### 2026-11-02: reconcile all prior plaquettes + variable-size SU(N) source

The source search found an older **canonical** `SUNWilsonAction` / `SUNWilsonClassFunction` owner. The new `YMClayNativeSixPlaquetteSUNWilsonActionWeldExact` builds a typed original signed-word `Path` and **proves** exact native original-positive-six-plane action equality with that canonical owner at each side-four site, globally, and after beta weighting. The trace-cyclicity-derived `SUNMatrixRealTrace` is now projected into the old canonical `SUNWilsonTraceAuthority`. `YMClaySUNVariablePeriodicGibbsGaugeExact` lifts original finite periodic SU(N) Wilson/Gibbs action and full local gauge invariance from fixed n=3 to **every original periodic lattice n**, using the real existing site enumeration rather than an abstract cutoff index. Source-written, Agda kernel not run; **no physical compact Haar, uniform R445 estimates, selected CMP116 R320 decay or same-H R333 gap is inferred**. Full search/ownership/attribution and exact remaining leaves: [source audit](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md).

### 2026-11-02: full native SU(N) finite gauge invariance (source-written)

`YMClaySUNMatrixSixPlaneGaugeInvariantExact` now reuses the selected native group gauge transformation, transformed-link/word equality, source positive-plaquette gauge cancellation, certified SUN matrix trace class function, original six-plane real site sums and literal beta-weighted Gibbs exponential. It proves the full original six-plane action **and same Gibbs density** are locally gauge invariant, not merely an individual plaquette. This removes any independent finite Gibbs gauge-invariance leaf, conditional on actual SUN matrix/trace theory inputs. Independent SU2 quaternion numerical fixture passed all 1536 original six-positive plaquettes (256 sites/1024 links) with max real-trace error 7.77e-16, action before=after 1538.045855541643. Source-written theorem remains uncompiled; fixture is NOT kernel certification. R443 normalized continuous Haar/Fubini + literal native bond-vector codec, R445 changing-cutoff physical tails, R320 CMP116 selected decay and R333 same-H OS uniform gap remain open.

### 2 November 2026 — physical SU(N) matrix-link and product-Haar max-cut

Canonical exact-lemma/source-owner crosswalk: [YMClaySUNMatrixR443R445R320R333MaxCut20261102](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md). This tranche **reuses** the existing `SUNMatrixCarrier`, `CompactLieGroupDerived`, original signed periodic Wilson owners, canonical CMP119 expectation and R278 covariance, R320 CMP116 physical source and R333/round557 OS consumer. It does not add a parallel rational/quaternion Haar source or assert a Clay solution.

**Source-written Agda (kernel/CI deferred):** `YMClaySUNMatrixNativeSignedWilsonExact`, `YMClaySUNMatrixWilsonTraceGaugeExact`, `YMClaySUNMatrixSixPlaneGibbsDensityExact`, `YMClaySUNMatrixSameFamilyR443R445Exact`, `YMClayFiniteProductHaarPermutationExact`, `YMClaySUNMatrixProductHaarC3Exact`, `YMClaySUNMatrixR445R320SameCovarianceExact`. These derive original signed SU(N) matrix Wilson holonomy/C3, gauge trace invariance from matrix trace cyclicity, literal six-positive-plane real Gibbs density, no-free-equality finite expectation, finite product-integral permutation invariance from two-link Fubini, C3 integral invariance under an explicit bond-to-vector permutation codec, and same-source R278 covariance from the finite real matrix Gibbs family.

**OPEN, exactly:** (R443) actual instantiated continuous SU2/SUN matrices, physical ReTr/N, one-link normalized compact Haar/Fubini and the 1024-positive-bond enumeration/C3 codec, selected beta/counterterms and Gibbs normalization; (R445) true *varying-lattice* UV and volume continuum, uniform moments/marked tails and physical cylinder consistency; (R320) selected CMP116 mixed-source derivative rooted-shell physical estimate with uniform domain and constants; (R333) the *same* OS reconstructed physical Hamiltonian with uniform strictly positive continuum/infinite-volume spectral gap, OS/Wightman nontriviality and Clay compact-simple-group scope. The previous n=3 rational fixed-volume 0..3072 bound is not a continuum-uniform estimate. **No physical source is promoted from a conditional record.**

### 2 November R445 native fixed-volume majorant

New source-written (kernel not yet run): `YMClayR445NativeSixDeficitUniformFiniteBoundExact` reuses the native normalized SU(2) trace inequalities, original six positive plaquettes and side-four rational sums. It proves the **literal rational action bounds** `nativeSixDeficitNonnegative` and `nativeSixDeficitAtMost3072` for every `RationalSU2BondData 3`. The constant is exact: six planes × 256 sites × maximum Wilson deficit 2 = 3072. This pays the finite R445 original-six Wilson majorant mentioned in the 1 November backlog. It is **not** a uniform bound across increasing lattice volumes/cutoffs, and says nothing by itself about compact Haar integrability, stochastic tightness or a continuum OS mass gap.

### 2 November 2026: R443 auxiliary-gauge marginalisation / source cut

**Source-written, exact-head Agda compilation pending.** `YMClayR443BondMarginalC3Exact` now factors the original native six-plane Wilson deficit through the actual n=3 bond field, proves its C3 square without the auxiliary `siteGauge`, constructs a pushforward finite measure on bond-only observables, derives that measure's integration/partition laws from the already-selected Gibbs source identity and source integration laws, proves normalized expectation equality, and reuses the existing R443→R431 numerator C3 compiler on that bond-only carrier.

This **pays the auxiliary-coordinate algebraic marginalisation** subcut; it does not pay compact SU(2) Haar. Rational norm-one quaternions form a proper countable subgroup of full compact SU(2). A normalized compact-group Haar law cannot be obtained just by naming an arbitrary integral on rational points, or by pushing it along the bond projection. The next R443-Haar source is a *different* compact-real link carrier, with a proven rational-to-real holonomy/action comparison and an actual compact product-Haar/change-of-variables construction. Do not report `NativeSixPlaneHaarBoundary` as a constructed physical Haar law.

The remaining high-alpha chain is: **real compact SU(2)/SU(N) source + Haar Gibbs ↔ same-action Wilson comparison → varying-cutoff R445 convergence/observable tails → selected R320 decay → same OS Hamiltonian R333 uniform positive gap → nontrivial full four-dimensional Clay scope.** n=3 is a fixed side-four lattice, not a UV scaling trajectory. K0 compilation remains deferred to the user.

### 1 November selected gauge/Wilson coarse-fine theorem contract

`YMClayVoyagerCovariantWilsonCoarseFineBidiExact` now proves a conditional
same-fine-carrier Wilson gauge-invariance result by *both* selected physical
commuting squares: `block∘gaugeFine=gaugeCoarse∘block` and
`Wfine=Wcoarse∘block`, plus gauge invariance of coarse Wilson. The second
equality is a strong test target, NOT automatically true for generic RG
blocking; correct coarse effective observables may need retained fibre or
quantitative defects. Do NOT turn this into an unconditional physical
theorem. The canonical OS-form pullback uses the distinct existing
`BalabanWilsonTransferBlockingExact` owner.


## 2026-11-01 further Yang-Mills symmetry/source recut

Full cross-repo source map: `Docs/physics/YMClayVoyagerCrossDomainSymmetryMaxCut20261101.md`.

Highest-priority pre-existing *theorem-bearing* direct physical C3 owners were omitted in the first video pass:
`BalabanC3MonsterEquivarianceAuditExact`,
`CMP119FlatSide4SpatialC3FieldCovarianceExact`,
`CMP119ClassicalCurvatureSpatialC3CovarianceExact`,
`BalabanWilsonD4SubsetCharacterExact`, and
`BalabanWilsonTransferBlockingExact`.
The literal four-axis site/bond/curvature C3 action is already source-written;
the full nonlinear generated-action R144/OS/R445 same-object lift and
intermediate equivariance are NOT inhabited. The target is selected SU2/compact
simple physical Wilson source, not a generic 369 observer.

Original jCOARSE/jFINE and `CoarseFineFabricCalculusExact` are genuine prior
projection nonfactorability theorems. `CompactLieLatticeGauge` is a **different**
genuine group-valued Wilson holonomy owner; `Base369Ternary27StratifiedFibreHolonomyExact`
is an explicitly-labelled finite holonomy *analogue*. The particularly
strong Agda #1249/Lean #84 donor supplies path graph 27/729/19683 gauge
covariance/negative flux controls. Import only after same-source field,
plaquette, gauge-group, blocking and Wilson-observable identities are proved.

Complex `i` = 90° real-linear J on an oriented 2-plane, NOT a third spatial
coordinate; source `ConcreteComplex` / `OrdinaryComplexPolar`, new finite
`YMClayVoyagerImaginaryC3DimensionBidiExact` quarter-turn/C3 discriminator,
`PolynomialMonodromyTernaryQuaternionBridgeExact` from branch Agda #1414
(quaternion Spin(3)). Wick, SO2, SO3 and SU2 must remain distinct maps.

`dashifine` 26/31 signature experiments and canonical Agda
`OrbitSignatureDiscriminant` / `CausalOrderLorentzClosure`: conditional
3+1 normal form but the selected tag 31 is included in the profile input;
independent tag-free derivation from physical data remains unpaid. The
`YMClayVoyagerDimensionSignatureForkExact` finite 2/3/4/5 YM coupling weight
and Creutz-5D/KK-5D/stochastic-time distinction do NOT prove dimensional
compactification, Lorentz selection or physical theory.

Probability `Markov` **inequality** in
`BalabanClayT5Path4MarkovProkhorovExact` differs from stochastic
Markov `transition`/invariant-law `YMClayVoyager2026CoverageExact`,
`DashiMarkov` transition sufficiency and
`FiniteStochasticBisimulationExact` coarse-kernel negative control.

Proposed YM spectral ζ must be constructed from same reconstructed
`H_OS`, with zero-mode removal/heat trace/Mellin domain and
infinite-volume trace regularization justified. Existing number-theory
Riemann ζ, modular j, Casimir ζ(-3) are *separate functions/objects*.
No zeta phrase in Voyager video.

**Do not demote the live P0:** same selected R445 measure/tail/moment and
R320/H1, actual R333/H_OS physical spectral attachment, OS/UV/IR
continuum, nontriviality and compact-simple-group scope.


## 1 November 2026: Voyager video completeness / source-calibration crosswalk

The chapter-by-chapter source-to-owner audit is
`Docs/physics/YMClayVoyager20260929CoverageAudit.md`. Golden Agda:
`YMClayVoyager2026CoverageExact.agda` (coverage/status, native P2
reuse, Route-S no-promotion, finite-versus-uniform gap theorem, stochastic
local/global/invariant-measure type separation), plus
`YMClayVoyagerR4HodgeBasisExact.agda` (six signed Euclidean four-dimensional
2-form basis directions and proof that `*^2 = +1` on those signed bases).
These are source-written proof candidates; **exact-head Agda kernel not run**.

Video topics indexed: Landau QED pole, Gross-Wilczek/Politzer beta sign,
Wilson blocking, lattice gauge/closed holonomy, strong-coupling area law,
Creutz 1979 **and distinct 1980** numerical studies, dimensional transmutation,
Balaban and MRS fixed-IR vs infinite-volume limitation, stochastic Parisi-Wu
and 2024 local 3D YM-Higgs, Chevyrev-Shen 2026 3D gauge-covariant
renormalisation uniqueness and 2D invariant YM Langevin law, classical
Donaldson/Freedman/Casson/Gompf instanton topology and exotic R4.

**Exact live highest-alpha payment remains unchanged:** actual R445
selected same-source physical 4D CMP119 Wilson measure/tails/moments, real
selected continuum family and OS axioms, R281/P3 literal spectrum =
reconstructed `H_OS` spectrum, nontriviality, uniform IR infinite-volume
gap and Clay group scope. Finite loop bounds and R320→R333 compilers are
not these inputs.

New finite classical Hodge result is **not** the metric Hodge-star of a
smooth 4-manifold: the missing lifts are linear extension, oriented metric,
2-form half projections, ASD/SD curvature, classical YM E-L implication,
instanton moduli and external smooth four-manifold topology theorems.
The existing `YMStrictSelectedHodgeAlgebraLaws` is finite 2D/selected and
must not be identified with this new flat Euclidean R4 basis. Likewise,
3D local-time Markov existence, equilibrium of the *same* 3D stochastic
flow and a 4D pure YM QFT are separate theorem targets.

**Attribution:** named original authors hold source claims; DASHI owns
source-written adapters only. No Monster/3B, ESD or Clay promotion.

# Clay Yang-Mills Proof Roadmap


### P2 rational-trace / same-algebra alternative (30 October extension)

The canonical `BalabanSU2RationalWilsonTraceBoundExact` proves
`-1 <= realPart(q) <= 1` for rational unit-quaternion SU(2) data.
`YMClayLiteralWilsonS2SameAlgebraBoundExact` now defines the proof-bearing
`RationalSU2TraceGramBoundSource` and the explicit projections
`rationalSU2TraceToSameAlgebraWilsonBounds` and
`rationalSU2TraceBuildsCanonicalS2`. Once one same-carrier `pointwiseUnitBoundGivesGramBounded` interpretation and `traceIsLiteralWilson` equality are exhibited, **all loopwise boundedness fields** follow from the existing literal configuration-dependent Wilson-path theorem. The resulting
canonical S2 inputs feed `YMClayLiteralWilsonP2ExpectationConvergenceExact`
and the already-proved three selected expectation-limit compilers. This removes a family of duplicate P2 per-loop boundedness proofs. The record now additionally requires `traceIsLiteralWilson`, an explicit equality on the SAME physical loop carrier. Boundedness is transported along that equality with `subst`; an arbitrary synthetic trace observable cannot be substituted into P2.

The exact
remaining P2 obligations are now the trace→Gram physical interpretation,
bounded-product closure, exact literal identity same-object equality, selected Euclidean
translate/support-time identity, and actual measure convergence on the same
physical theory. The rational-quaternion argument alone is **not** a proof
over full continuum Haar SU(2), nor an independent gauge-measure limit.



### Canonical rational Wilson-function donor (30 October late reuse correction)

Further source-tree archaeology found the existing
`BalabanLiteralRationalSU2WilsonBoundedAlgebraExact.agda` owner. It already
constructs **configuration-dependent** `RationalWilsonPath n` observables
using periodic bond holonomies, proves the complete pointwise unit bound
`literalWilsonPathPointwiseUnitBounded`, and proves one/multiplication
pointwise closure. The new P2 bridge now consumes this owner *directly*:
`physicalWilsonObservable : RationalWilsonObservable n → TestObservable`,
`traceIsLiteralWilson` on the actual path observable, and
`pointwiseUnitBoundGivesGramBounded` transport the existing theorem onto
the same physical `Gram.BoundedObservable` carrier. The bounded identity
follows from the existing literal unit observable and an exact same-object
identity equality, rather than being independently assumed.

This replaces the earlier fixed-quaternion-per-path approximation: path
holonomy necessarily depends on the configuration. The S2 adapter also fixes the literal SU(2) scalar ABI definitionally: `one = 1ℚ`, `groupRank = 1ℚ`, and scalar multiplication is rational multiplication, rather than accepting unconstrained numeric placeholders.

Generic
`Gram.BoundedObservable` multiplication closure is still a separate
stronger physical algebra input than rational-image pointwise closure. This
is the real remaining P2 implementation wall, alongside the physical
trace/Gram map and limit/time semantics.



### 30 October, subsequent source-first native-P2 max-cut

The stronger already-existing donor chain is now authoritative for **native**
rational Wilson paths:

```
BalabanLiteralRationalSU2WilsonBoundedAlgebraExact
  -> BalabanLiteralRationalSU2WilsonCylinderBoundDataExact
  -> BalabanLiteralWilsonNativeThermodynamicProducerExact
  -> BalabanLiteralWilsonNativePhysicalMeasureExact
  -> YMClayLiteralWilsonP2NativeMeasureExact.nativeWilsonP2Limits
```

The native physical-measure owner explicitly sets
`Gram.BoundedObservable = Σ majorant, QuantitativeBound` and
`Gram.multiplyObservable =` pointwise Wilson multiplication. Thus the earlier
generic `RationalSU2TraceGramBoundSource` with its separately provided
trace-to-Gram and generic multiplication closure is a **compatibility** route,
not a primitive P2 input in the native path.

In `YMClayLiteralWilsonS2SameAlgebraBoundExact`,
`nativeWilsonSameAlgebraBoundInputs` reuses the already-produced
quantitative Wilson path bound, unit bound, bounded products and native
physical-measure definitions. No new analytic closure is assumed in this
specialization. Moreover `nativeWilsonP2Limits` already constructs all
three actual convergence proofs **without** support-distance/time geometry;
support-distance belongs to P1. Its thermodynamic/expectation input package
still must be physically inhabited; the syntactic construction is not itself
a new four-dimensional measure-existence theorem.

**Normalization fix:** the canonical `literalRationalSU2WilsonCylinderBounds`
uses `groupRank = 1ℚ` for normalized Wilson traces. The new S2 adapter now
matches this exact source, rather than confusing normalized trace with the
matrix representation dimension two. This is a same-object semantic correction.

P3 donor search also found pre-existing
`YangMillsDirectSourceOSReconstructedSpectrumH3Exact` and
`YangMillsClayCMP119RealSameOSH3Exact`. Both retain the physical
selected-spectrum / actual reconstructed `H_OS` identification as a
proof-bearing input; no new synthetic H3 spectrum is introduced.




### R445 same-marked-moment source to native P2 (30 October continuation)

Existing `BalabanClayT5MarkedMomentProducerRound444Exact` and
`BalabanClayT5MarkedPreferredExpectationRound445Exact` already compile
one marked-polymer moment closure into the exact preferred diagonal
expectation producer on a selected thermodynamic family.
`BalabanLiteralWilsonNativePhysicalMeasureExact.nativeWilsonPreferredFromMarked`
now reuses that R445 input **on the same native Wilson thermodynamic
carrier**, then
`YMClayLiteralWilsonP2NativeMeasureExact.nativeWilsonP2FromMarkedSource`
constructs the actual three P2 expectation limits using the existing
`nativeWilsonP2Limits`. No second moment package, covariance shortcut,
support-distance theorem or independent trace-to-Gram interpretation is
introduced in the native route. Remaining inputs are the actual R445
`boundedObservableTail`, continuum-tail witness, selected moment
realization and physically identified native thermodynamic/measure family.
The real CMP119 and rational P2 carriers are not asserted equal by analogy.

The 2026 external literature scan included OpenAI's October 26 public
scientific-collaboration announcement, Bałaban's original CMP116 record,
and contemporary proof proposals; externally authored proof claims are
inspiration/search inputs, not kernel proof terms or guaranteed physical
witnesses. QIDs are discovery/provenance identifiers and do not substitute
for mathematical same-object equalities; the existing Ibrahim/QID and
Monster3B ownership fences remain unchanged.


## 2026-10-30 — Route-S H1 direct-source Pareto weld

The highest-value reuse cut is the **direct source/OS** mass-gap route, not a
repetition of the strong F1/F3/F4 Mosco path. The existing owners already
provide the exact compiler spine:

```text
R320 DirectSelectedT5MarkedDecayPayment (literal selected two-J inequality)
  -> YMClayRouteSH1DirectSelectedMarkedDecayExact.h1BuildsLocalizedR295
  -> R313.exactT5JMagnitudeFromR295 (with rational |·| meaning)
  -> R296.ExactT5JMagnitudePresentation
  -> R333.CanonicalBOSIndexedApplication + Completion
  -> OS.PhysicalMassGapCertificate on the SAME reconstructed H_OS
```

The new direct bridge in `YMClayDirectSourceOSMassGapFrontierExact` is an
explicit Agda composition of **existing** owners, not a new selected-source
inequality. It removes the apparent need to pay R295/R296 again after H1.
Its remaining actual inputs are R320 physical source localization, rational
absolute-magnitude interpretation, R333's physical Wilson/time, expectation
limit and same-H_OS spectral witnesses. P1/P2/P3 in the September closed-world
audit are the corresponding direct-route cut. The independent strong
F1-C/F1-D/P_a/E_a/Mosco obligations are **not** terminal prerequisites of
Route S, but remain available for the other Pareto lane.

Source roots and authorship: Tadeusz Bałaban, CMP 116 (1988), DOI
10.1007/BF01239022 (cluster expansions and differentiated localization);
R295/R313/R320/R333 are independently authored DASHI theorem interfaces and
compilers. A published paper, a typed import, a source-written proof and an
exact-head kernel check are distinct evidence levels. No physical source
witness is fabricated; no continuum or Clay promotion occurs from this weld.
The direct consumer is now smaller and can be attacked at its actual literal
Wilson P1/P2/P3 physical inputs; all-compact-simple-group and local-QFT
extension remains a separate terminal scope. Reference comparison: OpenAI's
26 October 2026 existence announcement is not an imported proof: its Yang–Mills
Lean artifacts were not publicly released as of this review.

Status: lemma roadmap; non-promoting.

This document is a dependency graph for what a DASHI-based proof of the
Jaffe-Witten Yang-Mills existence and mass-gap problem would have to prove.
It is not a proof, and it does not promote any Clay, Wightman, Standard Model,
or terminal claim.

Current corpus correction: the live Clay-facing manuscript is now
`Docs/papers/live/Paper3YangMillsClayDraft.md`, and it sharpens the real
frontier. The finite self-adjointness and domination steps are internal to the
current draft. The older `H3a -> H3b -> no-spectral-pollution ->
thermodynamic/OS/Wightman -> mass-gap/uniqueness` continuum theorem chain is
now recorded internally at its owning theorem surfaces. The remaining live YM
frontier is therefore narrower: Clay-promotion authority, physical
Hamiltonian/mass-gap identification, statement-formulation equivalence, and
external acceptance/review. Read the roadmap below as a wider dependency
ledger, not as a more current statement than the live paper.

Current packaging correction: the repo now records the exact theorem-shape
authority chain `H3a -> H3b -> no-spectral-pollution -> RP/OS -> Wightman ->
continuum mass-gap transfer` in the proof-facing Agda boundaries. This is a
governance improvement, not a theorem promotion: the Yang-Mills frontier
remains authority-backed unless the full Balaban multiscale package is
internalized.

Current governance correction: YM is now the only major lane whose remaining
burden is still naturally missing-content-shaped rather than merely
promotion-evidence-shaped. The continuum theorem chain is explicit and wired;
the remaining load-bearing in-repo burden is the final Clay boundary rather
than H3a/H3b themselves, unless the repo stays authority-backed by design.

Reviewer-packet correction: the repo now also carries an explicit final
authority-packet layer for the same chain. The finite self-adjointness,
domination, and finite spectral-margin story is internal; `H3a`, RP/OS,
Wightman, and the final continuum transfer remain explicit external or
authority-backed steps. This improves submission grammar only and does not
change theorem ownership.

## Sprint 79 Current Fork

The live in-repo YM fork now has two ordered lanes. The UV-continuum lane comes
from Eriksson 2602.0077:

```text
Eriksson26020077Theorem16Conditional
-> BalabanCMP98LocalOscillationBoundForQhp
-> LipschitzToSquaredOscillationForQhp
-> AnisotropicAssumptionA
-> SquaredOscillationSummabilityForHalfPlaneBlocking
-> FixedFiniteVolumeBlockedObservableContinuumLimit
```

The open DASHI target in this lane is `AnisotropicAssumptionA`: the
squared-oscillation summability bound for the half-plane/spatial Balaban
blocking map `Q_hp`. The favorable spatial link count `3*L^(3k)` is only an
arithmetic balance until that bound is proved. This lane does not prove OS
reflection positivity, the thermodynamic limit, or a mass gap.

Sprint 80 narrows the immediate proof target to:

```text
BalabanCMP98LocalOscillationBoundForQhp
-> LipschitzToSquaredOscillationForQhp
-> AnisotropicAssumptionA
```

The conditional product is
`3*L^(3k)*C_local^2*L^(-4k)=3*C_local^2*L^(-k)<=3*C_local^2`. At `L=2,k=9`,
the anisotropic factor is `0.005859375` relative to `C_local^2`, and
`0.00146484375` relative to the isotropic `4*C^2` baseline.

Sprint 81 attempts the first item above from in-repo material and keeps it
fail-closed. Before `BalabanCMP98LocalOscillationBoundForQhp` can become a
proof object, the repo must define or import:

```text
FormalOscillationSeminormForGaugeLinks
FormalQhpBlockingMapDefinition
BalabanCMP98AveragingLocalityImported
QhpPerLinkInfluenceConeLMinus2k
```

Sprint 81A adds a conditional authority branch. Relative to an explicit
Balaban CMP 98 local-oscillation authority input, the in-repo arithmetic closes
`LipschitzToSquaredOscillationForQhp` and `AnisotropicAssumptionA`. The CMP 98
locality theorem itself remains an external authority input, so this does not
promote Clay/YM or a mass gap.

Sprint 81B records the support-interface blocker for the KP lane, and Sprint
81C defines the typed carriers for
`BalabanEffectiveAction`, `Polymer`, `PolymerIn`, `LinkKind`, `TemporalLink`,
`SpatialLink`, `PolymerSupport`, `SpatialSupport`,
`ResidualEffectiveActionTerm`, `ActivityDependsOnlyOnLinksInsidePolymer`,
`TemporalMeasureFactorizationLambdaOneReconciled`, and
`DefinedOnBlockedL2SpatialGraph`. The next theorem is
`EffectiveActionPolymersSpatialOnlyForA1`; only after that can the blocked
`eta=4` count be earned.

The separate KP/mass-gap lane has moved to the strong Gate-B carrier path.
The legacy weak `PolymerIn` bridge is refuted for the current carrier and is
kept only as a diagnostic guardrail.  The proof-critical lane is now:

```text
StrongActionTermTransferResidualDisjointness
-> StrongResidualPolymerMembership
-> StrongGateBToKPTheorem
-> KPEntropyAtBlockedScaleL2
-> AnisotropicL2WeightedKPCloses
-> AllDiameterWeightedKP
-> SmallFieldBoundsSurviveAnisotropicBlocking
-> BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix
-> LatticeMassGapFromAnisotropicKP
-> ContinuumMassGapTransfer
-> OSWightmanReconstruction
-> ClayYangMills
```

The current route decisions are:

```text
UV: ANISOTROPIC_ASSUMPTION_A_PROVED_IN_REPO; NEXT_BLOCKER_FIXED_FINITE_VOLUME_BLOCKED_OBSERVABLE_CONTINUUM_LIMIT_CONDITIONAL
KP: STRONG_GATE_B_TO_KP_CLOSED; NEXT_BLOCKER_SMALL_FIELD_SURVIVAL
```

```text
q  = 0.23178189475262734
4q = 0.9271275790105094   closes on the strong blocked L=2 eta=4 lane
6q = 1.390691368515764    blocks fine-lattice spatial eta=6
8q = 1.8542551580210187   blocks generic 4D eta=8
```

`YMSmallFieldSurvivalAuthority` now splits the next gate into three in-repo
structural inputs, six imported analytic theorem slots, and one native
spatial-orbit slot.  Spatial-only blocking
compatibility, temporal-transfer compatibility, and polymer-activity
preservation are derived from the strong sector/KP stack.  The remaining
small-field blockers are `BalabanSmallFieldRegionStability`,
`BalabanFluctuationCovarianceBound`,
`BalabanPolymerActivityExponentialDecay`, `BalabanScaleUniformConstants`,
`GaugeFixingJacobianBound`, and `GaugeOrbitVolumeUniform`; the
`SpatialBlockingPreservesGaugeOrbit` slot is native/derived. Clay/YM promotion
remains false.

The downstream authority lane is decomposed rather than opaque:
`YMLatticeMassGapAuthority` now exposes four transfer/spectral-gap theorem
slots, `YMThermodynamicLimitAuthority` exposes five volume/continuum theorem
slots, `YMOSAxiomsAuthority` exposes five OS axiom theorem slots, and
`YMContinuumMassGapTransferAuthority` exposes four continuum spectral-transfer
slots.  These slots are the current authority lane; they are not internal
analytic proofs.

The immediate UV tranche is to prove or falsify:

```text
FormalOscillationSeminormForGaugeLinks
FormalQhpBlockingMapDefinition
BalabanCMP98AveragingLocalityImported
QhpPerLinkInfluenceConeLMinus2k
BalabanCMP98LocalOscillationBoundForQhp
LipschitzToSquaredOscillationForQhp
AnisotropicAssumptionA
SquaredOscillationSummabilityForHalfPlaneBlocking
```

The immediate KP tranche is to prove or falsify:

```text
EffectiveActionPolymersSpatialOnlyForA1
PolymerDefinedOnBlockedLattice
KPEntropyAtBlockedScaleL2
```

All later Balaban, small-field, lattice, continuum, OS/Wightman, and Clay
endpoint obligations remain open.

Weak-coupling bookkeeping correction for `2026-06-13`: the repo now has a
typed fail-closed polymer convergence package for the Paper 3 YM lane:

```text
YMLatticeAnimalCountingBoundReceipt
-> YMWeakCouplingRatioBoundReceipt
-> YMGeometricTailHalfBoundReceipt
-> YMPolymerWeakCouplingSumBoundReceipt
-> YMP7WeakCouplingPolymerConvergenceReceipt
```

This package records the `d=4` lattice-animal count surface `N_n <= (8e)^n`,
the tuned weak-coupling ratio surface `a = c_K / (4 g^2)`, the corrected
same-prime `p=7` threshold `c_K >= (4/3) log(24e)`, the geometric-tail
`<= 1/2` surface, the grouped origin-containing weighted polymer sum surface,
and the bridge back into the same-prime `p=7` Wilson activity lane. The repo
now uses that package to close the exact lane-local `p=7` local KP theorem
surface, then records lane-local strict absorption, uniform-volume KP, and
Balaban RG transfer as true in their owning receipts. It still does not prove
continuum Yang-Mills, mass gap, or Clay Yang-Mills.

Audit boundary: finite carrier spectral gaps, finite transfer-matrix gaps,
carrier string-tension diagnostics, and finite strong-coupling estimates are
evidence only.  They are not the Clay Yang-Mills theorem.  A Clay-level result
still requires a continuum Yang-Mills construction, Osterwalder-Schrader
axioms for the continuum gauge theory, reflection positivity at the right
continuum/infinite-volume object, an infinite-volume limit, and operator or
Hamiltonian convergence identifying a positive physical mass gap.  None of
those Clay-level obligations is proved in the current repository.

KP/RG/atom receipt boundary: `KPCouplingObstruction`,
`BruhatTitsBraidKPReduction`, and `AtomExtendedCarrierFrame` are governance
receipts, not Clay progress.  `KPCouplingObstruction` corrects the physical
`p=7` threshold to `beta_min ~= 10.13`, so the physical Wilson beta route fails
unless a separate RG bridge is supplied.  `BruhatTitsBraidKPReduction` may keep
the carrier RG beta branch conditionally passable under carrier hypotheses, but
that is not physical beta running, continuum tightness, OS/Wightman
reconstruction, or a mass-gap theorem.  `AtomExtendedCarrierFrame` is blocked by
an explicit `A > 0` positivity obligation before it can be consumed as analytic
input.

Spectral tower tranche boundary: the current tower distinguishes five
authority levels.  A0 is diagnostic/prose, A1 is finite diagonal
spectralizable evidence, A2 is a typed theorem target, A3 is calibrated
subclass decidability, and A4 is runtime/semantic/continuum/Clay promotion.
The PNF residual finite diagonal spectral severity receipt is A1 only: its
proof is spectralizable finite diagonal evidence, not runtime behavior or
semantic truth.  `SpectralTowerTheoremTarget` is A2, not theorem closure.  NS
FRACTRAN admissibility is A3 only for the Kolmogorov-calibrated subclass.  No
A4 continuum, Clay, runtime-semantic, or terminal claim is promoted here.
`YMContinuumGapFromCarrierConditionalReceipt` and
`YMFourStepsConditionalReceipt` record the Gate-3 reduction and four analytic
steps as conditional ledgers.  They do not construct self-adjoint continuum
YM, strict Mourre positivity, QFT ground-state uniqueness, weak spectral
measure survival, or a Clay mass gap.

Corrected math boundary: no current roadmap step may say that a gap
strengthens to `3.0`.  Where the CM/infinite-depth spectral comparison is
discussed, the honest Selberg-style lower-bound target is
`lambda1 >= 3/16`, still below Clay promotion.  Gate 3 remains the hard lift
from the carrier dictionary to `S'`, Chern-character compatibility, and the
real norm theorem.  K-theory/Bott language is a framing target only, not a
proof.  The PNF spectral-severity surface is finite diagonal evidence, and
any PNF-to-Z7 arrow remains open/lossy.  The two Clay reductions are
conditional ledgers only.

Spectral/Mosco receipt boundary: the new spectral receipt set must be read as
route organization and finite evidence, not as a continuum operator theorem.
For Gate 3, the blocking bridge is not merely "more spectral data."  It has
three named obligations: Mosco upper/density control for the selected carrier
core, a no-spectral-pollution theorem through the cutoff/depth limiting
process, and a mass-shell bridge that identifies the limiting operator
spectrum with the physical gauge-invariant mass surface.  Until all three are
proved, finite carrier spectral gaps, PNF spectral severity, and tower targets
cannot be promoted to L7/L8/L9, Wightman reconstruction, or Clay Yang-Mills.

NS two-phase diagnostic boundary: the current two-phase trace is empirical
diagnostic evidence only.  It falsifies the combined `Q_log` lane2+lane7
reading.  Scalar EV5 Lyapunov is rejected as the live criterion.  The current
candidate is vector-valued EV5, with lane7 read only as the dissipation
witness and lane2 read only as the bounded migration witness.  Those witnesses
are not an actual-flow Navier-Stokes transfer theorem, not a Serrin/BKM
estimate, not smooth regularity, and not Clay NS.  They may motivate future
projection and comparison tests, but they cannot discharge any YM Gate 3 or NS
Clay obligation.

Wave-pool/Gate3 boundary: the caisson/standing-wave picture is now recorded
only as a proof-search dictionary.  `CarrierMoscoConvergenceFromPhysicsReceipt`
keeps Mosco as a strong-resolvent/density route, not norm-resolvent
convergence.  `GreensFunctionConvergenceRateReceipt` records the finite
caisson convergence heuristic and the NS critical-index boundary, but leaves
the analytic bound open.  `CarrierPhaseStructureReceipt` records that YM can
quotient gauge phase in the physical Hilbert-space reading while NS cannot
treat high-prime phase loss as gauge.  These receipts explain why Gate 3 may
be easier for YM than NS; they do not prove Gate 3, OS/Wightman
reconstruction, or a Clay mass gap.

Codec atom / phase boundary: `CanonicalCodecAtomReceipt` records the common
codec form as coarse field plus sparse signed anisotropic atoms plus an MDL
residual budget.  This is a useful bridge because it identifies random-phase
residual synthesis as the implementation-level symptom of the same phase loss
that Gate 3 must control.  The receipt keeps the atom phase, orientation,
anisotropy, and twist fields visible, but it does not implement the runtime
codec, prove MDL matching pursuit, prove phase-aware decode stability, prove
Gate 3 density, or promote any NS/YM/Clay result.

Carrier phase/Gribov/BT-tree boundary: carrier gauge fixing is a
BT-tree/discrete-resolution statement inside the non-Archimedean carrier.  It
selects canonical representatives only at that finite/discrete carrier
authority.  Singer's continuum obstruction and the continuum Gribov-copy
problem remain open.  The `p=7` amplitude sector has a `Z/7` gap, while the
phase-unit sector is `Z/6`; these are different, incommensurable sectors and
must not be identified, divided through each other, or consumed as a single
phase/gap theorem.  Gate 3 must first prove trivial-sector density and the
continuum lift before any carrier representative, phase quotient, or finite
gap can be consumed by the continuum YM route.

Feshbach-Schur / fiber-gap boundary: the finite carrier fiber gap is only an
ingredient.  It may be used as local spectral evidence, but it does not by
itself establish a gap for the full tensor-product Hamiltonian.  The full
tensor-product route now has an explicit receipt,
`YMFeshbachSchurFiberGapBridgeReceipt`, which keeps promotion false until all
of the following are supplied: Gate 3 density of the selected carrier core in
the target Hilbert space, a Feshbach projection decomposition, invertibility
and lower control of the Schur complement on the complement, off-diagonal
relative bounds, and domain/core compatibility for the tensor Hamiltonian.
The existing `FiniteCarrierSpectralGapZ7Receipt` product-spectrum calculation
is therefore read as finite Cartesian-product evidence only, not as a physical
tensor-product Yang-Mills gap.

Balaban/RG induction gap: the preferred carrier-side YM attack is now the
KP/Balaban route.  This is not "Clay YM" as a solved claim.  It is the
concrete KP/uniform-volume obligation needed for a Balaban-style induction
step:

`H_k -> H_{k+1}` with Kotecky-Preiss polymer local-sum constants, small-field
bounds, large-field tail bounds, counterterm control, and block-averaging
error terms all uniform in lattice volume and stable under cutoff/depth
removal.

The repository now records this obligation explicitly in the Balaban,
polymer/KP, and carrier area-law receipts.  It is not proved or imported, and
`exactDecorrelation` must remain open unless supplied by a separate proof.
The naive 15-prime KP series fails; the admissible proof candidate must first
use a single-prime overlap reduction and then rebuild the KP local-sum bounds
from that reduced overlap surface.  The corrected reduction is only an
overlap-set statement: polymer activity is not multiplicative for
disjoint-prime polymers.  The cross term produced by the overlap split must
be bounded or recorded as an explicit obstruction before any KP/Balaban
local-sum estimate consumes the reduction.
Finite MDL/Fejer descent, finite strong-coupling bounds, and finite polymer
bookkeeping are only support surfaces.  The large/small field split is also
open: the ultrametric small-field sector is the carrier ball controlled by
existing finite estimates, while the large-field sector still needs a
tail-suppression estimate strong enough to feed the volume-independent RG
induction.

Braid boundary: there is no braiding inside one BT tree.  A product of
distinct commuting prime lanes is abelian bookkeeping, not a nonabelian braid
theorem.  Same-prime braid/Yang-Baxter remains an open target and cannot be
used as a proved input to the YM roadmap.

The current tower names the blockers through receipts such as
`ClayMillenniumClosureTargetReceipt`, `CarrierFactorVecInjectivityOSPositivity`,
`RGOperatorNormReceipt`, `RGBanachFixedPointReceipt`,
`OSPositivityFromRGFixedPoint`, `ScalarOSTransferMatrixReceipt`, and
`ClayBlockerUpdateReceipt`. `GribovFreeCarrierReceipt` is also available as a
carrier-only canonical-representative receipt: it consumes the concrete
`FactorVec` identity quotient, records uniqueness of the selected
representative in that identity fiber, and points at the existing
`factorVecQCoordinate` / p2-Lorentz coordinate-law primitives. It is not a
continuum Gribov theorem and it does not assert a smooth global gauge-fixing
slice. Newer finite-lattice receipts add a Wilson carrier lattice,
strong-coupling expansion, carrier string-tension estimate, finite
transfer-matrix gap, and an L2 status receipt. Those receipts give a blocker
map. The roadmap below decomposes the blocker into lemmas.

## Corrected Competitive Path

Historical broad roadmap context: the current competitive route is not "finite carrier pressure is below the
canonical dimension, therefore Yang-Mills has a mass gap."  In particular,
the local fact recorded by the pressure-below-15 surfaces,
`pressureBound = 14`, `canonicalDim = 15`, and `14 < 15`, is only a bounded
carrier diagnostic.  It is not a continuum spectral theorem and it cannot be
consumed as a Clay mass-gap proof.

Any credible DASHI-facing Clay YM path has to solve three hard problems as
mathematical theorems, in this dependency shape:

```text
H1 Balaban volume-independent induction
  -> H2 BRST reflection positivity
  -> H3 operator-valued spectral gap
  -> Clay YM existence and mass gap
```

After Sprint 79, the immediate H1 subproblem is narrower: prove the residual
KP graph is blocked-spatial, not fine-lattice spatial. `H1` still means a
genuine volume-independent constructive RG/cluster induction,
not a fixed finite-depth contraction receipt.  It must supply bounds uniform
enough for infinite volume and cutoff removal.

`H2` means reflection positivity for the gauge-fixed/BRST-compatible
continuum object, with the unphysical degrees of freedom controlled so that
OS/Wightman reconstruction is applicable to the physical sector.  Finite
Wilson reflection positivity or scalar-sector transfer positivity does not
discharge this step.

`H3` means a positive lower bound for the physical, operator-valued continuum
Hamiltonian or transfer generator, stable under the limiting process and
identified with the reconstructed gauge-invariant spectrum.  A scalar
inequality, finite carrier eigenvalue, transfer-matrix gap at fixed lattice
scope, or `14 < 15` pressure diagnostic is not this theorem.

The old `L1-L9` lemma map below remains useful as a decomposition of
existence and mass-gap obligations.  The governance rule is that no L7-L9
promotion may be recorded unless the H1/H2/H3 chain is explicitly discharged
or replaced by an equally strong theorem with the same continuum, positivity,
and operator-spectrum content.

## Dependency Graph

```text
L1 lattice YM measure
  -> L2 uniform correlator bounds
  -> L3 tightness of cutoff measures
  -> L4 continuum weak limit
  -> L5 OS axioms for the gauge theory
  -> L6 OS/Wightman reconstruction

L1, L2, L5
  -> L7 uniform transfer-matrix spectral gap
  -> L8 gap survives the continuum limit
  -> L9 physical mass gap in the reconstructed QFT
```

The existence block is `L1-L6`. The mass-gap block is `L7-L9`. A Clay-level
result requires both blocks.

## Lemma Status

| Lemma | Required mathematical content | Current carrier status | Existing receipt surface | Gap |
|---|---|---|---|---|
| L1 | Construct a lattice Yang-Mills measure at each cutoff/lattice spacing for compact gauge group `G`. | Partial target only. The carrier has finite FactorVec/RG scaffolding and finite gauge candidates, but no selected continuum YM gauge measure. | `CarrierRenormalizationGroupScaleReceipt`, `RGContractionReceipt`, `FactorVecAverageVsSumReceipt`, `RGOperatorNormFormalProof` | Need a genuine lattice YM action/measure tied to a carrier-derived compact gauge group. |
| L2 | Prove uniform cutoff-independent bounds on Schwinger/correlation functions, including reflection positivity and exponential decay where needed. | Partially inhabited only in the finite carrier strong-coupling regime. A corrected two-plaquette strong-coupling bound, carrier string tension `sigma ~= 5.27`, exponential plaquette decay at `beta = alpha1`, and a finite lattice gap are recorded as finite evidence only. | `StrongCouplingExpansionReceipt`, `UniformBoundStrongCouplingReceipt`, `StringTensionCarrierReceipt`, `LatticeMassGapFromTransferMatrixReceipt`, `YML2StatusReceipt`, `PolymerKPAsMDLReceipt`, `CarrierAreaLawBalabanSeedReceipt` | Need the KP/uniform-volume polymer obligation: volume-independent local-sum constants, small-field bounds, large-field tail bounds, counterterm control, continuum beta running, tightness as depth/cutoff is removed, dimensionful scale anchoring, infinite-volume control, and gap survival. |
| L3 | Prove tightness/compactness of the cutoff measure family as the cutoff is removed. | Uninhabited. RG contraction and Banach fixed-point receipts are finite/conditional and do not give continuum measure tightness. | `RGBanachFixedPointReceipt`, `OSPositivityFromRGFixedPoint`, `ClayBlockerUpdateReceipt` | Need compactness in the continuum constructive-QFT topology. |
| L4 | Extract a weak continuum limit and prove the limit is nontrivial. | Uninhabited. Continuum RG convergence is named open. | `ContinuumClayMassGapReceiptObligation`, `ClayBlockerUpdateReceipt` | Need interacting continuum YM, not just finite carrier limits or scalar transfer positivity. |
| L5 | Prove the continuum limit satisfies OS axioms: OS positivity, Euclidean covariance, symmetry, clustering, and regularity. | Partially inhabited only for finite scalar and finite ungauge-fixed Wilson-loop carrier inputs. The OS3 boundary is now explicit: ungauge-fixed Wilson positivity is finite-lattice evidence; BRST/Faddeev-Popov gauge fixing is not a positive-Hilbert OS3 proof because of the indefinite/Krein sector; ghost time reflection requires a graded sign/involution; carrier Gribov-free wording is only a representative choice, not a continuum Gribov-copy theorem. Full gauge OS, continuum reflection positivity, covariance, and infinite-volume OS control remain open. | `ScalarOSTransferMatrixReceipt`, `OSAxiomsContinuumStatus`, `WightmanReconstructionCandidateReceipt`, `YML5OSAxiomsForGaugeSectorReceipt`, `GribovFreeCarrierReceipt` | Need gauge-sector reflection positivity at the continuum/infinite-volume object, a gauge-invariant or quotient-compatible OS3 construction, ghost/BRST handling that lands in a positive physical Hilbert space, a real continuum Gribov-copy boundary, and restoration of full Euclidean covariance. |
| Gribov carrier guardrail | For any gauge-fixed route, distinguish carrier representative choice from a continuum Gribov-copy theorem. | Inhabited only for the local `FactorVec` identity quotient: the canonical representative is unique in the identity fiber and the coordinate projection primitive is recorded. | `GribovFreeCarrierReceipt`, `GribovResolutionAuthorityReceipt` | Need an accepted continuum theorem for smooth YM connections before making any global gauge-fixing or Gribov-free continuum claim. |
| Phase/BT-tree guardrail | Keep carrier phase fixing, finite amplitude gaps, and continuum gauge fixing in separate sectors. | Inhabited only as non-Archimedean BT-tree/discrete-resolution bookkeeping.  The `p=7` amplitude `Z/7` gap is not the `Z/6` phase-unit sector. | `CarrierPhaseStructureReceipt`, `GribovFreeCarrierReceipt`, `GribovResolutionAuthorityReceipt` | Need Gate 3 trivial-sector density, a continuum lift, and an independent continuum Gribov/Singer resolution before consuming this data in L5-L9. |
| L6 | Apply OS reconstruction to obtain a Hilbert space, fields, and Hamiltonian satisfying Wightman axioms. | Uninhabited. Reconstruction is a target/citation boundary only. | `ClayMillenniumClosureTargetReceipt`, `WightmanReconstructionCandidateReceipt` | Need L5 first, plus authority binding for all reconstruction hypotheses. |
| L7 | Prove the transfer matrix has a positive spectral gap uniformly in cutoff. | Uninhabited. Finite candidate gaps and selected finite PSD diagnostics do not give a uniform gauge gap. | `H0OSPositivityBaseCase`, `H0ExplicitMatrixReceipt`, `NormalisedH0OSPositivity`, `BalabanRGMassGapReceiptSurface` | Need a depth/cutoff-independent lower bound for the physical gauge Hamiltonian. |
| L8 | Prove the spectral gap survives the continuum limit. | Uninhabited. Requires L3/L4 and L7. Finite carrier gaps are evidence only. | `ColimitGapLiftOnHamiltonian`, `ContinuumClayMassGapReceiptObligation` | Need semicontinuity or a stronger operator/Hamiltonian convergence theorem for the infinite-volume continuum Hamiltonians. |
| L9 | Identify the limiting spectral gap with the physical Yang-Mills mass gap. | Uninhabited. The physical Hamiltonian/gauge group identification remains open. | `YangMillsMassGapBoundary`, `ClayMillenniumClosureTargetReceipt`, `Paper8UnificationBlockerMap` | Need a reconstructed physical Hilbert space and gauge-invariant one-particle/mass spectrum. |

## Feshbach-Schur Fiber-Gap Route

The admissible finite-to-full-gap route is now:

1. Record a carrier fiber spectral gap as evidence.  This is currently
   available for selected finite carriers, including the Z/7 cycle receipt and
   its finite product-spectrum caveat.
2. Prove Gate 3 density for the selected carrier core inside the target
   Hilbert space.  The current `Gate3NormDictionary` reaches a finite
   limit-71 inequality surface, but density remains false.
3. Supply the Feshbach-Schur operator hypotheses: projection decomposition,
   Schur complement invertibility, off-diagonal relative bounds, and domain
   compatibility for the full tensor Hamiltonian.
4. Only after those hypotheses can a tensor-product spectral lower bound be
   stated.  The current repository has no such bound and no Clay promotion.

This route is deliberately narrower than a Clay claim.  It is a local bridge
obligation for turning finite fiber evidence into a candidate operator theorem;
it still sits below L7/L8/L9 and below the continuum construction and
authority requirements.

## Current Honest Position

Update after the second roadmap-execution tranche: YM L1 is inhabited only at
finite carrier-lattice scope, and YM L2 is now partially inhabited only in a
finite strong-coupling scope. The tower has receipts for a three-site carrier
spatial lattice, depth as Euclidean time, a Wilson action with spatial and
spatial-temporal plaquettes, finite-lattice Wilson reflection positivity, a
strong-coupling plaquette expansion, a corrected connected two-plaquette
bound in the strong phase, a carrier string-tension estimate `sigma ~= 5.27`,
and a finite transfer-matrix gap.

This is not continuum Yang-Mills. The strong-coupling result is at carrier
`beta = alpha1` and records exponential decay in carrier units; it does not
construct the beta-to-infinity Wilson continuum trajectory, a dimensionful
physical mass scale, a Wightman theory, or Clay mass-gap promotion.

The carrier still does not have continuum beta running, continuum tightness,
continuum OS axioms, continuum reflection positivity, a BRST gauge-fixed
positive-Hilbert OS3 construction, a ghost time-reflection graded-sign theorem,
a continuum Gribov-copy resolution, an infinite-volume limit, Wightman
reconstruction, operator/Hamiltonian convergence, a weak-coupling/continuum
uniform correlator theorem, or a uniform continuum spectral gap.

The next admissible YM tranche should not aim vaguely at "Clay YM." It should
target the H1/L2-to-L3 interface: prove or refute a Balaban-style
volume-independent induction with constants independent of carrier depth and
volume, then isolate the BRST reflection-positivity and operator-valued
spectral-gap hypotheses required before any continuum limit can be consumed
as Clay evidence.

More concretely, the target is the KP/uniform-volume induction obligation:
prove the Kotecky-Preiss polymer bound with constants independent of the
spatial volume, prove the corrected single-prime overlap-set reduction and
its cross-term bound, prove `exactDecorrelation` if that route consumes it, prove an
ultrametric large/small field split with the large-field tail suppressed
uniformly enough for `H_k -> H_{k+1}`, and show that the resulting counterterm
and block-averaging errors remain controlled through cutoff/depth removal.
This would be a competitive Yang-Mills contribution if proved; it is currently
only an open obligation.

Phase 2 update: `StrongCouplingExpansionReceipt`,
`StringTensionCarrierReceipt`, `UniformBoundStrongCouplingReceipt`,
`BetaCriticalReceipt`, `CarrierRGTrajectoryYMReceipt`, and
`YML2StatusReceipt` record a partial L2 result only in the finite
strong-coupling regime `beta=alpha1`.  This gives a carrier-unit
string-tension/area-law diagnostic and exponential plaquette-correlator decay,
but it is not the Wilson continuum trajectory because fixed `alpha1` is not
`beta -> infinity`.  `Phase2ProgrammeReceipt` therefore treats the next YM
work as continuum beta-running, tightness, scale anchoring, and gap-survival
work, not as Clay closure.

Corrected coupling update: `CarrierScaleFromHeegnerReceipt`,
`QCDRunningFromCarrierScaleReceipt`,
`CarrierGaugeCouplingFromCSLevelReceipt`,
`WilsonBetaFromCSLevelReceipt`, `YML2CorrectedStatusReceipt`, and
`YML3TightnessFromKRunningReceipt` separate `alpha1` from the Wilson beta
and record a CS-level candidate: `alpha_s=1/3`, `beta_SU2=3/pi`, finite
string tension `2.125`, and a `2.33 GeV` mass-gap diagnostic.  The candidate
L3 family is `{mu_k}` as `k -> infinity`; tightness, continuum weak limit,
Wightman reconstruction, and Clay Yang-Mills remain open.

The same Phase 2 programme also records the CS-level gauge-coupling frontier:
`SMGaugeGroupFromCS3LanesReceipt`, `LevelRankDecouplingReceipt`, and
`WBosonMassFromCSReceipt` give candidate gauge-factor origins and expose the
SU(2)-SU(3) level-rank decoupling and W-mass RG/scale-matching blockers.  This
is Gate 6/Gate 7 gauge-coupling context for the YM programme, not a proof of
direct-product gauge independence, physical coupling normalisation, exact
Standard Model reconstruction, or a Yang-Mills mass gap.

## Promotion Boundary

The following must remain false until all nine lemmas and the required
authority boundaries are discharged:

- Clay Yang-Mills mass-gap promotion
- Wightman reconstruction promotion
- full gauge-sector OS positivity
- continuum reflection positivity and infinite-volume OS limit
- continuum Gribov-free/global gauge-fixing promotion from the carrier
  representative receipt
- consuming BT-tree/discrete carrier gauge fixing as a continuum Gribov or
  Singer theorem
- identifying the `p=7` amplitude `Z/7` gap with the phase-unit `Z/6` sector
- consuming carrier phase quotients, carrier representatives, or finite gaps
  before Gate 3 proves trivial-sector density and the continuum lift
- continuum interacting Yang-Mills construction
- operator/Hamiltonian convergence from finite carriers to the continuum
- Balaban volume-independent induction for the continuum constructive route
- KP/uniform-volume Balaban induction
- single-prime overlap-set reduction and its cross-term bound for any KP proof
  after the failed naive 15-prime series
- `exactDecorrelation` as a consumed KP/Balaban input
- ultrametric large/small field split with large-field tail suppression
- same-prime braid/Yang-Baxter theorem, or any nonabelian braid claim from one
  BT tree or from distinct commuting prime lanes
- BRST-compatible reflection positivity for the physical gauge sector
- an operator-valued physical spectral-gap theorem
- any inference of the form "`14 < 15`; therefore Yang-Mills mass gap"
- treating finite/strong-coupling carrier YM as continuum Clay YM
- terminal/unification promotion


### Max-cut 2026-11-01: native side-four rational-SU2 Wilson/C3 source carrier

Four new concrete source-aligned Agda owners are now linked from `BalabanRGTOERegression` (full audit in `Docs/physics/YMClayVoyagerCrossDomainSymmetryMaxCut20261101.md`): literal side-four C3 shifts/forward-bond path, group-valued loop naturality, `RationalUnitQuaternion` exact SU2 trace cyclicity/class-function invariance, and the `PeriodicBlock n=3` ↔ `Site4` bond graph pointwise codec. The positive-directed source signed-word holonomy and graph Wilson normalized real trace are same-object by finite induction, not merely two matching diagrams. Old `BalabanP33CMP109PeriodicPathHolonomyBridgeExact` independently verifies a signed-word/occurrence convention; it is imported as prior owner, not re-proved.

The exact remaining selected physical cuts are **inverse-edge extension**, **full closed plaquette action and C3 reindexing** on actual finite complete SU2/SU(N) group values, **product/constrained Haar change of variables**, actual **selected R443 finite action/Gibbs density**, **R445 preferred physical measure tail/convergence** and **R320/R333 same-H_OS spectral/UV–IR limit**. The existing R443→R431→normalized→continuum chain is already theorem-code; don't ask for another abstract facade. Rational unit quaternions need compact completion/Haar source and continuity, not categorical arithmetic promotion.

**Trust:** all new Agda is SOURCE-WRITTEN (not exact-head kernel-verified); no CI run.


### 2026-11-01 finite signed/native R443 symmetry closure

`YMClayNativeRationalSU2AllSignedC3WilsonExact.agda` closes the finite native
rational SU2 n=3 / side-four C3 graph-word transport for **both** positive
and inverse oriented links, using the actual existing path-holonomy/adjacency
operators. `YMClayNativeRationalSU2OrderedPlaquetteC3ActionExact.agda`
then proves a four-axis-site and 4×4 **ordered** oriented Wilson plaquette
real-trace sum is C3 invariant, via rational exact finite reindexing.
This is genuine finite selected group-valued Wilson algebra, independent
of a jFine/Monster analogy.

Source-next exact leaves in ranked order:
1. **R443-six**: prove the 16 ordered plaquette sum reduces to exactly the
   source six `μ<ν` action with sign/inverse trace equality, diagonal
   constant and physical beta-normalisation; selected SU2 group values.
2. **R443-Haar**: literal 4D C3 configuration action preserves actual compact
   group product/constrained Haar integral (not merely rational point samples).
3. **R443-W/R445-T**: actual source physical Wilson/Gibbs action/density and
   preferred full measure/family attached to this same carrier with uniform
   bounded-observable tails; feed existing R443/R431/OS3 compiler.
4. **R320/R333**: real selected decay, OS Hilbert Hamiltonian and uniform
   positive gap after continuum/infinite-volume.
No Clay promotion. Exact-head Agda compilation remains outstanding.


The native six-positive-plane geometry and actual `Native.rationalSU2PlaquetteHolonomy`
are now directly reused by `YMClayNativeRationalSU2SixPlaneSameSourceExact`.
It proves source six-plane `Bond.plaquetteBoundaryDirections` equals our signed
ordered path, and source native group value/real trace equals the 16-term
subfamily on those exact 6 planes. The actual `sixPlanePhysicalTraceAction`
is thereby on the original named six-plane carrier. Independent exact Fraction
positive-six-plane sums remain -1108/25 before and after C3 on the tested
fixture, and its ordered action satisfies 2×six + 4×256 = 23384/25.

The *general Agda* six-vs-ordered identity (reverse orientation + diagonal +
2× multiplicity), full source action couplings, actual compact Haar, same
R443/R445 selected finite measure, and continuum R320/R333 remain genuine
open physical-source obligations. This six-plane file is source-written only.


The native norm-one rational SU2 four-factor reverse Wilson trace is now
source-written exactly in `YMClayNativeRationalSU2FourFactorReversalExact`,
reusing `Q.inverseProduct`, `Q.inverseInverse` on the original group
and `realPart(inv q)=realPart q`. The remaining six-plane cut narrows to
the **physical oriented contour evaluation/reindexing** and universal
16ordered↔6positive multiplicity and coupling norm; generic 4factor
group reversal itself no longer needs an arbitrary external assumption.

The literal native SU2 n=3 bond field <-> dependent positive-edge graph map now has **both** pointwise roundtrip theorems including arbitrary selected graph fields; no function extensionality nor off-carrier topology was used. Source-written, not kernel-verified.


### 2026-11-01 decisive max-cut recut — original six-plane C3 and native universe

**New actual-source lemmas on PR #1444 (source-written, Agda exact-head not run):**
1. Lower the *original* `RationalSU2BondData n` from an unnecessarily lifted `Set₁` to `Set`, consistent with its fields and with existing `RationalWilsonObservable n : Set` / physical finite `Configuration : Set`. This is a required typed bridge; check all importers on compilation.
2. `YMClayNativeSixPlaneC3SourceReductionExact.nativeSixC3Summed` reduces the **original six positive planes** to two concrete reversed orientations (21 and 31).
3. `YMClayNativeSixPlaneC3ActualPhysicalSourceExact.nativeSixPositiveWilsonActionSpatialC3` uses **existing** `pathHolonomyReverseOpposite` + `periodicPlaquetteClosure` and native trace inverse to pay both orientation cases and assert universally quantified native finite six-plane Wilson C3 invariance. No novel source axiom.
4. `YMClayR443NativeSixPlaneHaarNumeratorExact.nativeSixPlaneNumeratorC3Invariant` passes this same six-plane native finite action into the pre-existing R443 Gibbs/Haar and R431 numerator compilers, retaining only selected physical **Gibbs-density identification** and **compact product/constrained Haar C3 change-of-variables** as hypotheses.
5. `YMClayR443NativeSixPlaneC3SequenceLimitExact` compiles actual cutoff-indexed R431 numerator → normalized finite expectation → selected scalar-limit C3 invariance with **the same n=3 native configuration**; this does not manufacture a 4D continuum, which requires scale/refinement identification.
6. `YMClayR445NativeSU2R443SameObjectExact` proves definitional R443/R445 configuration identity, real native Wilson observable embedding and specializes the existing native P2 finite cylinder expectation convergence conditional on genuine preferred physical measure data.

**Re-ranked exact remaining mathematical max-cut, not to be conflated with the above:**
- **K0 compiler**: Agda exact-head kernel acceptance of native universe change and all 1 Nov modules/transitive safe imports; no claim until run.
- **R443-Haar**: an actual compact SU2/SUN product/constrained Haar C3 change-of-variables theorem, plus the **same finite Wilson/Gibbs physical measure/density**, coupling normalisation and full real-group identification. The rational quaternion finite source theorem is only a rational subcarrier; genuine compact SU2 Haar lives on its real completion.
- **R443-lattice**: selected UV-varying physical lattice, restriction/projection compatibility and actual original CMP119 nonlinear generated action: fixed n=3 finite side-four expectation sequences are not a continuum regularisation.
- **R445-T**: uniform-in-cutoff/volume physical bounded-observable tail and moment/coercivity-tightness estimates, selected limiting measure, plus continuum Wilson observable compatibility; R444 supplies moments only subject to its source hypotheses, not the tails.
- **R320-H1**: same original selected J-family marked second derivative exponential/rooted-shell estimate with volume/scale uniform constants, not the easy finite quaternion trace bound.
- **R333-H3/P3**: selected R281 physical decay spectrum equals the H2 OS reconstructed Hamiltonian, OS positivity/reflection, mass-gap lower bound independent of volume/lattice spacing, and infinite-volume/UV nontriviality. Claiming these from symmetry would be a Clay problem breakthrough not proved by the code.

**No Clay promotion.** Universal 16ordered↔6 constant relation still not kernel proved but **not needed for the now source-backed six-plane C3 route**.


### 2026-11-01 six-plane / 16-ordered physical Wilson normalization

`YMClayNativeSixPlaneOrderedIdentityExact` now source-writes a universal
same-original-n=3-carrier proof that `orderedTrace16 = 2*sixPositiveTrace+4`
at **every** side-four site: four diagonal `+a,+a,-a,-a` loops are
source-native prefix/reverse-opposite identities, six negative orientations
are the already-proved native inverse-path traces. Consequently the correct
physical Wilson action deficits satisfy
`orderedDeficit16 = 2*sixPositiveDeficit`. `Six.sixPlanePhysicalTraceAction`
is retained for the original six trace, while R443 source action is now
`SixOrdered.sixPhysicalDeficitAction = Σ_6(1−ReTr)`, with a direct finite C3
proof, leaving beta and original CMP119 effective Gibbs counterterms explicitly
unpaid. Independent exact arithmetic 4096 checks passes for the selected
fixture; kernel unverified.

Re-ranked residual: **Agda exact-head**, **actual physical R443 product/constrained
compact Haar and exact CMP119 finite Wilson Gibbs density with UV-varying source
family**, **R445 bounded tail/uniform volume tightness and physical continuum
expectations**, **R320 physical CMP116 marked-J source derivative decay**, and
**R333 same OS H2/H3 Hamiltonian, nontriviality and uniform physical gap**.
No other finite plane-counting or new C3/369 formalism is the mass-gap max-cut.


New exact native same-object owner `nativeR443SixDeficitR445Observable` proves the six-source Gibbs Wilson deficit is a R445 rational-observable *function* on the original `RationalSU2BondData 3`. It is not yet proved a physically bounded R445 input, and even such boundedness would not by itself imply convergent selected Gibbs expectations or a uniform physical continuum limit. **Next exact numerical lemma:** finite six-plane deficit majorant (at fixed side-four, ≤3072) from existing single plaquette trace bound and additive finite fold; then connect selected real/cutoff/volume weight and measure tail separately. Existing `NativeP2.nativeWilsonP2Limits` already handles products of individual loops under its actual measure hypotheses.


**Physical-carrier caution:** the exact native `RationalSU2BondData 3` record also stores an arbitrary `siteGauge` function. Its type equality across R443/R445 is genuine, but physical link-Haar requires an explicit pushforward/integration of this redundant gauge coordinate or direct link-only compact SU2/SUN configuration correspondence. The Wilson observable is gauge-field independent, the arbitrary physical integration field is not proven equivalent. Add **R443-linkHaar** to the source leaves along with actual compact completion/Haar and physical UV.


### 2026-11-02 source-first max-cut: selected CMP119 Gibbs numerator already owned

A new primary source readback audit `Docs/physics/YMClaySourceOwnerReuseAndProofGate20261102.md` establishes that `CMP119WilsonGibbsFiniteMeasureSameObjectExact` and `CMP119SelectedWilsonGibbsAnchorExact` **already construct** the source-selected CMP119 metric-insertion N/Z/DN/DZ Wilson–Gibbs finite numerator same-object theorem under their stated selected beta-driven density anchor and Wilson insertion. Do not duplicate these compilers. The next concrete leaf is the correct source proof that the chosen R443 actual compact SU2/SUN link-only Haar Gibbs configurations and varying cutoff family instantiate *those* original CMP119/R124 owners; the native side-four rational C3 module alone cannot pay that.

Likewise, pre-existing R445 selected marked moment and preferred diagonal producer structures do not imply the actual continuum tail, and R320 selected marked second source derivative and R333 same OS H3 Hamiltonian remain real theorem-bearing hypotheses, not syntactic construction tasks. All prior source-written new Agda remains exact-head kernel-unverified. Keep the max-cut list in the 2026-11-02 audit authoritative.


### Revived Yang–Mills audit / R443–R445–R320–R333 exact owner cut (2026-11-02)

The bounded source audit and exact remaining fields are recorded in [YMClaySUNMatrixR443R445R320R333MaxCut20261102](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md#2026-11-02-revived-thread-source-audit-executable-max-cut-and-non-promotion). The fixed rational SU(2) six-plane C3 deficit proof and conditional Haar numerator remain valid separately from the **selected** CMP119 N/Z/DN/DZ metric-insertion / R124 beta-flow family. Neither supplies the other's missing physical same-object witness. The concrete compact SU(N) trace/Haar + bond codec, selected Wilson-action and insertion equality, changing-lattice UV/IR estimates, literal selected CMP116 J-pair shell decay, and same-H OS uniform physical gap are **OPEN**. All new Agda source modules stay SOURCE-WRITTEN / NOT KERNEL-CHECKED. Golden source authority remains Agda; do not promote unverified Lean analogy or finite numerical tests. CI intentionally deferred.


### 2 November 2026 — full explicit source/PR search and finite R443 Haar-algebra payment

The prior broad 'Fubini, SU(N), CMP119, CMP116, mixed J, Hamiltonian, spectral gap, Haar, Wilson' search was repaired with indexed-file searches **and PR changed-file archaeology** (especially Agda #1444/#1440/#1049/#996/#967/#1231; Lean #7). See [the current max-cut source inventory](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md#explicit-repo-and-pr-archaeology-and-new-finite-r443-implementation-2026-11-02).

**New source-written, not kernel checked:** `YMClayFiniteProductHaarOrderedAlgebraExact` derives N-link zero/add/scale/nonnegative integration by induction from the existing one-link algebra. `YMClaySUNMatrixProductHaarR443NumeratorExact` constructs the native finite Gibbs integration-law package and passes existing product-permutation C3 and action invariance through the original R443/R431 numerator theorem, without another global Haar or density-equality premise. Both are imported by `DASHI.Unified.BalabanRGTOERegression`.

**Unpaid physical max-cut:** (1) instantiate actual compact-real SU(N) normalized ReTr/N plus measurable selected one-link Haar/Fubini; note the existing `OneLinkProductHaar` type is total on all functions and must not be identified automatically with ordinary Haar; (2) construct the original side-four bond vector/C3 codec and source six-plane spatial action theorem; (3) identify the selected CMP119 R124 beta-flow and metric insertion, not just a fixed Wilson density; (4) provide actual all-n physical continuum measure/tails and cutoff compatibility; (5) selected CMP116 R320 mixed J rooted-shell inequality including physical source applicability; (6) H2/R281 same-H OS uniform spectral gap and nontriviality. Existing Lean PR #7 and Agda CMP116/CMP119 proof compilers must be reused without claiming their conditional hypotheses are paid. CI deferred; Agda kernel NOT RUN; Clay mass gap OPEN.


### 2 November 2026 — critical correction: Lean PR #15 already constructs compact finite Haar

[Exact Lean-PR-15 → golden Agda source map](../physics/YMClayLeanPR15FullPhysicalDonorCrosswalk20261102.md). Direct PR-head file reads recover real mathlib `literalSU2OneLinkHaar`, `literalSU2ProductLinkHaar`, `fourDimensionalNativeLinkHaar`, the exact product-identification theorem, and conditional selected CMP119 `ProbabilityMeasure`, Prokhorov, CMP116 mixed half-rate and OS spectral no-pollution machinery. Prior 'Haar entirely missing in repo' statements are inaccurate: **finite physical SU(2) Haar is source-written in Lean PR #15**. Golden Agda correspondence/selected measurable test class, original 1024-bond C3 codec and source R124 selection remain open. Do not call Lean PR-head theorem files Agda-kernel-accepted or pretend proof-bearing *transport* pays cutoff-uniform physical estimates.

The additional Agda strict-normalizer owners `productIntegralStrictlyPositive` and `nativePhysicalPartitionPositive` prove the finite Wilson–Gibbs partition is strictly positive conditional on the one-link strictly-positive integration law. The one-link source law remains explicit, not postulated in this module. R445 changing-lattice tightness, R320 selected actual CMP116 derivative, and R333 same-H physical continuum uniform gap are still unproved. No CI / kernel execution.

### 2026-11-02 — actual real SU(N) C3 site-Fubini theorem and finite Gibbs probability normalization

Added `YMClaySUNMatrixSpatialC3RealFubiniExact.agda`: instantiates the existing **polymorphic additive-monoid** `BalabanClayGate4FiniteWeightedAdjointFubiniExact.finiteFubini` at native real Wilson site sums. Two interchanges prove original side-four spatial C3 reindexing. This **derives global native real Wilson deficit/action C3 from a pointwise local six-plane C3 lemma**, rather than assuming global symmetry. In the R443/one-link Haar bridge, the former `sixPlaneActionC3` field is eliminated in favour of the strictly narrower `sixPlaneAtC3` original local physical trace equality.

Added exact native `normalizedExpectation` C3 symmetry, unit numerator = partition, and positive-partition + scalar self-division -> probability-normalized expectation of 1. Original R431 and `Finite.numeratorOneIsPartitionFunction` are reused, not replaced. All are source-written and re-exported through `DASHI.Unified.BalabanRGTOERegression`.

**Now highest-alpha finite R443 leaf:** instantiate local SU(N) inverse real-trace/oriented-plane identity (the rational quaternion source already supplies its geometric proof pattern), then construct exact original 1024-bond product-Haar codec and translate mathlib Lean PR #15's actual measurable compact Haar to golden Agda test algebra. This remains entirely separate from R445 continuum physical tightness, R320 selected differentiated CMP116 and R333 same-OS positive mass gap. See the updated physics ledger. No kernel execution/CI; no Clay promotion.

### 2026-11-02 — complete native SU(N) six-plane C3 proof reduction to matrix adjoint real trace

Source-wrote original SU(N) signed plaquette reversed-holonomy theorem with generic `pathHolonomyReverseOpposite`. Then established the full original six-positive-plane pointwise C3 permutation via real additive `sixRealC3Reindex` and exactly two reverse orientations; no new global C3 action assumption remains. `nativeC3BoundaryFromAdjointRealTrace` now constructs the actual R443 local boundary solely from the **matrix adjoint real trace law** and one-link ordered Haar laws. The new owners are `YMClaySUNMatrixNativeInversePlaquetteRealTraceExact` and `YMClaySUNMatrixNativeSixPlaneC3FromInverseTraceExact`. Canonical Balaban TOE imports them.

**Unpaid R443 local scalar leaf:** instantiate concrete complex SU(N) matrices and the **ReTr_N(A†)=ReTr_N(A)** property of the selected normalized real matrix trace. Existing SUNMatrixRealTrace supplies cyclicity, not adjoint. Construct matching actual 1024-bond C3 codec and genuine measurable one-link SU(N) Haar/Fubini under the same source action. The earlier two-plane C3 source fields can be derived from this one matrix theorem; do not reintroduce them. R443 selected CMP119 metric source, R445 variable cutoff, R320 selected CMP116 mixed-J, R333 same-H mass gap/nontriviality remain open. No kernel or CI run.


### 2026-11-03 explicit all-gate archaeology and golden constructive complex trace / local-gauge Haar

The exact source list and new constructors are in [the canonical SU(N) physical cut](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md#2026-11-03-all-six-gate-source-search-constructive-trace--true-local-gauge-haar). Searches include every requested matrix/ReTr/dagger, Haar/Fubini, source E/R/B/V/CMP119, moment/tail/Prokhorov, mixed-J/R318/R320, and H2/OS/R333 spectral term; direct `dashi_lean4` PR #15 source verified genuine compact SU2 Haar translation and conditional moment Prokhorov.

**Paid source-written, not kernel checked**: `YMClayConstructedComplexFiniteAdjointTraceExact` derives `ReTr(A†) = ReTr(A)` for finite complex matrices *on the existing constructive-real carrier* by induction (with normalized trace and exact certified-SUN operator-correspondence adapter). `YMClaySUNProductHaarGaugeFromOneLinkExact` proves actual coordinatewise n-link gauge Haar from only one-link left/right Haar invariance. `YMClaySUNProductHaarNativeGaugeR443Exact` attaches this to the **original native SU(N) gauge action** and same literal finite Wilson/Gibbs R443 → R431 numerator/normalized expectation. Original global Wilson gauge theorem is reused. Physical integration laws were refactored to `nativePhysicalIntegrationLawsFromOneLink` and reused in both gauge and spatial C3 modules. All are imported by `DASHI.Unified.BalabanRGTOERegression`.

**Residual gates:** finite actual `CertifiedSUNMatrixTheory` over constructed complex matrices with ReTr/N and scalar alignment to legacy `ℝ`; selected measurable one-link compact Haar/Fubini and strict positivity; native original 1024-link C3/vector/gauge codec; CMP119 *source-selected* R124 E/R/B/V metric insertion/beta/counterterms (the `CanonicalWilsonGibbsMetricFamilyWeldCompilerExact` already compiles the family from the selected source equality); R445 selected marked moment realization, bounded-observable tail and source compact-containment, variable-cutoff cylinder maps; R320 exact selected J domain/source magnitude and CMP116 rooted-shell envelope; R333 real selected CMP119 H2 OS and spectral no-subgap positive uniform gap/H6. CI deferred. **No kernel acceptance or Clay proof claimed.**


### 2026-11-03 — repaired bond-field extensionality and native Bishop matrix-trace donor

`YMClaySUNNativeWilsonBondPointwiseExact` and `YMClaySUNVariablePeriodicBondPointwiseExact` prove original actual SU(N) signed paths, positive plaquettes, six-plane actions and Gibbs densities respect **pointwise** bond equality (the latter at every original periodic cutoff), without an unrestricted function-extensionality assumption. `YMClaySUNNativeSetoidBondProductHaarExact` supplies an alternate **setoid** original bond/Vec codec and proves selected-observable C3 product Haar, including the actual native Wilson and Gibbs observables, conditional only on constructing the native codec and one-link Haar law. It does **not** equate arbitrary functions or replace the stronger original two-sided codec. All are imported in the Balaban TOE spine.

Source searches also recovered the concrete vendored Bishop backend and `BishopSetoidComplexExact`. New `YMClayBishopSetoidFiniteAdjointTraceExact` proves finite complex-matrix `ReTr(A†) ≃ ReTr(A)` and normalized analogue by real-setoid congruence, directly on the ACTUAL Bishop source. This cannot be promoted to legacy `RealAnalysisAxioms.ℝ` / Agda propositional equality; `CanonicalDASHIRealBackendExact.LegacyFacadeMigration` explicitly records that pending equivalence/audit. Continue from same-carrier Bishop setoid SU2/complex matrix and selected test-Haar construction; do not reinvent abstract `SUNWilsonAction` or compact-Prokhorov/OS compilers.

See [full gate-ordered ledger](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md#2026-11-03-late-max-cut-original-bond-function-setoid-every-cutoff-vendored-bishop-real-trace). Concrete complex SU(N) unitary/determinant, normalized trace/cyclic laws, actually selected measurable one-link Haar and 1024-bond setoid codec remain physical source obligations. R124 CMP119, R445 estimates, R320 selected-J decay, R333 real same-H gap and nontriviality remain OPEN. Source-written Agda, NOT kernel accepted.


### 2026-11-04 source-selected R445 same-measure pushforward cylinder theorem

The current selected #1444 R445 bridge has two new OWNED source-written lemmas: `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact` constructs the actual original side-four SU(N) finite-Gibbs weighted blocked-cylinder functional and derives positivity, linearity, correct original partition-normalization and selected coarse Wilson/Gibbs gauge laws from existing `PhysicalFiniteMeasureIntegrationLaws`. `YMClayFiniteRGPushforwardNonBareWitnessSafeExact` proves an independent finite fibre-multiplicity no-go to automatic bare coarse uniform weight. Its 64-state Q8-subgroup comparison checked 4,096 gauge transformations and the exact density mismatch in a toy finite model, **not** the physical selected SU(N) Wilson Gibbs law. Full details: [source and exact gate ledger](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md#2026-11-04--r445-original-physical-blocked-cylinder-pushforward-max-cut-source-written-not-kernel-checked).

**Remaining SOURCE→PHYSICAL gap:** show that this selected fine pushforward has a measurable coarse Haar Radon–Nikodym density/effective action, physical normalized disintegration and source-compatible RP cylinder transport, with actual beta(a), tightness/UV/IR uniform estimates and same physical source choice. Do not claim it is another bare Wilson weight; downstream R320 mixed-J, R333 same-H OS strictly positive gap/H6 and full Clay R⁴ remain open. Agda kernel/transitive postulate audit pending. Original 219 field inventory retained.
