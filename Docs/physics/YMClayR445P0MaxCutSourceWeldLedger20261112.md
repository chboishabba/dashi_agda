# Original Wilson R445 — P0.A–F maximum-cut source-weld ledger (2026-11-12)

**Branch / PR:** `research/ym-voyager2026-completeness-crosswalk-20261101`, PR #1444.

**Source boundary:** The two user-supplied documents are implementation briefs and proposed physical proof chains, **not** local Agda kernel receipts or proofs of their stated physical estimates. Original Wilson SU(N) source and the named real/Haar interfaces remain authoritative. Agda is the golden formalization; CI is not proof admission.

## Source-written finite implementation added in this round

| Owner | Exact declarations / construction | Status |
|---|---|---|
| `YMClayR445OriginalAxialBondParityInjectiveExact.agda` | `originalR445SelectedBondRoundTrip`, `originalR445NativeCoarseBondPairIndicesInjective`, phase disjointness for 64 coarse positive bonds × two axial phases | Existing source-written; now imported into focused regression and local kernel runner |
| `YMClayR445NativePairHolonomyIdentityExact.agda` | `originalR445NativeBlockAgreesPairedCodec`, same native two-step positive Wilson path, not a second block map | Existing source-written; registered for verification |
| `YMClayR445OriginalNativeParityPairWeldExact.agda` | `originalR445NativeOriginIsEvenSite`, `originalR445NativeSecondBondIsParity`, `originalR445NativeBlockAgreesExplicitParity` | Existing source-written; registered for verification |
| `YMClayR445CanonicalBondPermutationCodecExact.agda` | Original selected list (128), source canonical residual list (896), duplicate-free/disjoint/complete proofs, concrete `OriginalR445PairResidualFinite`, canonical and pair/residual `Vec` codecs and inverse round-trip proofs | **New** source-written P0.B; computational length equations and elaboration still require Agda kernel checking |
| `YMClayR445FlatPairedHaarIntegrationExact.agda` | `splitFlattenRoundTrip`, `flatHaarIsPairedResidualHaar`, `flatHaarNativeBlockWithResidualIsCoarseHaar`, literal `sideFourSideTwoFlatHaarBlock` | **New** source-written P0.D on the actual SU(N) one-link Haar carrier, in **flat pair/residual order** |
| `YMClayR445OriginalPureHaarBlockWeldExact.agda` | `originalR445PureHaarBlockedIsOriginalCoarseHaar` follows from an explicit `OriginalR445PermutationAndNativeBlockWeld` record | **New** conditional theorem. The required finite permutation word and native 64-vector order witness are **not inhabited** |
| `YMClayR445OriginalFullWilsonFiberDensityExact.agda` | `originalR445ReconstructedPhysicalFine` using canonical 1024-bond decoder, `originalR445ReconstructedWilsonWeight` using the actual original n=3 Wilson action, `originalR445FullInteractingEffectiveDensity` integrates all 64 relative + 896 interior links, strict positivity and partition positivity, `originalR445AllPairsRecomposeCoarse` | **New** source-written P0.E definition and positivity/recomposition. Equality to canonical original fine-Wilson weighted pushforward **not proved** |

## Independent exact arithmetic/index regressions

- `scripts/check_ym_r445_canonical_bond_codec_exact.py`: all **1024/1024** source-order fine bonds; 64 coarse positive bonds; 128 distinct axial selected indices; 896 distinct residual indices; no overlap; 20 exact field-vector reorder roundtrips. Computed canonical permutation SHA-256 `49b954c21ccd1649208074eb5096e5b6b63102313da773fe17e1268b67727ada`. This is a **Python calculation**, not Agda kernel verification.
- Existing `scripts/check_ym_two_link_haar_fiber_exact.py` and `scripts/check_ym_finite_paired_haar_exact.py`: earlier exact rational finite noncommutative controls (512 and 12 cases), not SU(N) kernel receipts.
- `scripts/check_ym_e1_harmonic_regrouping_countermodel.py`: exact rational bounded non-Cauchy sequence with **131071** checked adjacent differences `|a_(k+1)-a_k|≤2/k`, and alternating dyadic anchors 0,1. The mathematical witness disproves the supplied E1 inference that a bare `O(1/k)` step-error bound can be promoted to a geometric tail just by regrouping.
- Run local authoritative Agda 2.9: `bash scripts/check_ym_r445_p0_maxcut_local.sh`. The full baseline regression includes all new P0.A–E modules via `scripts/check_ym_original_rg_p0_kernel.sh`. **No Agda kernel check was executed in this assistant runtime.**

## Exact remaining finite welds

1. **P0.B kernel receipt and source enumeration proof:** accept `originalR445ResidualCountIs896`, `originalR445PairResidualDistinct`, `originalR445PairResidualComplete`, `originalR445CanonicalReorderRoundTrip` and reverse. These are actual source-written proof terms, not merely numerical checks.
2. **P0.D original permutation word:** construct `originalPermutationWord : Haar.LinkPermutation 1024` together with its source-exact action on canonical encoded bond vectors, `permutationIsOriginalReorder`, instead of postulating arbitrary permutation invariance.
3. **P0.D native coarse vector order:** inhabit `actualNativeBlockIsFlatPairBlock` using `originalR445NativeBlockAgreesExplicitParity` and the concrete `T.cartesian` order of original side-two bonds. Then `originalR445PureHaarBlockedIsOriginalCoarseHaar` needs no remaining finite unknowns beyond the existing one-link Haar/Fubini authority.
4. **P0.E weighted full-density transport:** extend the finite Haar pair/reorder proof to the *actual* coupled Gibbs integrand (arbitrary correlated weight). Prove `originalR445ActualWeightedNumeratorIsConstructedEffectiveNumerator` and `originalR445ActualFinePartitionIsConstructedEffectivePartition` for the same physical n=3 source; show the chosen positive-time/reflection source support if the downstream OS weld uses it.
5. **P0 scalar and trace carrier:** the selected original `RealAnalysisAxioms.ℝ` vs Bishop setoid interpretation is uninhabited, and full arbitrary SU(N) real normalized matrix-trace range remains unproved. Signed Wilson moment transport is source-written only under explicit same-carrier real and trace laws.

## Genuinely unsolved physical producer theorems

| Clay gate | Mathematical leaf still OPEN |
|---|---|
| **P0.F / E1-D1 first physical max-cut** | `originalR445PhysicalEffectiveBareResidualUVUniform`: a genuine original-Wilson nonconstant, scale- and volume-controlled bound on the effective-minus-renormalized-bare density/observables, including the true running coupling and all induced relevant/marginal effective interactions |
| **D1** | `originalConnectedCovarianceRootedShellBound`: construct actual original connected-polymer activities and summable rooted-shell decay with uniform physical constants |
| **E1** | Original changing-cutoff all-cylinder **Cauchy/projective consistency**, reflection positivity and nontrivial interacting limit, with a justified measure/reconstruction theorem |
| **D2** | Same-continuum OS Hilbert space, common positive self-adjoint Hamiltonian and spectral-measure proof excluding continuous and eigenvalue subgap support on the full vacuum-orthogonal space |
| **N1** | Actual nonzero same-limit non-Gaussian connected observable/cumulant with leading-vs-remainder lower bound |
| **G1** | All compact simple groups: source-native carriers and the physical uniform bounds for E1/D1/D2/N1. Positivity of `h^∨` is not sufficient |

### Important countercalculation against the attached “all gates closed” argument

The attachment derives a step rate `g0²(a_k)~1/k` and claims dyadic regrouping produces `2^{-δj}` cylinder increments. The implication is invalid without a further estimate/cancellation. Every dyadic harmonic block obeys

`sum_{k=2^j}^{2^{j+1}-1} 1/k ≥ 2^j/2^{j+1}=1/2`.

Moreover, there is a bounded, explicit rational sequence `a_k∈[0,1]` with `|a_(k+1)-a_k|≤2/k` but alternating values `a_(2^j)=0,1,0,1,...`. Thus even *bounded* observables with `O(1/k)` adjacent changes need not have a limit. No subsequence-regrouping assertion replaces a summable original-source rate or justified cancellation.

The attachment also assumes its massive covariant propagator, polymer activity envelope, original OS same-object identification and four-point nonvanishing remainder control. Those are the **very analytic theorems** outstanding and cannot be promoted by naming their intended conclusions.

**Bottom line:** original native P0.B finite partition and flat P0.D integration are now source-written; P0.E has an explicit full original interacting density and strict positivity. P0.D's final source permutation/native order and P0.E's weighted identification remain welds; P0.F and all five Clay terminal physical gates remain genuinely open. No source-written candidate is called kernel-accepted without a successful local Agda receipt.


## 2026-11-12 later same-source R445 audit — correction of earlier P0.D/E inventory

A later audit of the **authoritative original Wilson regression's actual imports** found that the repository already had stronger F15–F19 and M.01/M.02 source-written constructions than the new, parallel P0.B/D/E helper modules. The earlier wording above ("P0.D original permutation word uninhabited" / "P0.E original weighted equality missing") applies to the **new auxiliary record presentation**, but is NOT a complete description of the older existing source path.

### Pre-existing, more advanced original path

- `YMClayNativeClosedThreeEqualitiesCandidateExact` source-writes the `originalPairSpectatorLengthClosed`, `originalPairSpectatorSelectabilityClosed` and `originalPairSpectatorCanonicalLabelsClosed` actual original-label goals. The two computational values are written using `refl` against the real 1024-bond codec and require actual Agda normalization. **No exact-head kernel receipt.**
- `YMClayNative1024ClosedReindexHaarConsequencesExact` **constructs** `actualPairProgram : Haar.LinkPermutation 1024` and `actualPairSpectatorReindexEveryOriginalVector` for arbitrary original link values, together with original product-Haar invariance. This is the canonical P0.D route, ahead of the newer `OriginalR445PermutationAndNativeBlockWeld` record, which remains uninhabited as that *particular* alternative presentation.
- `YMClayNative1024WeightedWilsonReindexExact` constructs the inverse program and `actualWeightedReindex` for arbitrary weights; `originalWilsonPartitionIsSortedPhysicalPartition` applies it to the true original n=3 interacting Wilson Gibbs action.
- `YMClayNativePairsSpectatorsFubiniExact` proves original full flat=64-pair/896-spectator Haar integration with arbitrary coupled integrands.
- `YMClaySUNWeightedDisjointPairFibreReparamExact` F18/F19 already proves all-pair arbitrary-weight non-Abelian fiber reparametrization, all-spectator integration, effective density and signed/source-marked observable transport.
- `YMClayOriginalWilsonF19ConcreteWeightExact` specializes F19 two-source marked numerators and same-partition normalized values to the original *physically sorted* n=3 Wilson weight.
- `YMClayOriginalWilsonPhysicalF19PartitionExact` already proved `originalFinePhysicalPartitionEqualsNestedF19`. **New direct composed theorem** `originalFinePhysicalPartitionEqualsActualEffectivePartition` reuses that source equality, `originalAllPairsGeneralWeightedChange`, and `originalInterleavedIntegralIsCoarseFibre` to state that the original canonical 1024-bond interacting Wilson partition equals the original constructed full coarse effective-density Haar integral. It assumes no factorization, independent coarse density or physical RG convergence.

### Further source-written implementation and correction this pass

- Fixed the concrete `Torus.Empty` vs `Data.Empty.⊥` mismatch in `YMClayR445CanonicalBondPermutationCodecExact` using explicit empty eliminators and removed an unjustified `--safe` marker from this unchecked composite module.
- `YMClaySUNTwoLinkHaarEffectiveFiberDensityExact`: new `nativeTwoLinkKernelChangeOfVariables` (arbitrary (K(U,V,UV))) and `nativeOnePairAllInteriorWeightedChangeOfVariables` (arbitrary coupled signed finite-interior weight). These are **small standalone source lemmas**; the pre-existing F18/F19 path is the preferred all-pair proof owner.
- `YMClayR445OriginalFullWilsonFiberDensityExact`: `originalR445FirstSelectedPairWeightedHaarTransport` and `originalR445FirstSelectedPairPartitionTransport` specialize the source two-link theorem to the original n=3 1024-bond Gibbs action with 1022 other fine links frozen; F18/F19 remains the full all-pair owner.
- `YMClayR445AdjacentHaarPermutationCompilerExact`: generic typed program for original `Haar.LinkPermutation` and its exact execution proof. This is **auxiliary**, not a claim that the canonical permutation is missing from M.01. The deterministic source-order insertion sort takes 41,792 legal adjacent moves (hash `9d75eed2b46c4507c92a699a337413b3bed9d41580c4ac616228f2dad82562cd`), whereas M.01 already constructs a more suitable program subject to kernel acceptance.
- Exact-rational D4 regression: `check_ym_r445_kernel_valued_haar_exact.py` passed 256 signed arbitrary-kernel and 32 signed fully coupled two-interior-link cases; `check_ym_r445_adjacent_schedule_exact.py` passed the 41,792-swap source-order program and 12 independent vector actions. **Neither is an Agda SU(N) or physical receipt.**
- `scripts/check_ym_r445_p0_maxcut_local.sh` now checks the ORIGINAL closed label/sort, original Wilson weighted reindex, F18/F19 owners **first**, followed by auxiliary new modules and the main regression. It runs the exact finite Python controls, then accepts AGDA_BIN, Agda on PATH or the project Nix shell; no CI, Docker, or replacement kernel.

### Updated fail-closed classification

| Owner / gate | Actual current classification |
|---|---|
| P0.A/B/C/D original 1024-bond permutation and Haar reindex | **Source-written actual original witnesses exist in M.01 and parity/codec modules.** Local Agda 2.9 kernel acceptance and exact source-action identification remain unpaid; do not infer completion from `refl` text |
| P0.E full original Wilson partition and arbitrary weighted F19 disintegration | **Source-written full original partition equality and F19 effective density exist**, including new direct same-source composite. The normalized two-marked original-native block observable identification and kernel acceptance must be checked across the exact transitive root |
| P0 scalar and trace | Original Wilson ↔ Bishop setoid scalar `OriginalWilsonToBishopScalarWeld` remains uninhabited; fully selected arbitrary-SU(N) trace bound needs constructive source proof |
| P0.F | **Genuinely open mathematical theorem:** source-derived nonconstant UV/volume-uniform effective-minus-bare Wilson RG bound |
| E1 / D1 / D2 / N1 / G1 | **Genuinely open physical Clay gates**, not completed by source-written finite Haar/disintegration or one-loop beta |

**Trust:** source readback and independently executed finite control checks, NOT pinned Agda kernel acceptance. The live #1498 Bałaban Wilson/ghost/Haar physical integrand and four quadratures are a separate open branch and do not close this R445 physical RG estimate.


### 13 November: constructed *original physical* F19 strict positivity (source-written)

**New original-source proof in `YMClayOriginalWilsonPhysicalF19PartitionExact.agda`**, not an independent effective-density oracle. The module now constructs five declarations, with the **same** side-four SU(N) interacting Wilson/Gibbs weight, the actual native M.01/M.02 1024-bond sorter and the original 64-pair/896-spectator F19 effective density:

1. `originalSortedWilsonPhysicalWeightPointwisePositive`: pointwise `exp(-S_Wilson)>0` from the existing `StrictPositiveRealExponential.expPositive`.
2. `originalPhysical896SpectatorMarginalStrictlyPositive`: integrates **all 896 physically coupled spectator bonds** with the existing source `OneLinkStrictlyPositiveIntegration`, retaining Wilson interactions.
3. `originalFullInteractingEffectiveDensityStrictlyPositive`: strict positivity of the exact original coarse effective density at every native 64-block configuration via F18/F19 original pair-fibre integration.
4. `originalFullInteractingEffectivePartitionStrictlyPositive`: strict positivity of the same effective coarse partition.
5. `originalCanonicalFineWilsonPartitionStrictlyPositiveFromF19`: strict positivity of the original UNSORTED 1024-bond Wilson partition by transporting the previously source-written same-source F19 partition equality.

**Status:** source-written, GitHub readback verified, **local pinned Agda 2.9 kernel OPEN**. These are genuinely original physical finite-object instantiations, though they use the already explicit `OneLinkStrictlyPositiveIntegration` and independently postulated `RealAnalysisAxioms.ℝ` rather than constructing Borel Haar or the scalar carrier. The proof does not supply P0.F effective-vs-bare Wilson contraction, a physical UV/IR uniform bound, continuum E1, decay D1, spectrum D2, N1, G1, or #1498 original Wilson/ghost/Haar perturbative beta integrals.

**Trust/runner repair:** `check_ym_r445_p0_maxcut_local.sh` and `check_ym_original_rg_p0_kernel.sh` now explicitly set `AGDA_BIN` from PATH before calling the original shared runner, preventing an unwanted implicit Nix build; Nix remains a supported fallback. The latter now targets the ORIGINAL M.01/M.02/F18/F19 source before dependent quantitative RG modules. `check_ym_bishop_partition_maxcut_local.sh` separately runs `--safe` on the constructed Bishop-only root, then ordinary typechecking of the original Wilson real-socket modules with their transitive legacy postulate boundary disclosed. Removed misleading `--safe` annotations in `YMClayFiniteProductHaarOrderedAlgebraExact.agda` and `CMP119AntigravityRealGibbsDensityPositiveExact.agda`, both of which import explicitly postulated `RealAnalysisAxioms`. **No local Agda 2.9 receipt obtained in this assistant runtime.**

**Exact next mathematical producer:** prove source-dependent all-volume, UV/IR-uniform smallness of `X(F)` (equivalently three genuine normalized moment differences) for actual nonconstant Wilson tests `F,G,FG` with a scale summability sufficient to compare the effective Gibbs law against the distinct bare coarse Wilson law. The exact F19 partition identity and its strictly positive normalizer do not imply this.


### 13 November P0.E strengthened: actual physical two-source normalizer equals original canonical Z

The same **`YMClayOriginalWilsonPhysicalF19PartitionExact.agda`** now also contains a nested original `OriginalPhysicalF19TwoMarked` module with five exact source-written consumers of the previously implemented `F19Physical.physicalWeight` and `actualF19WilsonTwoMarkTheorem`:

- `originalPhysicalTwoMarkedAtZeroIsOne`: pointwise exact `(1+0·F)(1+0·G)=1` on the actual 64-block test carrier, using existing real ring laws.
- `originalPhysicalF19EffectiveMarkedZeroIsPartition`: the actual source F19 effective two-marked numerator at `s=t=0` is the previously constructed physical 64-block effective partition, using original finite-Haar extensionality.
- `originalPhysicalF19FineMarkedZeroIsCanonicalPartition`: exact **same original canonical unsorted 1024-link** Wilson Gibbs partition equality `Z_aff(0,0) = Z_original fine`, combining the source F19 two-mark theorem with original M.01/M.02/F19 partition transport.
- `originalPhysicalF19FineMarkedNormalizerStrictlyPositive`: the same original source two-marked denominator is strictly positive under the already explicit original strict Haar and exp-positive hypotheses.
- `originalPhysicalF19TwoMarksNormalizeByCanonicalPartition`: the *entire* physical fine/effective two-source generating expression is identical when both are normalized by the original canonical Wilson fine partition, without a second `Z` oracle or physical RG moment identification.

**Scope:** the tests are actual native original F19 coarse-block functions, and the interacting fine weight is the same original SU(N) Wilson Gibbs density. This advances the finite native physical **normalizer and two-source source-identification**, not the distinct remaining marked physical Wilson word/loop observable identification into that carrier, the missing positive division semantic interpretation, or the cutoff-uniform `P0.F` original effective-minus-bare physical moment errors.

**Verification:** all five new declarations are only **SOURCE-WRITTEN / pinned Agda 2.9 kernel OPEN**; in particular `RealAnalysisAxioms` remains an explicitly postulated scalar boundary. No CI result or finite Python witness is used as kernel authority.


## 13 November 2026: P0.F induced two-source interaction negative control

**New source owner:** `DASHI/Physics/YangMills/YMClayP0FGeneratedTwoSourceInteractionNegativeControlExact.agda`. This is an explicitly **finite Z₂-character rational control**, not the original SU(N) Wilson model. The control uses two observed sign characters `x,y` and one **shared** interior sign character `z` with strictly positive fine weight at `t=1/2`:

```text
K(x,y,z) = (1 + t*x*z) * (1 + t*y*z)
rho_eff(x,y) = Haar_z K = 1 + t^2*x*y
```

The source-written Agda module implements literal interior/coarse Haar averages, full fine/effective marked-test equality, positive finite effective density, matching partition functions `Zfine=Zeff=Zbare=1`, vanishing effective/bare single-character moments, and induced `FG` moment/covariance **1/4 vs 0**. It also proves `effectiveCrossDeterminant = 1` and the general independent-character product determinant is zero, rejecting representation as an arbitrary rank-one independent bare density. The same finite toy indexed by a formal cutoff retains its nonzero error: indexing alone cannot generate UV decay. This is **not** a counterexample to a genuine 4D Wilson RG theorem, because its original physical Wilson source and running couplings are absent.

**Independent executed receipt:** `scripts/check_ym_p0f_generated_two_source_interaction.py`, exact `fractions.Fraction` arithmetic, **4,096/4,096** arbitrary signed marked tests for eight strictly positive fine couplings, **8/8** normalized one-point/bare controls and **8/8** nonfactorization/covariance controls. Both focused original Wilson referee and R445 P0 runner now include the new source/check. This is a finite mathematical regression, **not** Agda kernel verification; the full source has no new postulate/hole declarations and does not assert `--safe`.

**What this changes in P0.F:** finite M.01/M.02/F18/F19 disintegration, positivity, equal partitions and even equality of the two selected *first* moments are insufficient to bound the third `FG` error. Genuine Wilson blocking can generate extra gauge-invariant multi-observable interactions; the physical comparison target must explicitly specify running couplings, allowed relevant/marginal operator counterterms, and a uniform remainder norm controlling `X(F)`, `X(G)`, and `X(FG)` on the same original R445/E1 measure family. The old quantitative three-moment compiler already transfers such estimates to covariance, so there is no reason to duplicate that algebra.

**Precise open physical producer:** for the true source `E_eff,n` of the original side-four blocked Wilson state and separately defined renormalized bare coarse `E_bare,n`, prove a source-derived bound `sup_{test in admissible Wilson algebra} |E_eff,n(test)-E_bare,n(test)| <= eps_n` with explicit support dependence, physically justified counterterms, uniform volume constants and a summable/decaying `eps_n`. Prove the actual group/theory-dependent estimate; do not infer it from exact normalization or a toy finite uniform bound. Original constructive scalar/Haar/trace carrier admission and the full E1/D1/D2/N1/G1 endpoints remain OPEN.


## 2026-11-13 additional maximum cut: direct canonical MARKED physical F19 pushforward

### Source-written exact proof producers on PR #1444

- `YMClayOriginalWilsonCanonicalMarkedReindexExact.agda`:
  `inverseProgramTwice` and `forwardAfterInverse` prove both directions for the **actual original** adjacent-swap permutation (not a chosen inverse map);
  `originalWeightedMarkedReindexExact` transports the entire original
  interacting Wilson density times **any sorted-carrier marked observable**;
  `originalCanonicalMarkedNormalizedIsSorted` transports its numerator and
  the original canonical Wilson partition as a **same-Z normalized equality**.
- `YMClayOriginalWilsonPairSpectatorDecoderExact.agda`:
  `splitJoinedOriginalExactly`, `joinedSplitOriginalExactly` and
  `sourceSideFourSplitJoin` establish the actual two-sided vector
  isomorphism for 64 ordered original pairs and 896 retained spectators
  (2×64+896=1,024), with no factorization assumption.
- `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.agda`:
  `sourceSortedBlockIsOriginalPairs` identifies source sorted-pair
  readout with the **same** 64 non-Abelian block holonomies;
  `originalFineCanonicalBlockedNumeratorEqualsPhysicalEffective`
  composes original native marked reindex, count transport, exact source
  Fubini and existing actual F19 weighted disintegration to identify the
  **original unsorted 1,024-link Wilson** marked numerator with its
  genuine physical 64-block effective-density numerator **for arbitrary
  coarse observables**;
  `originalCanonicalBlockedNormalizedEqualsPhysicalEffective`
  composes that with `originalFinePhysicalPartitionEqualsActualEffectivePartition`
  to identify normalized marked expectations using exactly the same
  original Wilson partition, no synthetic coarse partition.
- `YMClayOriginalWilsonEffectiveBetaFiniteDifferenceExact.agda`:
  original partition equality parameterized by the physical Wilson
  coupling `beta` yields `originalCouplingFirstFiniteDifferenceExact`
  and `originalCouplingSecondFiniteDifferenceExact` for *all*
  coupling arguments, no differentiation-under-Haar premise. These are
  **finite Wilson coupling differences**, not Bałaban's physical mixed
  external-momentum tensor two-jet / continuum beta function.
- `YMClayOriginalWilsonPartitionEqualityDoesNotBoundRGExact.agda`:
  an explicit positive two-point finite Haar model has
  `Z_bare=Z_eff=1`, with a persistent density discrepancy `1/2`
  and a persistent **normalized marked moment discrepancy `1/4`**
  for bounded nonconstant F=G=FG, at every cutoff. Thus neither
  the original P0.E source partition equality NOR even same-Z
  normalized observational transport establishes effective-vs-*bare*
  RG closeness P0.F. The model is a logical countercontrol, not a
  surrogate of the genuine 1,024-bond Wilson law.
- No duplicate trace authority was retained: existing
  `YMClayOriginalPlaquetteTraceCyclicityInsufficientExact` already
  proves the accurate original RealAnalysisAxioms scalar trace obstruction.
  Cyclicity alone cannot yield the arbitrary SU(N) unitary trace bound.

### Verification

**All new Agda declarations are SOURCE-WRITTEN and pushed, NOT
kernel-accepted in this session.** The Agda/Nix executable is unavailable
here; no CI was run. Both fail-closed pinned local referees now explicitly
include the new original source theorem roots:
`scripts/check_ym_r445_p0_maxcut_local.sh` and
`scripts/check_ym_original_rg_p0_kernel.sh`.
The independent `scripts/check_ym_original_marked_maxcut_exact.py` uses
exact Fraction arithmetic on a noncommutative S3 five-link example
(2 ordered pairs + a spectator), four marked two-source conditions,
strictly positive fully coupled weights and 7,776 configurations
per side; the independent Python execution produced equal sums
and common positive normalizer. This is **NOT** SU(N) physical integration
nor Agda typechecking.

### Remaining maximum-cut mathematical gates after this source lift

1. **Kernel admission:** Agda 2.9 first-error check, repair, acceptance for
   M.01/M.02/F18/F19 and every new canonical 64-pair marked consumer.
   Source code and Python arithmetic alone are not receipts.
2. **Original scalar:** inhabit the already-written
   `OriginalWilsonToBishopScalarWeld` on the *actual*
   `RealAnalysisAxioms.ℝ` Wilson partition/expectation carrier, with
   faithful operations/order/division/reflectsEquality. Existing
   `YMClayP0BishopRealCarrierInstancesExact` proves Bishop algebra but
   does NOT identify the postulated source real with that carrier.
3. **Arbitrary SU(N) trace:** prove the source original
   matrix normalized-real-trace unitary magnitude ≤1 from a
   genuine finite complex matrix entry/norm and `Tr(I)=N`
   authority, then transport it to original plaquette words.
   Source cyclicity alone is mathematically insufficient.
4. **P0.F:** genuine *same original interacting source* all-volume,
   UV/IR-uniform polymer/RG physical estimate bounding the actual
   normalized F,G,FG covariance/cross numerators; source-bare Wilson
   effective interaction comparison requires a true scale-summable rate,
   not partition equality or a generic F19 change of variables.
5. **E1/D1/D2/N1/G1:** interacting cutoff-continuum consistency,
   original rooted-shell covariance decay, same E1 OS Hamiltonian with
   positive full spectrum gap, nontrivial interacting witness, and all
   required compact simple groups all remain OPEN.
6. **Separate PR #1498:** the perturbative Bałaban mixed-momentum
   Wilson/ghost/Haar scalar, physical Fourier sine/shifted denominator,
   Ward/tensor-to-beta weld, real four integral/Hessian/error certificates
   remain OPEN; original finite Haar blocking does not replace them.
