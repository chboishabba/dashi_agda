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



## 13 November: audit correction — original canonical blocked marks already source-written

The earlier P0.E ledger statement that the canonical original physical marked-observable identification remained unimplemented was **too broad**. Original canonical 1024-link blocked-holonomy observables have an existing complete SOURCE-WRITTEN same-Wilson-weight, same-Haar integration, same-normalizer proof chain.

Actual declarations and precise responsibilities:

- YMClayOriginalWilsonCanonicalMarkedReindexExact.originalWeightedMarkedReindexExact: the original native 1024-link adjacent permutation carries an arbitrary marked Wilson integrand without dropping spectator interactions.
- YMClayOriginalWilsonPairSpectatorDecoderExact.sourceSideFourSplitJoin and joinedSplitOriginalExactly: two-sided original 64-pair / 896-spectator vector source codec. Its physical canonical test identification is used by the canonical blocked-mark owner.
- YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.sourceSortedBlockIsOriginalPairs: true decoded coarse vector agrees with original 64 noncommutative link-pair holonomies.
- Same file markedSortedToFlat and markedFlatToActualFinePairs: source count equality, flat-to-nested Fubini and original coupled physical fine weight.
- Same file originalFineCanonicalBlockedNumeratorEqualsPhysicalEffective: canonical original unsorted fine 1024-link numerator agrees with the actual F19 effective-density numerator for EVERY test on the 64 blocked holonomies.
- Same file originalCanonicalBlockedNormalizedEqualsPhysicalEffective: identical FULL normalized canonical fine/effective blocked observable, since originalFinePhysicalPartitionEqualsActualEffectivePartition identifies precisely the SAME original canonical Wilson normalizer.

That closes the **source-authoring** gap for the canonical blocked-HOLONOMY marked-observable identity; this does not supply Agda 2.9 KERNEL acceptance, concrete Haar/Fubini representation, a model for the separately postulated RealAnalysisAxioms real carrier, arbitrary-SU(N) normalized trace, or physical localized Wilson-loop/OS meaning. In particular, physical P0.F uniform effective-minus-bare RG estimate is still completely open.

The authoritative unified regression root DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda is now extended to import YMClayOriginalWilsonCanonicalBlockedMarkF19Exact directly, instead of importing only the unmarked physical F19 partition. The focused checkers already include the decoder, canonical marked, and canonical blocked F19 source modules. No new local Agda kernel receipt.

P0.F finite rational negative control independently reproduced: for the positive fine Z2 character weight K(x,y,z)=(1+t*x*z)(1+t*y*z), integrating the shared interior sign gives rho_eff(x,y)=1+t*t*x*y. Although Zfine=Zeff=Zbare=1 and both one-point means are zero, the cross expectation E_eff[xy]=t*t differs from bare zero. This audit independently executed 4,096/4,096 seeded arbitrary signed marked-observable transports and all eight selected coupling positivity/partition/cross-determinant cases with exact rational arithmetic. This does NOT prove or disprove original 4D SU(N) Wilson P0.F; it proves why correct F19 partition/marks alone cannot establish RG closeness. The original physical comparison must specify running relevant/marginal counterterms and pay cutoff/volume-uniform genuinely summable or decaying errors for F, G, and FG on the SAME selected Wilson family.

Verification boundary: run scripts/check_ym_r445_p0_maxcut_local.sh at the precise PR head, followed by scripts/check_ym_original_rg_p0_kernel.sh. The existing Bishop-partition checker uses --safe only for the constructed Bishop-only root and ordinary typechecking for postulated legacy original Wilson real roots. No physical E1/D1/D2/N1/G1 closure is asserted.


### 13 November: attachment seven-gate "constructively closed" claim rejected on original source

**Controlling exact audit:** `Docs/physics/YMClaySevenGateAttachmentClaimAudit20261113.md`.

The latest #1444 source has already paid even MORE P0.E than an earlier inventory: `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.originalCanonicalBlockedNormalizedEqualsPhysicalEffective` proves full same-source **original canonical 1024-link blocked observable -> original F19 effective-density normalized moment** for arbitrary selected 64-block tests, with original spectator-weighted source and same original Z. Do NOT re-open this as a merely missing independent source carrier. The remaining source-specific marking issue is the selected Wilson **word/loop family and physical derivative/OS identification**, which is distinct from arbitrary 64-block tests.

**Constructive trace audit added:** `YMClaySUNTraceCyclicityDoesNotImplyRangeExact` explicitly constructs the actual source `SUNMatrixRealTrace` record on the certified SUN theory with `Scalar=Nat` and constant two, then proves that an alleged universal unit-range theorem contradicts the native identity element. It complements existing `YMClayOriginalPlaquetteTraceCyclicityInsufficientExact` (real constant trace => allegedly every real is bounded). It is not a physical trace range certificate and does not establish `|Re Tr(U)/N|≤1` for the **genuine** matrix trace: original `CertifiedSUNMatrixTheory` has no indexed entries/diagonal sum to instantiate Cauchy–Schwarz.

**Strong E1 blocker:** strengthened existing `scripts/check_ym_e1_harmonic_regrouping_countermodel.py`; exact finite 131071 step differences `≤2/k`, all dyadic harmonic blocks `≥1/2`, and **convergent `4^j` subsequence identically zero with intermediate `2·4^j` values one**. The latter refutes even a sparse-convergence inference, not the actual Wilson family. One-loop `g0²(a_k)∼1/k` does NOT imply `Σ ε(k)<∞`; the attachment's asserted geometric grouped E1 Cauchy rate has no physical producer.

**All claimed E1/D1/D2/N1/G1 closures still OPEN.** The specific source RG P0.F errors require actual nonconstant tests, UV/volume-uniform physical small/large-field bounds and summable/cancellation scale control, which neither F19 Haar equality nor a perturbative beta coefficient supplies. D1's original activity `m1≥log64+2` is a missing **input**, not a result of rewriting its geometric tail. D2 needs the actual E1 continuum same-H OS core and a common nonvacuum physical-time exponent. N1's four-point coefficient/remainder is unproved for physical nonabelian gauge invariants. G1's dual Coxeter positivity does not build measures/gaps for all groups. The Bałaban #1498 physical Wilson+FP/Haar Ward/one-loop quadrature source remains a parallel 12-gate P0, not a consequence of F19.

**Exact-head verification remains OPEN.** The P0 local referee now includes the source-specific Nat cyclicity negative control and the exact 131071-step sparse-subsequence regression. No Agda 2.9 local receipt, transitive trust audit, positive normalized Borel Haar construction or genuine P0.F physical estimate was established this round.


### 13 November / full Killing-Casimir-reuse, real E1/R445 and N1 witness correction

**Controlling researched source audit**: `Docs/physics/YMClayKillingCasimirGeometricFullReuseAndOriginalE1Weld20261113.md` (31,762 exact #1444 GitHub tree paths reviewed; relevant native definitions fetched). Unlike older gate lists, it explicitly credits:
- `CompactSimpleClassificationAdjointCasimirExact.classificationStrictCasimirCarrier` and `BalabanCompactSimpleUniversalBetaFloorExact.classificationAdjointCasimirAtLeastTwo`, `classificationGroupUniversalCoefficientAtLeastElevenTwelfths`: genuine **all-family** (C_A\ge2), (b_G\ge11/12) rational theorems, NOT to be reproved. `YangMillsCompactSimpleCasimirDynkinTraceExact` pays the finite representation trace/Casimir balance algebra.
- `CompactSimpleBiInvariantRicciReserveExact` and `CompactLieHeatDoobRicciReserveDebtExact`: actual Killing-metric positive Ricci reserve recorded at standard-imported Riemannian boundary; same-metric **physical** heat/Doob and uniform cumulative negative Hessian debt still open. The unrelated `YMKillingBoundarySelfAdjointnessTheoremBoundary` is a different *YM-A boundary flux* lane.
- `BalabanP33PhysicalCombesThomasPromotionExact`/`...SchurExact`: real physical 3072-coordinate SU2 finite CT Schur/tilt algebra with source-dependent stencil, coercivity and bound premises, not continuum mass gap.
- `BalabanContinuumScaleLocalObservableCauchyExact`, `BalabanClayT2UrsellCauchyExact`, `BalabanSharedMarkedAnalyticShellExact`: **the geometric Cauchy/tail proofs and three differentiated mark grades are already present**. The original physical Wilson step-increment/shell activity is still the analytic leaf.
- `YangMillsActualGroupQuantitativeConstructorRound569Exact` / `YangMillsActualGroupFiveBlockConstructorRound570Exact` / `YangMillsActualGroupSourceFirstCompleteRound571Exact`: actual compact-group operations and five-block *alignment* compilers are already written; remaining group-specific **real physical source estimates** include local quantitative group data and each charge-relative test.
- `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.originalCanonicalBlockedNormalizedEqualsPhysicalEffective` remains a PAID same-original 1024-link blocked-observable source equality.

**New original source-positive weld (kernel still pending):** `YMClayE1OriginalR445ThreeMomentCutoffTransportExact`. Its seven proof declarations plus native three-field record identify ACTUAL E1 original n=3 blocked versus n=1 bare Wilson F,G,FG expectation discrepancies with the existing original R445 effective-versus-bare residual. The final `originalE1CovarianceErrorFromThreePhysicalCutoffMoments` invokes original R445 quantitative error telescope on precisely those original E1 physical inputs. Source rewritten rather than arbitrary abstract cutoffs/independent measures; no physical error smallness asserted.

**New N1 source-validity control (kernel still pending):** `YMClayN1GaussianNonlinearFourthCumulantNoGoExact`. Exact rational Gaussian Wick inputs show `κ4(X)=0` but `κ4(X²)=48`: nonzero connected FOURTH cumulant of a **nonlinear Wilson-loop-like observable** cannot by itself distinguish a Gaussian underlying field. N1 needs an actual continuum gauge-invariant generating-functional/non-free witness or an appropriate correctly null Gaussian comparison.

**Independent exact regression:** `scripts/check_ym_source_killing_geometric_n1_20261113.py` (270 finite (4^{-k}) tail identities, 4101 Lie family Casimir sample values, Gaussian 0/48) PASS. The new modules and this script are included in original local-only R445 and original RG kernel-focused referees. No pinned Agda 2.9 available in this execution container; source-written is not kernel accepted.

**Attached proposed physical geometric estimate NOT proved:** a Wilson loop's formal `a_k²/R²=4^-k` cannot be accepted as its actual interacting source scale-step RG bound. The exact `Σ_{k=n}∞4^-k=(4/3)4^-n` also corrects the attachment's `(1/3)4^-n`. Physical `P0.F` scale-local numerator/Haar/covariance estimate, E1/D1, original same-H D2, N1 and all-group G1 remain OPEN. Existing `BalabanClayHighestAlphaRound83SevenAnalyticLemmaExact` is the precise seven physical L1–L7 source cut, with no missing plain Cauchy or (C_A>0) sublemma.
