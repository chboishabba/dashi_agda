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
