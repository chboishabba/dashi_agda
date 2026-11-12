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
