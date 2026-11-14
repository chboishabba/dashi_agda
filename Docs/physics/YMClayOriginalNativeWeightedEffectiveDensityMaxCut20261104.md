# Yang–Mills R443/R445 weighted effective-density max-cut (4 Nov 2026)

**Work ownership:** independent YM/Clay [PR #1444](https://github.com/chboishabba/dashi_agda/pull/1444). Other worker retains the independent TSVF/observer/(3,1)/KK P01–P11 [PR #1460](https://github.com/chboishabba/dashi_agda/pull/1460). This dossier describes **new finite proof-source work**. It does not claim that four-dimensional quantum Yang–Mills or the mass gap is solved.

**Trust status:** GitHub-verified Agda sources and independent exact-rational Python executions; **NO exact-head Agda kernel acceptance** (compiler unavailable here), no transitive zero-postulate Golden proof (legacy `RealAnalysisAxioms` is imported by original Haar carriers), no constructed Borel Haar, and no continuum/volume limit. New modules contain no local `postulate` or `{!!}` holes; one F17 missing closing parenthesis was found by static audit and repaired.

## Reused original theorem owners (not duplicated)

`SUNMatrixCarrier` and `YMClaySUNMatrixNativeSignedWilsonExact` supply exactly the original noncommutative SU(N) multiplication, inverse and group laws; `YMClayFiniteProductHaarPermutationExact.OneLinkProductHaar` supplies the selected one-link integral, congruence and Fubini; `YMClaySUNProductHaarGaugeFromOneLinkExact.OneLinkSUNBilateralHaar` supplies Haar translations; `YMClayFiniteProductHaarOrderedAlgebraExact` supplies scalar linearity and strictly positive integration. `YMClayNativePositiveBondEnumerationVectorExact` supplies original 1024-bond encoding; `YMClayNativeSideFourTwoLinkPairSameObjectExact` supplies the pointwise equality of selected weighted-Gibbs block to original ordered two-link path; `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact` owns the **actual selected full Wilson–Gibbs** pushforward functional.

These objects are NOT replaced by a rational Q8 probability model, new coarse density oracle or stand-in lattice.

## R445.F17 — weighted noncommutative Haar *single-pair* disintegration

New `DASHI/Physics/YangMills/YMClaySUNWeightedHaarPairFibreDisintegrationExact.agda` derives directly from the original SU(N) group cancellation, right-Haar invariance, Fubini, one-link linearity and real multiplication commutativity:

\[
\int_{G^2} w(U,V)F(UV)\,dH(U)dH(V)
=\int_G \rho_{\mathrm{eff}}(W)F(W)\,dH(W),
\quad
\rho_{\mathrm{eff}}(W)=\int_G w(WV^{-1},V)\,dH(V).
\]

**Arbitrary nonfactorizing weights** are allowed: this is stronger than F13's unweighted Haar law and does not require a fictitious bare coarse-Wilson action. The original fine and derived coarse partitions agree exactly, and using the **same chosen scalar division**, their normalized expectations agree; the latter alone does not warrant physical positivity without the original integration/real denominator laws.

For pointwise strictly positive fine weight, the selected original `OneLinkStrictlyPositiveIntegration` gives strictly positive effective density.

An independent exact Q8 rational-reference run passed **1,800 weighted pairs**, **1,800 globally coupled spectator-dependent weights**, and a nonbare effective-density control. Q8 is only a noncommutative finite regression group, **not the physical Borel SU(N) group**.

## R445.F18/F19/F22 — arbitrary all-pairs weighted change-of-variables and positive effective density

New `DASHI/Physics/YangMills/YMClaySUNWeightedDisjointPairFibreReparamExact.agda` proves for every finite \(n\), any original joint fine integrand \(g\) (with no factorization across pairs), and the **same ordered original matrix-link multiplication**:

\[
\int\!\prod_{j=1}^{n}dH(U_j)dH(V_j)\,g(\mathbf U,\mathbf V)
=\int\!\prod_{j=1}^{n}dH(W_j)dH(V_j)\,
 g(\mathbf W\mathbf V^{-1},\mathbf V).
\]

This is derived by induction from the original oneLink Fubini and right-invariance, with explicit source proof that the reparametrized original blocked holonomy is exactly \(\mathbf W\).

A further, separately derived one-link↔finite-vector Fubini theorem groups *all* coarse variables before *all* fibre variables. Thus the **explicit derived all-pairs coarse effective density** is

\[
\boxed{\rho_{\mathrm{eff}}(\mathbf W)
=\int_{G^n}\!\prod_{j=1}^{n}dH(V_j)\,
 w(W_1V_1^{-1},V_1,\ldots,W_nV_n^{-1},V_n).}
\]

For arbitrary coupled fine weight and arbitrary coarse cylinder observable \(F\), the original full weighted numerator equals the integral of this coarse density times \(F(\mathbf W)\). The original scalar scale law proves observable extraction; it is **not** an assumed RG compatibility axiom. The source also constructs the strict positivity of \(\rho_{\mathrm{eff}}\) and of its coarse Haar partition **conditional on pointwise positive fine weight and the existing strictly-positive original one-link Haar input** (F22).

The source explicitly specializes to the native side-four → side-two **64 coarse ordered pairs + 896 spectators**, with a completely arbitrary weight coupling the spectators to all selected links: it first integrates spectators in the original product Haar, then integrates the 64 block fibre links at fixed coarse links. No conditional independence of the **weight** is assumed; the product reference Haar is the underlying independent-link measure, as required.

Independent Q8 regression:
- **117** nonfactorizing all-pair change-of-variables fixtures over **1,184,769** enumerated rows, including arbitrary pair couplings, passed.
- **81** nonfactorizing complete effective-coarse-density, same-partition and positivity fixtures for \(n=0,1,2,3\), passed.
- These are arithmetic references; not Agda kernel checks, analytic Haar existence or physical 1024-decoder equality.

## R443.F08 / R445.F20–F21 — real native adjacent-swap program constructors, still finite-kernel-open

- `YMClayFiniteNativeAdjacentWordInverseExact`: constructs a typed original `Fin`-indexed adjacent swap, ordered word interpreter as **original** `Product.LinkPermutation`, source-written two-sided permutation inverse on arbitrary Vec, no new permutation carrier.
- `YMClayNativeC3AdjacentSortProgramExact`: computes a real native original `LinkPermutation 1024` candidate from `C3.forwardVector canonicalLabelVector` and the original 1024 positive-bond labels. The **one closed** `constructedNativeC3CanonicalLabelGoal` remains **unproved in Agda**; on its proof the existing `SingleVectorC3PermutationCertificate` immediately delivers all link-vector C3 equality.
- `YMClayNativeSideFourPairSpectatorSortProgramExact`: builds original 128 selected pair labels from F15/F16 and the original 896 spectator complement using the true native positive-bond decidable equality. Reuses **that same original C3 sorter** to produce an R445 program candidate, conditioned on two **closed Agda checks**: list length = original 1024-count and one exact canonical bond-label vector equality.

Independent original-coordinate Python checks recomputed precisely **46,592 adjacent swaps for C3**, **41,792 adjacent swaps for 64 ordered pairs + 896 spectators**, C3³=id, typed-program orientation, inverse word action, original target digests and wrong-order controls. These do **not** prove the three closed Agda goals.

**Next exact finite identity:** prove the native pair/spectator program's two closed equality goals (prefer a general proof-relevant distinct-label permutation owner over a massive computational `refl`), then use `Product.productHaarPermutationInvariant` and the existing original native decoder to identify F19's **derived weighted effective density** with `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact.actualPushforwardNumerator` **on the actual original 1024 matrix-link Gibbs field**. Construct the separate C3 canonical label equality. Do not mark R445 effective-action density as a proved *physical* result until that same-object integration identification and genuine one-link continuous Haar are established.

## Actual physical max-cut remains

| Gate | Live proof obligation, unchanged by the finite mathematics |
|---|---|
| R443 | Genuine compact SU(N) matrix/real scalar correspondence; Borel Haar and integration of selected Gibbs/cylinder test algebra; exact native C3 canonical-label equality; physical CMP119 action/metric/counterterms |
| R445 | Kernel-accepted original 1024-bond decoder/reindex and all-M,L endpoint; full selected weighted Gibbs pushforward effective-density identification; reflection-compatible block/RG, cutoff and thermodynamic controls, \(a(n)\), uniform tails/moments, physical continuum limit |
| R320 | Same original Wilson/Gibbs marked-\(J\) log partition differentiability and CMP116 rooted-shell decay, with **cutoff/volume-uniform constants** |
| R333 | Selected physical OS reflection positivity, same self-adjoint reconstructed Hamiltonian, a **strict** continuum spectral gap (and calibration), H6 nontriviality and group scope |
| Clay | Nontrivial four-dimensional quantum Yang–Mills construction satisfying the stated axioms for prescribed compact simple gauge groups, including \(\mathbb R^4\) and spectral gap |

**No novelty/ownership confusion:** classical compact Haar, Wilson 1974 and Bałaban constructive RG remain credited; existing DASHI finite product-Haar, native torus/codec, connected-covariance, original R320/CMP116 and R333/OS owners are reused and unchanged. This branch does not modify the TSVF/(3,1)/KK PR #1460 or ESD surfaces.

**Repro/source files:** `scripts/check_ym_weighted_nonabelian_haar_fibre_disintegration.py`, `scripts/check_ym_weighted_disjoint_pairs_fibre_reparam.py`, `scripts/check_ym_all_pair_weighted_effective_density.py`, `scripts/check_ym_native_c3_and_pair_original_sort_program.py`; the existing `scripts/check_ym_native_1024_pair_spectator_reindex.py` and `scripts/check_ym_sun_disjoint_pair_haar_pushforward.py` remain independent reference sources. **No exact-head Agda compiler receipt.**
