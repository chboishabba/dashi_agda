# Yang–Mills R443 → R445 → R320 finite same-source Haar blocking max-cut

**Date:** 4 November 2026. **Owner:** [Agda PR #1444](https://github.com/chboishabba/dashi_agda/pull/1444). Do not move into child [#1460](https://github.com/chboishabba/dashi_agda/pull/1460); another worker owns the TSVF/observer/KK/OS unification branch. **Status:** source-written exact Agda proofs, GitHub write/readback; exact-head Agda kernel acceptance **PENDING**. This is a *finite* kinematic Haar and selected-original-Gibbs covariance reduction, not the continuum Clay construction.

## Original owners — no second model or invented RG kernel

- `SUNMatrixCarrier.sunMultiply`: original noncommutative certified SUN multiplication, not scalar or Q8 substitution.
- `YMClayFiniteProductHaarPermutationExact.OneLinkProductHaar`: original normalized one-link functional and integral extensionality/Fubini.
- `YMClayFiniteProductHaarOrderedAlgebraExact.OneLinkOrderedHaarAlgebra`: original one-link linearity, positivity and scalar scaling.
- `YMClaySUNProductHaarGaugeFromOneLinkExact.OneLinkSUNBilateralHaar.oneLeftInvariant`: original Haar translation law.
- `YMClaySUNMatrixProductHaarC3Exact.productIntegralCongruent`: original product integration congruence.
- `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact`: **actual** original 1024-positive-bond side-four SU(N) Wilson-Gibbs selected fine measure and original side-two ordered native two-link block.
- `BalabanFiniteProbabilityPartitionDisintegrationExact`, `BalabanFiniteRGObservableReopeningExact`, `YMClayFiniteRGExistingPushPullReopeningWeldExact`: finite **rational** exact partition/disintegration/transport for a different carrier; NOT silently identified with continuous physical SU(N) Borel Haar.
- `YMClaySUNMatrixR445R320SameCovarianceExact`, `BalabanConnectedCovarianceExpectationLimitRound278Exact`: original selected covariance/continuum **conditional** compilers; the *physical changing-cutoff family and estimates* must still be supplied.

## New exact source reductions

### R445.F13 — original noncommutative Haar pair distribution

File: `DASHI/Physics/YangMills/YMClaySUNHaarDisjointPairBlockingExact.agda`.

Using the **existing** one-link normalized Haar, left invariance and linearity rather than an assumed product-of-blocks law:

```math
\int_{G}dH(U)\int_{G}dH(V)\,F(UV)
  =\int_{G}dH(W)\,F(W).
```

`integrateConstant` comes from `oneScale` + `integrateUnit`, `oneNoncommutativePairPushforward` from `oneLeftInvariant`, `disjointPairHaarPushforward` by *n* coordinate-inductions, and `productIntegralConstant`/`originalUnweightedSpectatorsDisappear` by induction over unobserved independent links. The terminal `originalDisjointPairSpectatorPushforward` proves the exact unweighted law for **any n disjoint ordered non-Abelian pairs and any number of Haar spectators**. It does not assert pair-disjointness of an arbitrary blocked torus: that remains a *separate source-native finite geometry/program proof*.

Physical original selected side-four to side-two geometry consists of **64 coarse positive bonds** (16 sites × 4 directions). Each coarse bond traverses two distinct fine positive links, giving **128 distinct selected fine links**. Exactly **896** of the 1024 fine links are unselected spectators. The original native torus/codec and positive-link path construction have precisely these dimensions and a source-written selected two-block endpoint. The still-unconstructed Agda certificate is the **1024-index original-bond permutation / disjoint pair decomposition** and the exact literal `SUNBlock.nativeSUNBlockLinks` coordinate equality, not a new Haar/disintegration axiom. An independent exact reference enumerates every original 4D coordinate and checks distinctness and periodic endpoint, but is not a kernel proof.

**Important:** The fine Wilson density couples links, so one cannot drop 896 spectator bonds from the *weighted Gibbs law*. The theorem applies to the **unweighted Haar** pushforward of coarse observables. Its physical payoff is a kinematic path for a coarse-Haar reference, not a bare Wilson effective action.

### R445.F14 — actual selected physical finite blocked covariance

File: `DASHI/Physics/YangMills/YMClaySUNR445BlockedPushforwardR320CovarianceExact.agda`.

Instead of introducing a new coarse gauge model, the theorem reuses **the exact same** original fine Gibbs measure, original source-normalized weighted expectation and native blocked map from `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact`. For arbitrary coarse observables F,G, exact definitional equality gives:

```math
\operatorname{Cov}_{B_*\mu_{fine}}(F,G)
 = E_{\mu_{fine}}[(F\circ B)(G\circ B)]
   -E_{\mu_{fine}}[F\circ B]E_{\mu_{fine}}[G\circ B].
```

This is the correct **finite R320 covariance identity**, not a proof that the selected `∂_{J_1} ∂_{J_2} \log Z(J)` exists or that it decays. The physical mixed-source/log-partition differentiation, changing-cutoff and volume-uniform rooted-shell estimate, and spectral OS reconstruction remain separate open R320/R333 producers.

## Independent exact reference (NOT Agda)

`scripts/check_ym_sun_disjoint_pair_haar_pushforward.py` was executed with `fractions.Fraction` on the noncommutative quaternion group Q8:

- 64 arbitrary single-block test functions, exact `E_{U,V}F(UV)=E_WF(W)`, all pass.
- 14 arbitrary **non-factorized** vector observables, disjoint ordered pairs with n=1,2,3 and exact sums over Q8^(2n), all pass.
- Original 4D side-four fine 1024 positive bonds, side-two coarse 64 bonds, disjoint 128 pair-selected fine bonds and 896 spectators, including periodic wrap endpoint, all pass.

Q8 is a finite group *reference*, not the physical continuous compact SU(N) measure. It tests arithmetic/geometry; it does not prove the Agda terms or analytic application.

## Exact remaining Pareto max-cut (fail-closed)

| Priority | Theorem-bearing missing producer | Why F13/F14 do not discharge it |
|---|---|---|
| P0 R443.C3 | One canonical 1024-label adjacent-swap `Product.LinkPermutation` program + closed label vector equality; compact Borel SU(N) Haar on selected test class, selected real/complex matrix backend and physical action | Pair Haar follows **conditional** on existing one-link Haar; the 1024 physical C3 program remains |
| P0 R445 geometry | Construct all-scale `BlockEndpointCompatibility` and source-exact side4 native selected 128-pair+896-spectator finite bond reindex/codec; reflection-compatible block | Q8/native arithmetic reference is not Agda; all-M,L endpoint unproved |
| P0 R445 effective density | From the **actual fine** unweighted product Haar and *actual weighted* Wilson Gibbs density, prove a measurable disintegration/pushforward against the selected coarse Haar with correct conditional fibre integral and effective action/counterterms | Unweighted pair Haar cannot remove coupled Gibbs spectator links |
| P0 R445 estimates | Physical a(n), changing cutoff + volume, positivity and uniform moments/tails, reflection-compatible RG, continuum + thermodynamic limit | All above the fixed-side 4D finite source |
| P0 R320 | Same original Gibbs `∂J_1∂J_2 logZ` analytic source plus CMP116 uniform rooted-shell exponential decay | Exact finite covariance is necessary algebraic grounding, not an analytic decay estimate |
| P0 R333 | Same physical OS reflection-positive continuum Hamiltonian, quantitative positive gap surviving both limits and H6 nontriviality | Covariance and clustering compilers require physical source and strict spectral estimate |
| Clay | Nontrivial four-dimensional gauge theory on R4 and prescribed compact simple gauge-group scope | Millennium problem remains open, no solved claim |
| P01/P07/P02–P11 | TSVF/observer/KK same-object unification on **PR #1460**, not this standalone YM branch | No unification symbols imported into the YM parent |

**Proof trust:** These modules traverse the existing `DASHI.Foundations.RealAnalysisAxioms` postulate boundary; do not mark them transitive zero-postulate Golden or Agda-kernel checked. No `postulate`, `{!!}` or new axiom added in these new files. Existing one-link `OneLinkProductHaar` accepts arbitrary functions rather than a selected measurable/integrable test class; a physically sound continuous compact SU(N) instantiation must refine that analytic scope. F13 and F14 are **source-written reductions**, not unconditional physical theorems.

**Attribution:** Wilson (1974), Bałaban (1985), compact-group Haar and original DASHI source-owner provenance preserved; no transfer of the TSVF/KK worker's results to Clay.
