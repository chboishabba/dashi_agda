# Original Wilson SU(2) conditional variance, coupling overlap and spectral obstruction — Itakura cross-pollination

**Date:** 2026-11-09. **Source attribution:** Hidetoshi Itakura, [4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap), CC BY 4.0 (copyright 2026), specifically original source [ContinuousCompactOrientedGaugeWilsonConditionalPairVarianceBCF.lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/main/MGAP4D/MathlibAnalytic/ContinuousCompactOrientedGaugeWilsonConditionalPairVarianceBCF.lean), [ContinuousCompactOrientedGaugeWilsonConditionalOverlapCouplingKernel.lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/main/MGAP4D/MathlibAnalytic/ContinuousCompactOrientedGaugeWilsonConditionalOverlapCouplingKernel.lean), [ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicHomogeneousPoincareCoercivityBCF.lean](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/main/MGAP4D/MathlibAnalytic/ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicHomogeneousPoincareCoercivityBCF.lean), and [PHYSICAL_REALIZATION_BOUNDARY.md](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/main/PHYSICAL_REALIZATION_BOUNDARY.md). DASHI's **independently derived** original SU(2) conditional variance lower bound was established in `YMClayOriginalSU2ConditionalVarianceNoncollapse20261109.md`. New in this crosswalk is the exact same-source quantitative *pair-energy* and the original local overlap analysis, with the correct non-uniformity countercheck. No Itakura code has been copied.

## Original measure and a *specific* actual plaquette

Take the true four-dimensional periodic SU(2) Wilson model (side L>=3, E=4L^4 positive links), Haar probability product dH^E, coupling beta>=1, Wilson density proportional to exp(beta sum_{p} t(U_p)), t(U)=ReTr(U)/2. Fix an actual plaquette p and one of its original positive boundary links ell. Condition on all exterior links A=U_{E\{ell}}. The genuine single-link conditional is

```
nu_A(du) = f_A(u) dH(u),
f_A(u) = exp(beta sum_{j=1}^6 t(u V_j(A))) / Z_A,
Z_A = int exp(beta sum_{j=1}^6 t(u V_j(A))) dH(u).
```

This is the original full Gibbs disintegration, not a different independence model. The actual plaquette trace X_A(u)=t(U_p(A,u)) is a real unit quaternion coordinate in some unit direction. Put its conditional mean m_A=int X_A dnu_A and variance v_A=int (X_A-m_A)^2 dnu_A.

## NEW cross-pollinated quantitative one-link **pair-energy**

Itakura's `continuous_compact_oriented_singleLinkConditionalIndependentPairDifferenceEnergyBCF_eq_two_mul_variance` establishes the general, exactly normalized conditional pair-variance identity, while its companion theorem connects the original Gibbs average of this pair energy to the norm-square of the heat-bath fluctuation projection.

Apply it to the **same original** plaquette and its beta-rescaling. For two auxiliary conditionally independent resamples u,v from nu_A (not two independently sampled Wilson lattices), F_A(u)=beta X_A(u), and any fixed exterior A,

```
int int [F_A(u)-F_A(v)]^2 dnu_A(u) dnu_A(v)
       = 2 beta^2 v_A.
```

The original SU(2) quaternion calculation proved in the existing DASHI N1 owner gives, **uniformly over every exterior A**,

```
v_A >= 1/[73728*(1+6 beta)^2].
```

Therefore its original full-Gibbs exterior expectation satisfies

```
E_{A~mu_original} E_{u,v~nu_A}
   [ beta*(X_A(u)-X_A(v)) ]^2
 >= 2 beta^2/[73728*(1+6 beta)^2]
 >= 1/1806336   (beta>=1).
```

Equivalently, the original single-link heat-bath projection defect for the same gauge-invariant elementary plaquette obeys

```
|| (I-P_ell) [beta*(t(U_p)-E_mu t(U_p))] ||^2_{L2(mu)}
 = E_{A~mu_original}[beta^2 v_A]
 >= 1/3612672.
```

The identity of the heat-bath projection defect with the integral of conditional variance follows by the genuine conditional expectation/disintegration, and **only** for the original selected Gibbs measure. For a heat-bath Dirichlet form summed over ALL original links, this one selected ell already contributes at least this much, by nonnegativity of the remaining squared defects.

**What this pays:** a nonzero *original finite-Wilson* L2 conditional fluctuation, with numerical lower bound, meaning the centered beta-scaled original plaquette is demonstrably not invariant under the actual one-link heat bath. This is stronger than merely asserting a positive full Gibbs variance. It does NOT establish a Poincare **lower bound for all vacuum-orthogonal vectors** or any cutoff-uniform physical-time OS covariance exponent. Also it remains a cutoff-scale observable, not a proven fixed-physical-support continuum field.

## Original Wilson conditional-overlap theorem (finite all-beta locality)

Since each of the SIX original plaquette traces in the conditional exponent lies in [-1,1], for beta>=0, every configuration A and u in SU(2) obeys

```
exp(-6 beta) <= exp(beta sum_{j=1}^6 t(u V_j(A)))
            <= exp(6 beta)
exp(-6 beta) <= Z_A <= exp(6 beta)
exp(-12 beta) <= f_A(u) <= exp(12 beta).
```

For ANY two original exterior configurations A,B, the two conditional laws nu_A and nu_B consequently have a common subprobability measure of mass at least exp(-12 beta): their min-density satisfies

```
int min(f_A(u),f_B(u)) dH(u) >= exp(-12 beta).
```

An explicit normalized **maximal-overlap coupling** therefore satisfies

```
Pr(U_A = U_B) >= exp(-12 beta),    TV(nu_A,nu_B) <= 1-exp(-12 beta).
```

This is genuinely original finite Wilson Haar (no invented iid plaquette law), group/volume independent at fixed beta. More sharply, if A and B agree on the 18 external link slots of all six original incident plaquettes, their six staple lists are identical, hence `nu_A=nu_B` and `TV=0` EXACTLY. Thus the original single-link conditional influence is *geometrically local*, and the crude worst-case Dobrushin row sum is at most `18(1-exp(-12 beta))`. That last coarse bound **does not establish a contracting row** at large beta; it tends to 18. This is an honest obstruction to inferring the Clay D1.03 spatial decay directly from universal positive overlap.

**Important distinction:** Itakura's published original one-slab Harnack factors and our six-staple single-link bound use different physical kernels/normalizations. Do not import `exp(8 beta)` or a one-slab transfer bound as if it were exactly our six-staple link Gibbs conditional. The `12 beta` exponent above is derived afresh for this actual conditional.

## Itakura beta=0 random-scan countercheck: 1/324 is finite-volume, not physical-time mass

At beta=0, the original Wilson law is product Haar. On E=4L^4 positive link variables, let P_ell be exact conditional Haar averaging of one link, and K_E=(1/E) sum_ell P_ell. For any nonzero centered f depending only on one original link ell_0,

```
P_ell0 f = 0;   P_ell f=f  (ell != ell0).
K_E f = (1-1/E) f;
(I-K_E) f = (1/E)f.
```

Thus the beta-zero random-scan Poisson operator has an actual nonvacuum eigenvalue `1/(4L^4)`. For L=3, E=324, reproducing the **original finite 1/324** scale appearing in Itakura's [beta-zero random-scan Poisson Lean theorem](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/main/MGAP4D/MathlibAnalytic/ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanSharpPoissonCoercivityL2.lean). This eigenvalue **tends to zero as L→infinity**, so no L-independent lower gap for unrescaled random-scan dynamics can follow from that beta-zero witness. Moreover, even if a separate heat-bath/sweep generator had a suitable bound, it must be proved to reconstruct the SAME physical-time OS Hamiltonian from E1; a random-scan Markov chain is not by definition Euclidean Yang–Mills physical time.

This is a source-specific exact NEGATIVE CONTROL, not a refutation of a physical Clay gap.

## Implications for the original DASHI Clay maximum cut

- **D1-ITK-01 (finite paid analytically):** literal original Wilson six-staple conditional is positive, absolutely continuous w.r.t. product Haar, and admits the exp(-12 beta) overlap/minorization with exact remote-star locality.
- **N1-ITK-01 (finite paid analytically):** original SU(2) local beta-rescaled plaquette conditional pair-energy >=1/1806336 and corresponding true Gibbs heat-bath defect squared >=1/3612672 uniformly in finite L,beta>=1.
- **D1-ITK-02 (OPEN):** original physically BLOCKED/renormalized joint overlap or competing frustrated contour activity with contraction uniform as bare beta(a)→infinity, *including spatially connected bad-polymer geometry*; raw-link Harnack cannot supply this.
- **D2-ITK-01 (OPEN):** connect (if a legitimate source theorem exists) the original physical Wilson OS time transfer and E1 reconstructed H to the actual same Hilbert inner product; no generic heat-bath spectral gap can be swapped for the OS Hamiltonian.
- **E1-CONV-01 (OPEN):** actual interacting physical-support Schwinger convergence/OS axioms, as distinct from finite source coupling.
- **N1-SU2-03 (OPEN):** same-E1 fixed-physical-support renormalized observable, upper moment/tightness and surviving continuum noncollapse; ultraviolet conditional energy alone does not give this.
- **G1.03 (OPEN):** supply genuine all-compact-simple-group continuum E1/D2/N1 witnesses, beyond the finite Haar representation estimates.

**Formalization status:** analytic proof, grounded in the actual original Wilson SU(2) conditional; no Lean4 code imported into Agda, and no native Agda 2.9 kernel receipt. The Itakura source uses CC BY 4.0; attribution must persist if these ideas are formalized, and no incorrect physics promotion is authorized.
