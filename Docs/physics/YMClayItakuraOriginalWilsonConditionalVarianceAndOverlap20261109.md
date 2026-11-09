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


## Stronger new theorem: GAUGE-INVARIANT original beta>=1 random-scan spectral-gap upper bound

The beta-zero example above is **not necessary** to demonstrate volume degeneration. On the **actual interacting beta>=1 original finite SU(2) Wilson law**, fix an original gauge-invariant plaquette trace `X=t(U_p)` and center it: `F=X-E_mu X`. By the original conditional-variance theorem above, `||F||²=Var_mu(X)>0` uniformly at each finite beta, so F is a *genuine nonzero vector of the gauge-invariant vacuum-orthogonal sector*. It depends on exactly four original boundary link variables, for L>=3.

For each original link ell, let `P_ell F=E_mu[F | all links except ell]` be the **actual orthogonal conditional-expectation projector in L²(mu)**. Then:

- If ell is not one of the four boundary links of p, **P_ell F=F**. This is exact conditional-measurability, irrespective of Wilson correlations.
- For any ell, orthogonal projection gives `0<=||F-P_ell F||²<=||F||²`.
- The original Gibbs random-scan one-link heat-bath Markov operator is `K_E=(1/E) sum_ell P_ell`, E=4L^4. It is self-adjoint, positive, preserves constants and commutes with gauge transformations because the Wilson measure and the selected complete link update are gauge covariant. In the invariant sector, its generator `I-K_E` has quadratic form:

```
  <F,(I-K_E)F>
   = (1/E) sum_ell ||F-P_ell F||²
   <= (4/E) ||F||² = (1/L^4)||F||².
```

Since F is **nonzero**, its Rayleigh quotient is at most `1/L^4`. Therefore the bottom of the spectrum of `I-K_E` on the genuine original **nonvacuum gauge-invariant L²(mu)** sector obeys

```
boxed:   inf sigma((I-K_E)|gauge-invariant Omega-perp) <= 1/L^4.
```

As L→infinity this upper bound goes to zero. **Consequently no strictly positive L-independent coercivity constant can hold for UNRESCALED random-scan, one-link-per-step heat-bath dynamics on the original full gauge-invariant Wilson state space.** This is a rigorous original source no-go for every beta>=1, not an artifact of taking beta=0 or choosing a gauge-variant test.

This does NOT refute a physical Yang–Mills mass gap, a **properly rescaled per-sweep block dynamics**, a genuine real-time Hamiltonian or an OS reconstructed H; `K_E` is an algorithmic Markov transition not the E1 same-physical-time semigroup. It *does* forbid directly promoting a finite-size `1/324` random-scan gap or a scale-independent heat-bath coercivity assertion in that unrescaled operator to Clay D2. The chosen physical time normalization and operator identification must be proved.

**Revised highest-alpha D2 source:** rather than trying to prove the false `inf spectrum(I-K_E)>=m>0` uniformly in L for each-link random scan, source-prove a common physical-time autocorrelation decay exponent on a norm-dense E1/OS test family as in `YMClayOriginalOSDenseTestAutocorrelationGapCut20261109.md`, including noncollapsed gauge-invariant continuum vectors and the real E1 reconstruction. If exploring sweep-normalized heat-bath generators, explicitly distinguish `E(I-K_E)` from physical OS H and supply a correct scaling/semigroup comparison theorem. The 4/E variational upper bound on a single plaquette does **not** provide a lower gap for the sweep-normalized generator either.

**Source attribution:** Itakura's exact finite conditional-variance/heat-bath projection machinery (see links above); DASHI's original SU(2) positive plaquette-variance theorem; standard variational spectral bound. The quantitative gauge-invariant all-beta no-go is derived in this DASHI crosswalk and is distinct from Itakura's beta-zero sharp 1/324 proof.


## Donor's more recent ORIGINAL signed-transfer work: AHC → AHD → AHE (2026-11-07 JST)

The authoritative Itakura theorem branch is `formal/real-hilbert-uniform-coercive-strong-limit` (the `main` README is an attribution-bearing historical mirror; do not conflate stale `docs/current_proof_status.md` with the latest theorem checkpoint). His explicit [AHE verified source receipt](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/main/docs/proofs/P4-Q2-PZ37AHE_verified_20261107.md) records **merged PR #6430**, actual source/merge tree `0c978fd763c57fe7c91d9a995732a3d1ee43732b`, stated exact-source Lean CI `11366/11366`, and a named [verified Lean source file](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/048d6b38a577201bb231147c6c4981789c4da5e8/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTrueHaarMidpointSignBudgetV5_PZ37AHE.lean). These are **donor-reported receipts**; DASHI has not rerun the donor's entire Lean build.

The actual reusable AHC→AHD→AHE chain is:
- `AHC`: for FIXED finite H and selected rational-coordinate boundaries, original signed-transfer containing intervals have arbitrarily small width via a common original Borel mesh/Taylor budget.
- `AHD`: original signed transfer `t_H(B)≠0` iff some sufficiently fine genuine signed-Haar rational certificate interval has strictly positive lower or negative upper endpoint.
- `AHE`: exact original cell midpoint/error decomposition and Bool soundness: `lower = sum a_i^- mid_i - sum |a_i^-| err_i`, `upper=sum a_i^+ mid_i + sum |a_i^+| err_i`, preserving signs and true Haar mass intervals.

**The source explicitly does NOT construct a fixed-H original boundary/table with checker=true, so it has NOT proved the actual nonzero signed transfer.** Even that nonzero witness would be distinct from the all-H two-sign shell, physically cutoff-uniform coercivity and the same E1/OS Hamiltonian positive gap. Nor does DASHI's original positive conditional variance magically furnish this fixed-H signed-transfer witness: the functionals are different until an exact same-source identity between Itakura's `t_H(B)` and the selected DASHI conditional/connected observable is established.

**High-alpha possible donor reuse:** construct true finite rational Haar cell intervals and original selected centered Wilson source coefficients, then submit a concrete signed-table witness to AHE; test whether a *same physical source* mapping into DASHI's CMP119 connected-source derivative exists. Retain **both signs and error budgets**. Under no circumstances treat mere interval shrinkage or verified Lean checker soundness as a physical nonzero transfer certificate, uniform spectral gap or interacting continuum. These future mathematical producers are separate from the verified finite D1/N1 crosswalk above.
