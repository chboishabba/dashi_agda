# YM D1 exact two-mark signed/physical geometry cut — 17 Nov 2026

## Source and attribution

Existing original owner: `DASHI/Physics/YangMills/BalabanWilsonWEXTMaxCutRound494Exact.agda` whose `WilsonTwoMarkWEXTSource` includes `connectedCovarianceExpansionExact`, source-supported contributing clusters and actual physical rooted-shell tail, with `wilsonTwoMarkExpansionLevel = conditional` and `wilsonConnectingWeightTailLevel = conditional`. `DASHI/Physics/YangMills/BalabanLiteralTwoWilsonCMP116ConnectingTailExact.agda` has `TwoWilsonCMP116PhysicalShellPayment.chargeSumBelowPhysicalRootedShell` as **unpaid field**. `Docs/physics/YMClayOriginalPolymerAnimalReuseMaxCut20261109.md` already identifies P06/R429 original link supports, physical charge and uniform entropy-rate margin. This work adds **no duplicate abstraction** and no ESD edits.

Published theorem donor (attributed): Kotecky and Preiss, *Cluster Expansion for Abstract Polymer Models*, Commun. Math. Phys. **103** (1986), 491–498, https://www.math.ucla.edu/~biskup/290k.1.24w/PDFs/Kotecky-Preiss.pdf ; see also Bissacot, Fernandez, Procacci, *On the Convergence of Cluster Expansions for Polymer Gases*, J. Stat. Phys. 139 (2010), 598–617, https://webspace.science.uu.nl/~ferna107/papers/bisferpro.pdf . Standard abstract KP theorems require proper marked source/dictionary and geometric weighted norm hypotheses for physical decay. Neither establishes original 4D Yang--Mills infrared estimates.

## Exact counterexample to unqualified KP -> Euclidean mass

Take a finite polymer gas with two **incompatible** polymers a,b, same activity z=1/16, and source couplings `z_a(s)=ze^s`, `z_b(t)=ze^t`. Partition `Z(s,t)=1+ze^s+ze^t`; exact mixed logarithmic derivative
`Cov(1_a,1_b)=d_s d_t log Z|_0 = -z²/(1+2z)²=-1/324`.
Choose KP a(a)=a(b)=1, and diameter penalty m=1 with `diam(a)=diam(b)=0`. Closed-neighbourhood KP sum is `2ze=e/8<1`. No statement links abstract incompatibility to physical distance, so place the two incompatible polymers at physical distance 10. The claimed suggested root bound `z exp(1)exp(-10)=exp(-9)/16<3/(16*2^10)<1/324` is **false**. Generalize distance -> infinity to disprove any fixed positive physical decay rate deduced without a geometric locality hypothesis. This is NOT a counterexample to the full marked+geometric KP theorem, nor to YM.

## Exact signed-to-absolute RH cross-pollination

Build `d_s d_t log Z` for literal original Wilson two-mark sources, THEN identify it with the same-source covariance using already present finite mixed-J compiler. The subtraction `E(FG)-E(F)E(G)` removes disconnected components. Keep its sign while performing the original marked cluster expansion; only then apply absolute values to **connecting** coefficients to obtain the physical shell bound. This is structurally analogous to preserving R2 `FarExact` signed instead of prematurely taking its absolute value. Does NOT transfer R2 zeta-zero inequalities into YM.

## Conditional physical rooted transfer theorem

Let `K(x,y)>=0` be the *actual* connecting-step charge majorant on original physical support blocks; `d` a **physical metric** obeying the triangle inequality, `b>1`. If
`sup_x sum_y K(x,y)b^(d(x,y))<=q<1`
uniformly in Wilson UV cutoff and physical volume, and the original literal two-mark connected covariance has a certified domination by a finite mark prefactor times the sum of K-paths, then
`sum_{r>=1} (K^r)(x,y) <= q/(1-q)*b^(-d(x,y))`.
Proof: for any path x=x0,...,xr=y, triangle inequality gives `b^d(x,y)<=product_i b^d(x_{i-1},x_i)`. Weighted row norm is submultiplicative; the r-step sum is <= q^r b^-d; sum geometric. In physical units with fixed block side ell, the exponential rate is `log(b)/ell`.

This is a rigorously proved finite/nonnegative path-matrix **conditional transfer**, NOT an original physical activity proof. The real Wilson connecting expansion may involve hyperedges/branching clusters, requiring an actual anchored cluster/tree transfer into K and a prefactor; do not assert that transformation.

## Local SymPy regression

`scripts/check_ym_d1_signed_kp_geometry_20261117.py` passes exact hard-core mixed-log derivative, negative signed covariance, rational nonlocal KP counterexample, and a 6-block nearest-neighbour path resolvent with K(i,i+1)=1/16, b=2, q=1/4. Exact rational endpoint path sum `16/16451071 <= 1/96`.

## Exact remaining original YM D1 source lemmas (priority)

1. `bWilsonTwoMarkExpansion`: `originalWilsonMarkedClusterLogDerivativeExact`—same R445 Wilson Gibbs measure, original gauge-invariant F,G source exponentials, exact normalization and log/cumulant analyticity, source observable-to-cluster map, connected marks only. Existing R494 conditional interface must be **inhabited**, not copied.
2. `originalWilsonP06R429PhysicalGeometryFaithful`—actual link/block supports, local incompatibility, rooted trace injection, diameter/separation inequality, nonvacuous connecting classes and geometrically weighted connected tree estimate.
3. `originalWilsonSparseFrustratedActivityBelowCanonicalP06Rate`—SOURCE-specific full Wilson small+large field marked activity; quantified per cutoff/volume **strict** entropy margin `C_animal exp(-kappa)<1` in fixed physical units. This is the hard analytic wall, not solved by bare strong-coupling KP.
4. `bWilsonConnectingWeightTail` / `TwoWilsonCMP116PhysicalShellPayment.chargeSumBelowPhysicalRootedShell`—literal physical rooted shell bound with original charge and same-source mark geometry, cutoff/volume uniform; conditional K-path estimate above can serve only after 2+3.
5. `originalFullWilsonSmallPlusLargePhysicalClustering`—combine the true original large-field remainder and small-field CMP116 on the same full Gibbs law, q<1 and physical block length.
6. `sameE1PhysicalCovarianceLimitPreservesClustering`—actual interacting continuum E1 Schwinger family carries D1 bound.
7. `sameE1AllNonvacuumSpectralDetection` then `sameE1FullHamiltonianSpectralExclusion`—D2 on full same OS H, no invisible slow modes.
8. Independent endpoints `originalInteractingNoncollapseCumulant` (N1), `eachGOriginalHaarWilsonAndLocalRG` (G1), and E1 existence remain OPEN.

**Status:** D1/D2/E1 original physical OPEN, expanded portfolio 14/28 resolved, 14/28 OPEN, 0/6 Clay endpoints. No local Agda version is installed in container; only SymPy tests were run. Attribution of KP and original DASHI compilers retained.
