# YM P0 — authentic original Wilson adjacent F19 two-fibre continuous SU(2) Haar integral

23 November 2026. SOURCE MATHEMATICS LOCALLY VERIFIED; physical CMP119/122 constrained T, original absolute W3, R4 OS and same-H mass gap remain OPEN. Use SymPy locally, not Agda/Lean or GitHub CI.

## Prior art and precise source scope

Reuse existing original 4D Wilson L4 SU(N), 64 R445 F19 pairs / 896 interacting spectators, and unique original 1/F/G/FG from YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact; the original single-pair twelve-staple SU(N) Haar source, SU(N) baryon/centre and exact nonfactorizing Cartan witness in YMClayP0OriginalSUNF19TwelveStapleCenterHaarBaryonAndNonfactorization20261123.md; and the original native 1536-face checker scripts/check_ym_p0_original_wilson_marked_ordered_t_20261123.py. Do NOT rebuild the already-existing CMP119 factorized T/CMP122 Eq171/marked approximation or CMP116/R573/R574/R576/OS compiler records.

Choose TWO genuine adjacent native original F19 pairs at the same time-zero origin, one along y and one along z, with coarse holonomies both I. Hold every other original link at I only as a real original Wilson conditional background, not as a new full interacting lattice measure. Denote the two genuine fine-fibre variables V,W in SU(2), so their first native links are V^-1,W^-1 and second native links V,W.

The authentic full 1,536-face Wilson action has 11 faces touching only V, 11 touching only W, exactly ONE shared original y-z plaquette and 1513 unchanged faces. In normalized trace t(U)=ReTr(U)/2,

S_original(V,W)=11(1-t(V))+11(1-t(W))+(1-t(V^-1 W))
               =23-11t(V)-11t(W)-t(V^-1 W).

This identity was tested by exact original-plaquette evaluation on all 81 pairs of rational (including noncommuting) SU2 unit quaternions; it follows for arbitrary V,W from original face-word geometry. The source's actual fine y-z F deficit is F(V,W)=1-t(V^-1 W). The remote original time-two G deficit is identically zero ONLY ON THIS FIXED-BACKGROUND SLICE. No two-distant-mark connected covariance is derived from this example.

## Exact true SU(2)^2 continuous Haar result, all beta

For SU2 irreducible characters chi_n of dimension n+1, the classical Peter-Weyl expansion and Schur orthogonality give

exp(x t(U)) = sum_(n>=0) a_n(x) chi_n(U),
a_n(x) = 2(n+1) I_(n+1)(x)/x
       = sum_(k>=0) (n+1)(x/2)^(n+2k)/(k!(n+k+1)!).

The x=0 values are taken by continuity. The classical central convolution identity is

int_SU2^2 chi_n(V^-1 W) chi_m(V) chi_l(W) dH(V)dH(W)
= delta_nm delta_nl /(n+1).

Consequently, for any a,b,c>=0, the true compact-group two-fibre source integral is

J(a,b,c) = int_SU2^2 exp[a t(V)+b t(W)+c t(V^-1 W)] dH(V)dH(W)
         = sum_(n>=0) a_n(a) a_n(b) a_n(c)/(n+1),

T_original(beta) = exp(-23 beta) J(11 beta,11 beta,beta).

Every term in the sum is nonnegative for beta>=0, and every term is strictly positive for beta>0. All coupling orders and **both continuous Haar variables** are paid, not sampled via Q8/Z2. The expression does not integrate the remaining 959 interacting original F19 coordinates.

The ORIGINAL once-inserted shared F deficit has exact source marked mass

T_F(beta) = exp(-23 beta)
            [J(11 beta,11 beta,c)-partial_c J(11 beta,11 beta,c)]_(c=beta).

This derivative is taken with respect to the shared face's positive trace exponential, while retaining the full common source denominator. The original G/FG DEFICIT columns vanish for this particular frozen remote-background experiment; they need not vanish in the complete Wilson Gibbs measure.

## Strict interaction: independent factorization is false for every beta>0

The erroneous independent-three-factor expression retains only n=0:

T_naive=exp(-23 beta) a_0(11 beta)^2 a_0(beta).

The genuine original source difference is strictly positive for ALL beta>0:

T_original-T_naive
=exp(-23 beta) sum_(n>=1)a_n(11 beta)^2 a_n(beta)/(n+1)
>0.

The FIRST n=1 character correction has expansion

a_1(11 beta)^2 a_1(beta)/2 = 121 beta^3/16 + O(beta^5).

Thus independent single-pair T masses fail already at order beta^3, not merely on a chosen finite-difference Cartan test. This is a genuine all-beta **nearby shared-plaquette source connected correction**, NOT a termwise absolute CMP116/W3 bound connecting two time-separated original global Wilson marks.

## Rigorous factorial truncation bound at every finite beta

Using |chi_n(U)|<=n+1 and the positive series for modified Bessel functions,

a_n(x) <= (n+1) exp(x),
a_n(x) <= exp(x^2/4) (x/2)^n/n!.

The full original, normalized TWO-fibre Wilson character-series remainder after n=K obeys

0 <= T_original-T_original^[K]
   <= exp(-beta+beta^2/4) sum_(n>K) (n+1)(beta/2)^n/n!.

If x=beta/2 and rho_K=x(K+3)/(K+2)^2<1, the sum is bounded by

[(K+2) x^(K+1)/(K+1)!] / (1-rho_K).

This is a genuine rigorous convergent local source approximation, not a uniform original CMP119 beta(a)->infinity multiscale/source-geometry comparison and not spatial decay.

## Reproducibility and acceptance

Run: python scripts/check_ym_p0_original_adjacent_pair_continuous_su2_character_20261123.py

**340/340 exact assertion groups PASS** locally with SymPy 1.14.0. The script imports the existing full original 1536-face Wilson checker, confirms original face geometry and 81 independent exact rational noncommuting SU2 field pairs, tests the global source F/G marks, computes BOTH unmarked and original F-marked continuous-Haar Taylor coefficients through beta^9 in two independently derived ways (SU2 character series versus exact monomials of independent unit S3 quaternions), tests exact n=1 leading coefficient, strict positive interactions at beta=0.1,0.3,1,3 and rational factorial-tail majorants.

**GitHub file blob 6b9aa41b11c3a39f92114c69315896c1882bdd7a matches the exact locally executed file byte-for-byte.** Agda, Lean and GitHub CI were not run.

## Three requested Clay P0 endpoints: decisive remaining proof leaves

1. **Physical CMP119/122 T still OPEN:** this honest two-fibre original Wilson conditional integral is not Bałaban's physical CMP119 (2.18)-(2.22) admissible Omega/Lambda/S histories with S internal to T, CMP122 Eq.(1.71) constrained gauge-fixed T, nonlinear Q_B average, FP/ghost/Jacobian, E/R/B/V, R-modified residual and running beta(a). The missing proof is a *same-original-source equality or four-column relative bound* for those actual operators, not a new T record.

2. **Original ABSOLUTE W3 still OPEN:** the one shared face, positive character-series correction and exact wall-only all-beta source are insufficient to dominate EVERY connected original two-distant-mark cluster/activity after source localization, large-field/root entropy and all cutoffs. The existing actual W3 compiler R573/R574/R576 requires the unpaid physical source absoluteConnectingWeightSumBelowRootedShell with cutoff-/volume-independent physical positive rate.

3. **Same-H interacting R4 OS gap still OPEN:** the real continuum interacting Wilson/Schwinger OS measure, noncollapsed dense vacuum-orthogonal gauge-invariant core, common reconstructed selfadjoint H, and spectral estimate at physical time t are still absent. The existing YMOriginalD2FullSectorBidiDetection20261121.md source shows decay of a selected observable alone does not imply a gap on the full same-H sector. Source physical -log Q(a)/a, uniform amplitude and observable spectral detection must be paid before the existing gap compilers are invoked.

Attribution: original Wilson action and compact SU2 Haar/Peter-Weyl/Schur/Bessel identities; Bałaban CMP109/116/119/122; original DASHI F19, CMP119, W3 and OS owners. NO Clay solution claimed.
