# YM W0 — original fine Wilson marks are not functions of R445 coarse links (23 Nov 2026)

## Existing owner precedence

Reuse YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact.agda; YMClayOriginalWilsonPhysicalF19PartitionExact.agda; YMClayR445CanonicalBondPermutationCodecExact.agda; YMClayNative1024ClosedReindexHaarConsequencesExact.agda; YMClaySUNWeightedDisjointPairFibreReparamExact.agda; and YMClaySUNOriginal64Pair896MarkedEffectiveSourceExact.agda. The existing previous [full fine-moment audit](YMClayOriginalF19FineWilsonFourCoefficientSourceBIDI20261122.md) explicitly handles all four coefficients and nonzero fibre-connected correlations. Do not reimplement this fibre theorem.

The actual beta-driven CMP119 producers also exist: CMP119AntigravityLiteralPlaquetteBetaDrivenDensityExact.asBetaDrivenCompleteDensityInputs constructs literal plaquette **beta history** but still accepts densityAt and Section 2 conditions as record fields. Balaban1989BetaDrivenFunctionalDensityExact compiles a literal functional density. BalabanCMP119Equation218FactorizedFunctionalDensityExact implements the ordered CMP119 sequences, components, T-step products and residuals but does not extract the original physical indices/operations. BalabanCMP119BackedR108FamilyRound214Exact.asR108Family provides same-action R108 potential from selected localization and action-equality fields, not unconditional physical localization.

## Exact original 4D link/plaquette counterexample

Work on the native 4D periodic side-four Wilson torus, with 4^4×4=1024 original positive fine links, 4^4×6=1536 original positive plaquettes, and 64 side-two blocked oriented links. Take Q8 as an SU(2) **subgroup finite regression**, not as a substitute continuous Haar measure. Start with all fine links I.

At either original selected disjoint y-z fine plaquette position (0,0,0,0) or (0,0,0,2), toggle the selected fine y-link pair (U,V) from (I,I) to (i,-i). Then its exact original native ordered two-link block W=UV remains I, while the first unit Wilson plaquette contains U but not V. Its normalized trace deficit J=1-ReTr(P)/2 therefore changes from zero to one. These two original toggles are independent, and **all 64 coarse links remain identity** for each of the four full original fine configurations.

| Original pair toggles | Fine F | Fine G | Original Wilson deficit over 1536 plaquettes |
| --- | ---: | ---: | ---: |
| none | 0 | 0 | 0 |
| G only | 0 | 1 | 12 |
| F only | 1 | 0 | 12 |
| F and G | 1 | 1 | 24 |

Source checker: [check_ym_w0_fine_mark_not_coarse_measurable_20261123.py](../../scripts/check_ym_w0_fine_mark_not_coarse_measurable_20261123.py). The four rows were independently reproduced using original Q8 plaquette words and the actual original fine block endpoints in the local Python/SymPy environment. The repository checker has been committed but was not byte-for-byte executed locally from GitHub; exact-head pinned Agda and GitHub CI remain unrun.

**No-go:** there cannot exist functions f(W),g(W) of only all 64 R445 coarse links reproducing these two original unit fine-plaquette Wilson marks on all fine fields. The older F19 theorem for **coarse-only** test marks cannot represent these original physical F and G without integrating the fine-fibre dependence.

## Correct existing four-coefficient connection

For the original interacting Wilson fine weight w(P,S), P denotes all 64 pairs and S all 896 **interacting** spectators. At fixed W=UV, existing noncommutative Haar/Fubini reparametrization constructs exact conditional fibre moments K0=integral(w), KF=integral(w F), KG=integral(w G), and KFG=integral(w F G). Thus the correct original global affine effective density is

\[
K(W;s,t)=K_0(W)+sK_F(W)+tK_G(W)+stK_{FG}(W).
\]

When K0>0, f=KF/K0, g=KG/K0, c=KFG/K0-fg, giving the exact identity

\[
K=K_0[(1+sf)(1+tg)+stc].
\]

**Do not set c=0 because the marks are allegedly coarse-measurable.** Nonmeasurability by itself does NOT imply c differs from zero for a particular measure: in this deliberately simple four-point restricted ensemble, weights exp(-12 beta(F+G)) factorize and conditional covariance is zero. An earlier full-interacting fine-Wilson F19 finite slice already found nonzero fibre c; it is the correct positive example. The original total covariance includes both between-coarse mean covariance and average conditional-fibre covariance. Neither may be omitted by a formal factorization.

## Precise source-level W0 max-cut

1. Reuse existing full native 1024-bond permutation/Haar and original **fine-mark** K0/KF/KG/KFG F19 producers (not bare coarse Wilson, not duplicate global marks).
2. Physically instantiate the **same** complete four-column normalized original Wilson source in CMP119 Equation 2.18 admissible domain sequences, Eq. 2.19 component products, Eq. 2.20/2.22 ordered T steps AND sequence residuals, with original E/R/B/V, background, gauge, FP/ghost and Haar Jacobian. Identify the source-generated action and actual Section-2 hypotheses at active physical beta(a); do not merely populate record field types with unrelated values.
3. Then use existing same-source CMP119/122/116/R108 compilers; derive source-localized termwise absolute W3 connecting shells and cutoff/volume-uniform physical SI rate. The earlier nonconstant SU(2) **linearized** wave witness and first-step small-beta q<11/20 remain distinct.

**Authority:** independently locally reproduced finite Q8 counterexample; the committed checker and note are source-only pending literal script readback, pinned Agda and CI. No continuous SU(N) Haar integral, CMP119 physical source inhabitant, nonlinear wave continuum, OS reconstruction or Clay gap solved. Original Wilson/Haar, Bałaban, and DASHI existing source owners remain credited.
