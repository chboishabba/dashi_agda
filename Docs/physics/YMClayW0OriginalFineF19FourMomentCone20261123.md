# YM P0 W0 — sharp four-moment consistency cone for original SU(N) Wilson/F19 fine marks (23 November 2026)

## Source-first reuse and scope

Prefer existing original constructions: YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact.agda (true original Wilson fine-observable 1/F/G/FG and all 896 interacting spectators), YMClayOriginalWilsonPhysicalF19PartitionExact.agda (canonical 1024-bond partition = actual F19 effective partition), YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.agda (canonical full observable for *coarse* tests), YMClayNative1024FullMarkedWilsonReindexExact.agda (arbitrary original canonical two-mark reindex), YMClayR445CanonicalBondPermutationCodecExact.agda, YMClayNative1024ClosedReindexHaarConsequencesExact.agda and BalabanCMP119Equation218FactorizedFunctionalDensityExact.agda (CMP119 2.18-2.22 conditional finite factorized density). Do not duplicate these producers. The preceding [fine-not-coarse counterexample](YMClayW0OriginalFineMarksNotCoarseMeasurable20261123.md) proves the original selected fine unit plaquette marks cannot in general be functions of the 64 R445 blocks alone.

Original Wilson/Haar measure and positivity are the physical source. The following elementary inequalities are a source-derived **necessary admission filter**, not an equality of the actual Wilson measure with CMP119's T products. This note records mathematical consequences of ordinary positive real Haar integration conditional on its explicitly stated real compact SU(N) interpretation. The Agda record-level one-link Haar, matrix trace and positivity implementations still require exact-head typechecking/transitive authority.

## The source four-coefficient cone

At a fixed coarse W, let dmu_W(V,S) be the original *positive* SU(N) Wilson Boltzmann weight times Haar over the true 64 fine pair fibres V and ALL 896 interacting spectators S. For the original two globally unique fine y-z plaquette deficits,

\[
F=1-\frac1N\operatorname{ReTr}P_F,\qquad
G=1-\frac1N\operatorname{ReTr}P_G,
\quad 0\leq F,G\leq 2
\]

because P_F,P_G are unitary, and |ReTr(U)|<=N. Define exactly the existing F19 moments K0=integral dmu_W, KF=integral F dmu_W, KG=integral G dmu_W, KFG=integral FG dmu_W. All four use the **same** original physical conditional measure and its unchanged normalization; no factorization of the 896 spectators or arbitrary new effective density.

With K0>0, positivity of F, G, 2-F, 2-G, FG, F(2-G), G(2-F), (2-F)(2-G) gives the exact sharp **four-column cone**

\[
0\leq K_F,K_G\leq 2K_0,\qquad
\max(0,2K_F+2K_G-4K_0)\leq K_{FG}
\leq\min(2K_F,2K_G).
\]

Thus a candidate CMP119 same-source marked density that violates these pointwise source constraints cannot equal the original F19 Wilson density. The converse is false: these finite moment inequalities do NOT characterize the original source, even if the candidate's density is positive and normalized.

The pointwise conditional covariance at fixed W is
\[
c(W)=K_{FG}/K_0-(K_F/K_0)(K_G/K_0).
\]
By the Cauchy-Schwarz inequality and Var(X)<= (max X-min X)^2/4=1 for any X in [0,2],
\[
|c(W)|\leq 1.
\]
The interval [-1,1] is *sharp among positive conditional laws*: equal mass at (F,G)=(0,0),(2,2) has c=+1, while equal mass at (0,2),(2,0) has c=-1. These corner laws are abstract sharpness witnesses, NOT claims of attainability of the endpoints under a particular original Wilson density. The previous 15-link full-original-plaquette conditional discrete-slice experiment is the separately grounded nonzero physical-source-geometry c witness; its Q8/SU(2)-centre conditional counting measure likewise is NOT continuous Haar.

The selected original real marked density is
\[
K(W;s,t)=K_0+sK_F+tK_G+stK_{FG}
= \int d\mu_W(V,S)\,(1+sF)(1+tG).
\]
For complex |s|,|t|<=r with r=9/100,
\[
|K(W;s,t)-K_0(W)|
\le (4r+4r^2) K_0(W)=\frac{981}{2500}K_0(W).
\]
Therefore the **uniform finite pointwise nonvanishing lower bound** is
\[
\boxed{|K(W;s,t)|\ge (1519/2500)K_0(W)>0.}
\]
The bound is conservative and independent of number of fibres/spectators or their coupling, as long as F,G retain the original normalized plaquette range. It is a **finite source complex marked-fibre stability** statement; it does not provide uniform original CMP119 physical RG step difference, absolute W3 cluster charge, a nonzero rate in SI units or a continuum theorem.

## Exact executable diagnostics

New [compact SymPy/Fraction checker](../../scripts/check_ym_w0_f19_four_moment_cone_20261123.py) enumerates all 4^4-1=255 nonzero integer-weight four-corner probability laws and verifies all inequalities with rational arithmetic, positive semidefiniteness of the full 2x2 conditional covariance matrix, and |c|<=1. It independently checks sharp c=±1 witnesses and r=9/100 nonvanishing coefficient exactly (1519/2500). A negative control changes KFG while respecting the coefficient cone: the source could be different, so cone membership alone does **not** prove original-Wilson/CMP119 equality.

A matching local exact Fraction/SymPy reference calculation ran and passed all 255 laws. The committed script is source-written/read-back, not independently executed byte-for-byte. No Agda kernel or GitHub CI was run.

## Physical W0 next and non-promotion

1. **Re-use original fine-mark F19 theorem** and canonical original Wilson sorter to get the true positive K0/KF/KG/KFG on the source's concrete original SU(N) measure. Check the candidate physical CMP119 differentiated density against the necessary four-column cone at each selected slow field/coarse W (if the target uses a different reference measure, first construct its correct positive RN transport).
2. **Identify source**, not just bound it: supply real CMP119 (2.18) sequence lists, (2.19) component lists, (2.20)/(2.22) source T operations and residual term, source-selected E/R/B/V/background/gauge/FP/ghost/Jacobian with the SAME actual original marked finite partition, all four coefficients and active beta(a). Reuse existing CMP119 beta-history and Round214/R108 compilers. No record-field dummy inhabitant or duplicate compiler.
3. **Absolute W3:** derive termwise original source-localized bounds on differentiated connected activities, uniform cutoff/volume rooted shell sum and SI rate, and retain fibre c plus between-coarse covariance. The pointwise bound |c|<=1 is NOT spatial decay: summing over arbitrarily many shells is not justified by it.
4. **E1/D1/D2/N1/G1** and nonlinear gauge-equivariant wave-to-OS same-H nonvacuum spectrum remain open; the earlier nonconstant SU(2) Cartan wave is a finite linearized witness only. TOE #1291 six-face/27 signed-neutral states remain index/provenance, not dynamical estimates.

Attribution: original Wilson, Haar, Bałaban CMP109/116/119/122, elementary probability inequalities and the existing DASHI original exact source owners. No new physical Yang-Mills mass-gap theorem.
