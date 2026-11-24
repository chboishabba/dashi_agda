# YM Clay P0 — original Wilson weak-coupling one-exterior-link influence obstruction, actual R445 weighted-coupling donor, and physical good/bad max-cut
24 November 2026 · research on the actual original 4D SU(2) Wilson Haar source. **Clay YangMillsClaySolved = false**: genuine CMP119/122 selected physical T, full original termwise absolute CMP116/W3 at beta(a)→∞, interacting noncollapsed continuum and SAME-H OS gap remain OPEN.

## Live provenance and worker reconciliation (verified 24 Nov)

Default branch is \`master\`, inspected head **c36aa4a423091063bb3741cc74044726279b47c4**. P0 PR **#1536** targets master and is heavily divergent (observed 98 ahead / 70,160 behind at inspection); original physical CMP119 donor PR **#1444** is still open on a different research base, **#1535** native selected-time reflection/positive-half-space PR is **merged** and reusable, **#1503** F19 original source PR is merged. Do not rewrite or cherry-pick bulk divergent material.

The other worker's existing [weighted exterior theorem](YMClayR445WeightedExteriorInfluenceMaxCut20261114.md) and [finite Fraction checker](../../scripts/check_ym_r445_weighted_exterior_influence.py) are **identical files on current master and #1536**, and predate this note. The named Agda files \`DASHI/Physics/YangMills/YMClayR445WeightedExteriorInfluenceFiniteExact.agda\` and \`.../YMClayR445ExteriorKernelTVChainFiniteExact.agda\` are **NOT FOUND at those paths** on live \`master\`, live #1536 or PR #1503 head. Their claimed local completion must remain **UNVERIFIED/POSSIBLY UNPUSHED**; do not call them kernel-accepted or make another copy without acquiring the worker commit. The odd duplicated heading from the pasted edit is absent in the existing GitHub document.

Already established by external and repo donors: original Yang–Mills native SU(N)/gauge/Haar at arbitrary L; true F19 64 blocked pairs and 896 spectators on L4; anchored tree gauge Haar; source affine 1/F/G/FG; original high-beta SU(N) Weyl-cap plaquette deficit and local excess; original SU(N) sparse frustrated-plaquette chessboard [YMClayOriginalSUNSparseFrustratedContourChessboardPhysicalW3Cut20261123.md](YMClayOriginalSUNSparseFrustratedContourChessboardPhysicalW3Cut20261123.md); original CMP116/CMP119/122 RG sources with physical T/Q_B/E/R/B/V uninhabited; original OS same-H dense-core bridge. No new general finite coupling or FP record needed.

## 1. Source-specific high-beta theorem: a single exterior positive-link change has TV → 1

On the **original** periodic \`L=4\` four-dimensional SU(2) Wilson source, use all 256 sites, 1024 native positive links, 1536 native positive plaquettes and full action \`S=Σ_p(1−ReTr P_p/2)\`. Fix \`ell=((0,0,0,0),mu=0)\`. Exactly SIX original native plaquettes contain \`ell\`, two for each transverse direction \`nu=1,2,3\`. The six opposite positive links \`j_(nu,±)=((0,0,0,0)±e_nu,mu=0)\` are pairwise distinct; each occurs in exactly ONE of ell's six touching plaquettes. Other 1017 exterior link variables (or more generally the rest of the original 1023 outside ell) are fixed as described, not deleted from the Wilson model.

Let \`zeta=e^(2 pi i /5)\` and for \`j=0,…,4\` take the exact SU(2) matrices

    H_j = diag(zeta^j,zeta^(-j)) in SU(2).

These are 5 distinct elements of the continuous group (a finite sample of link values, not a finite replacement of Haar). The exact cyclotomic identity \`1+zeta+zeta²+zeta³+zeta⁴=0\` and its conjugate give \`Σ_(j=0)^4 H_j = 0\` as a 2x2 matrix. Assign the corresponding five unique opposite positive source links \`U_(j_link)=H_j^-1\`, leave the other required exterior links \`I\`, and choose the sixth opposite link equal to \`+I\` or \`−I\` (both actual SU2 centre values). By original *oriented plaquette word* cyclicity and \`ReTr(P^-1)=ReTr(P)\`, the six complete original Wilson plaquette traces conditioned on the selected U_ell become

    {t(U_ell H_0),…,t(U_ell H_4), ±t(U_ell)},

where \`t(V)=ReTr V/2\`. The five contributions cancel **FOR EVERY U_ell IN THE ENTIRE CONTINUOUS SU(2)**:

    Σ_(j=0)^4 t(U_ell H_j)=0,
    Σ_(j=0)^4 [1−t(U_ell H_j)] = 5.

All other 1530 original Wilson plaquette terms are independent of U_ell under the conditional law, though still included as conditioned original energy. Flipping just the SIXTH original exterior link from +I to −I thus produces

    K_β^+(dU_ell) = exp(+β t(U_ell)) / Z_β dH_SU2(U_ell),
    K_β^−(dU_ell) = exp(−β t(U_ell)) / Z_β dH_SU2(U_ell),

with \`Z_β=2 I_1(β)/β\` genuine continuous SU(2) Haar normalization. No Q8, Z2, one-link replacement action or conditional-independence assumption.

## 2. Strict quantitative TV lower bound and link to physical frustrated bad sector

Under normalized SU(2) Haar, \`t(U)\` has density \`(2/pi)sqrt(1−t²)dt\` on [−1,1]. Put

    h = Haar{t>=1/2}=1/3−sqrt(3)/(4pi)>0.

For \`A={t>0}\`, symmetry gives \`K_β^−(A)=K_β^+(A^c)\`. Furthermore

    Z_β >= h exp(β/2),
    K_β^+(t<=0) <= [1/2]/Z_β <= exp(−β/2)/(2h).

Consequently, for all β≥0,

    TV(K_β^+,K_β^−) >= max(0,1−exp(−β/2)/h),
    TV(K_β^+,K_β^−) → 1 as β→∞.

In particular the explicit lower bound at **β=16** is **0.9982840883675882**. Therefore the sup over all *one exterior coordinate* changes of the actual bare continuous-SU2 native one-link conditional kernel tends to one. **Any proposed strictly subunit high-beta UNIFORM worst-case row Dobrushin coefficient for the bare native one-link specification is false.** This says NOTHING against a different true CMP119 renormalized localized target: its conditional kernel has not been source-identified or proved to inherit the same influence.

The source witness belongs exactly to the repo's preexisting *near-minimizing frustrated bad plaquette* sector: since the five real original plaquette deficits sum to five for EVERY U_ell, at least one original plaquette incident to ell satisfies \`d_p≥1\` with probability **one** conditioned on this exterior. This is not simply high local energy-excess; indeed the five link-dependent energies cancel, and the overall conditional energy depends on the sixth only. The exact equality persists with source boundary configuration; nearby boundary configurations have nonzero Haar neighborhoods and nearly frustrated deficit. **No assumption that this rare exterior has a uniform positive Gibbs mass** is made. The existing original SU(N) high-beta fixed-contour chessboard estimates are relevant donors to bound probability of bad *collections*, but their quantitative charged cut must be attached to the source-selected T and two globally marked insertions. A pointwise all-exterior contraction is not the appropriate physical endpoint.

## 3. How to use the other worker's weighted coupling result without circularity

The already-present generic finite theorem for selected local X and exterior Y asserts for any coupling \`π\` of the SAME-source exterior marginals:

    TV(P_X,Q_X) ≤ A_X + E_π[TV(K_Q(.|Y), K_Q(.|Y'))],
    A_X=E_(P_Y) TV(K_P(.|Y),K_Q(.|Y)).

A coordinate telescope bounds its last term by \`Σ_i c_i(X)π(Y_i≠Y'_i)\`, but the c_i(X) are **global supremum sensitivities**. The present actual Wilson source calculation proves that a naive substitution \`Q=bare original SU2 fine one-link conditional\` has one nearest-neighbour \`c_i→1\` at large β, so a cutoff-independent *strict Dobrushin contraction* does not follow from this generic theorem. Note that a site-local B2 exponential upper envelope with arbitrary prefactor C is not itself contradicted by a nearest-site c_i→1; the blocked physical target and rooted-shell inequalities are separate.

The exact NON-CIRCULAR stronger use is to retain a source-specific coupling-weighted **good-pair event** \`Good_k(X;Y,Y')\` and *actual* local kernel differences. On Good one must prove an influence estimate

    TV(K_Q(.|Y),K_Q(.|Y')) <= Σ_i c^good_(k,i)(X) 1_{Y_i≠Y'_i}.

Off Good simply use TV≤1. Then for EVERY coupling of the actual exterior laws,

    TV(P_X,Q_X)
      ≤ A_X
        + E_π[ 1_Good Σ_i c^good_(k,i)(X) 1_{Y_i≠Y'_i} ]
        + π(Good^c).

This is a direct rigorous consequence of the existing mixture lemma, not a source-specific W3 proof. The **physical mathematical payments** are (a) identify actual Q_B/FP/R/localized target Q on the same genuine F19 blocked original four-column source, (b) derive a nonvacuous source-selected \`Good\` with gauge-invariant original plaquette/contour criteria and influence bounds, (c) construct an ACTUAL exterior coupling that controls weighted disagreement, (d) bound *bad-pair* and path-intermediate failures by already-owned original strong-beta chessboard/sparse-contour or genuinely renormalized good/mixed/large activities, and (e) sum the total cutoff physical shells without inserting the target mass gap as an assumption. **If coordinate interpolation passes through bad fields despite good endpoints, an endpoint-only bad probability bound is insufficient**; use a stable good-path condition or explicitly pay its path bad event.

Even if the weighted TV B1–B5 are paid, this gives a localized marginal comparison, NOT AUTOMATICALLY the termwise absolute connected CMP116 W3 activity, full RP/OS construction, or common spectral mass rate. Those remain distinct math endpoints.

## 4. Exact local reference and P0 terminal

Independent local Python/SymPy 1.14.0 script \`ym_p0_su2_single_exterior_worstcase_20261124.py\`, executed **23/23 exact assertion groups PASS**, Git-style blob \`9203374620629aba5dbe37fa7925517763b1248e\`, SHA256 \`7b0d988f5e43f1749267dda5988a964a34f8a6c4d6c44527724d302484b90bb4\`. Original 1536 plaquettes, six explicit native opposite positive links, all five-staple orientation/cyclotomic cancellation and gauge-invariant deficit sum, exact \`SU2\` Haar Bessel denominator and lower-bound limit; the local script is attached to the conversation. **This document's repo commit does not imply the script has been committed to GitHub**; no Agda/Lean kernel or CI run.

**Clay solution remains FALSE.** The next large mathematical task is to use the actual CMP119/122 axial rT/component \`Q_B\` and true weighted source-history sum to produce actual physical **good/bad path-coupled** local influence + differentiated original Wilson 1/F/G/FG marked source transfer, **then** original connected *absolute* W3 rooted-shell at cutoff-uniform SI physical m, **then** noncollapsed interacting same-H OS core. Stop repeating unsourced finite kernels or Landau auxiliary tests.
