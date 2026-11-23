# Clay Yang–Mills P0 — THREE weld rounds: nonconstant transverse mode, source F19 indexed square, physical CMP119/W3/OS
Date: 23 November 2026. Owner: original YM master-based PR #1536. RH #1533 / H05 #1291: chart/geometry donors, subordinate to Clay YM P0.

**Priority correction:** We have already constructed and tested the signed-zero branch, source residual, orientation, original 4D bond/plaquette incidence, Singer grade k, history clock t, and physical source time. They distinguish the SAME original 4D Wilson gauge system from the fixed P3^9 graph. Do **not** create a fourth geometry/graph invariance "round", or assume k is Balaban RG time. Three rounds here means three targeted *cross-representation/source* welds; it does NOT mean the Clay mass-gap theorem can be completed merely by three finite chart rewrites.

## Round 1 — ORIGINAL Wilson Cartan transverse Fourier Hessian / nonconstant wave: locally exact

**Recovered existing source**: \`Docs/physics/YMClaySUNNonconstantLinearWaveSourceSeam20261123.md\` and \`scripts/check_ym_sun_nonconstant_linear_wave_20261123.py\` are already on #1536; \`BalabanPeriodicDifferenceSymbols.agda\` owns native periodic difference/curl/Hodge/reference Fourier theorem statements, \`BalabanPeriodicFourierHodgeRegression.agda\` their source type regressions. The reference Hessian there includes gauge-fixing/block terms and is NOT automatically the pure Wilson Cartan curl Hessian \`H(p)\`. The original changing-side finite SU(N) periodic 4D Wilson gauge action is already implemented in \`YMClaySUNVariablePeriodicGibbsGaugeExact\`; the explicit one-Cartan-generator second variation is a special selected SU(2) background near identity, NOT the full interacting non-Abelian one-loop Hessian.

For \`U_mu(x;eps)=exp(i eps A_mu(x) sigma3)\`, original Wilson plaquette deficit \`1-(ReTr P)/2=1-cos(eps F_munu)\` gives \`J''(0)=F_munu^2\`, with \`F_munu=Delta_mu A_nu-Delta_nu A_mu\`. For \`p=(0,2pi/L,0,0)\`, \`d_mu=exp(i p_mu)-1\`:

\[
H_L(p)= \left(\sum_{\alpha=0}^3 |d_\alpha|^2\right)I_4-d\,d^\dagger
 = \mathrm{diag}(\lambda_L,0,\lambda_L,\lambda_L),\quad
\lambda_L=4\sin^2(\pi/L).
\]
**Exact values**: L4: 2; L8: 2−√2; L16: 2−√(2+√2). \`H d=0\` is ONE longitudinal gauge-null vector; exactly THREE transverse polarizations have the positive nonzero selected eigenvalue. \`A_2(x_1,t)=cos(2π(x_1-t)/L)\` is a nonconstant exact discrete centered-wave solution on these sizes. This is an **exact finite linearized wave fixture**; the integer-pair wave algorithm and a physical YM Hamiltonian remain different operations.

Independent locally executed SymPy 1.14 script [three-round finite checker](../../scripts/check_ym_p0_three_round_transverse_hessian_f19_20261123.py) passed exact radical eigenvalues, longitudinal and three transverse equations, exact temporal/spatial second differences and Fourier norm-energy normalization at L4/8/16. Previous original Wilson 1536-plaquette gauge and global 1/F/G/FG mark check also already passed in source script. This is **not** an analytic Agda proof of the nonzero-mode eigenspectrum or physical Yang–Mills covariance in infinite volume.

## Round 2 — selected F19 original pair tangent AND Singer k/time native source square: formal + local exact

Original **noncommutative** R445 two-bond product is \`W=U0 V\`, \`V=U1\`, \`U0=W V^-1\`, full original 64 selected pairs and **896 interacting spectators**. For Cartan Lie tangent at the actual Wilson identity, linearization of the actual group multiplication is

\[
J_\mathrm{F19}=\begin{pmatrix}1&1\\0&1\end{pmatrix},\quad
(\delta W,\delta V)^T=J_\mathrm{F19}(\delta U_0,\delta V)^T,\quad
J_\mathrm{F19}^{-1}=\begin{pmatrix}1&-1\\0&1\end{pmatrix}.
\]

At the ORIGINAL UNMARKED Wilson stationary identity, the **full native Wilson curl quadratic Hessian** under this invertible two-link coordinate change obeys
\[
H_{\rm F19}=J_{\rm F19}^{-T}\,H_{\rm original}\,J_{\rm F19}^{-1}.
\]
Its 64 native pair blocks and untouched 896 spectators form the original full 1024 dimensional reindex/tangent transform, not a Wilson mass or new quadratic action. A source-equivalent exact six-link/two-pair **non-diagonal coupled spectator** algebraic regression checked \`H_new=J^-T H_original J^-1\` directly as the literal Hessian of pulled-back curl energy; this is a local selected test, **NOT** an Agda/functional analysis theorem for the arbitrary SU(N) physical field manifold.

The original RH Singer grade source action is the **already built** Griess/Sah/antipode order-26 word on the existing 9-trit hyperfabric. Each original C4 coordinate retains its zero-branch bit \`0↦neg,1↦(zero,0),2↦pos,3↦(zero,1)\`; the complete original 256 gauge sites are recovered at each of 26 stages, even though the projected nine-trit coordinate changes zeros and fixed-P3^9 neighbours. The original *physical* source link and Wilson plaquette incidence are moved together. **Do not identify chart k with the original 4D Euclidean time direction OR the physical RG k.**

The existing current module \`YMClayY369OriginalSingerWilsonFourMarkSourceWeldExact.agda\` already source-writes:
- \`sourceIndexedAddressRefinementSquare\`: original SOURCE edge and its grade-refined endpoint chart commute;
- \`sourceIndexedLinkRecoversOriginal\`, \`originalIndexedPlaquetteIsOriginal\`, \`originalIndexedSixPlaneWilsonDeficitIsOriginal\`, \`originalWilsonActionDensityIndexedEqualsOriginal\`: original 1024 fields/1536 native plaquettes and full Wilson action;
- \`originalIndexedWilsonPartitionIsOriginal\`, \`originalIndexedWilsonNumeratorIsOriginal\`, \`originalIndexedWilsonFourMoments\`, \`originalIndexedWilsonNormalizedEqualsOriginalF19\`: original one Z and 1,F,G,FG, with the **original inverse F19 sorting permutation applied to marks** before comparing canonical and sorted vectors;
- **NEW** \`originalIndexedWilsonTimeSecondIsOriginal\` and \`originalPhysicalTimeSecondDifferenceCommutesWithSingerStage\`: the 3-slice second difference of the **ACTUAL ORIGINAL WILSON GIBBS DENSITY** is independent of Singer chart stage k, for any original 1024-link temporal source trajectory. This is a genuine nontrivial k/time *transport* square, not a proof the arbitrary trajectory itself solves a nonlinear Yang–Mills wave equation or that the Gibbs density is a travelling wave.

The finite 26-stage Q8 source gauge and Wilson testing is independent of the local F19 Hessian test. **Agda kernel/trust receipts for ALL newly written declarations are pending.**

### Crucial Hessian chain-rule warning

For a nonlinear coordinate map \`x=x(y)\`, the Hessian has BOTH terms:

\[
\nabla_y^2[S(x(y))] =
D x^T(\nabla_x^2 S)D x +
\sum_i (\partial_{x_i}S)\,\nabla_y^2 x_i.
\]

At unmarked original identity the \`grad S=0\` term disappears, validating the simple J-congruence. A globally marked source, a physical background, or the local Bałaban gauge-fixed density can have nonzero first derivatives; there the **second term is essential**. The local regression verified an explicit nonlinear mark \`S(x)=x^2/2+theta x\`, \`x(y)=y+y^2\` with Hessian \`1+2theta\`, not \`1\`. Therefore do NOT identify the full marked F19/CMP119 action Hessian or inherit a source Hessian covariance by simple fixed J-congruence.

## Round 3 — physical source/localized RG and same-H continuum: genuinely still UNPAID

**Owned compilers, not missing frameworks:** master \`BalabanCMP119Equation218FactorizedFunctionalDensityExact\` already owns (2.18–2.22) Omega/Lambda/S histories and ordered T products/residual; \`BalabanCMP122Equation171TOperationSemanticsExact\` and Gate4/refinement own constrained T source; \`BalabanCMP119Section2SourceNativeStateExact\`, Round214 E/R/B/V original effective action; #1444 \`YMClayCMP119122116SelectedProducerWeldExact\` already owns beta/marked same-flow compiler, but #1444 is research-branch-based; master and #1536 own actual original Wilson/R445/F19 marked full source; \`YangMillsPreferredWilsonWEXTSourceRound576Exact\` plus R574/R494/CMP116 already compile a **given** original rooted absolute shell into a positive rate; original finite/native RP and \`YMClayE1TimeKResidualCylinderWaveTransportExact\` own conditional physical-time/cutoff/convergence/comparison structure.

**Exactly remaining physical source gates**:
1. **P0.T**, source-specific original Wilson normalized 1/F/G/FG ⇔ original nonlinear CMP98/109 transported logarithm averaging (correct path13 L=13 vs original F19 scale2 meanings), CMP119 admissible \`Omega/Lambda/S\` with \`S\` INSIDE T, CMP122 Eq1.71 continuous original SU(N) constrained Haar/gauge/FP/ghost/Jacobian/R-operation, E/R/B/V/vacuum and real beta(a) **one actual selected source**, including full marked Hessian chain rule (direct second derivative + first-score covariance). Need original *inhabited* source equalities or quantitative source errors, not more generic records.
2. **P0.W3**, original differentiated, termwise ABSOLUTE two globally unique Wilson marks source cluster weights, rooted **native graph distance in physical units**, sparse/mixed large-field budgets and entropy corrected uniform cutoff/volume and beta(a) physical rate. Need positive m_phys independent of a, not a positive one-wave Fourier eigenvalue. The fixed-spacing \`lambda_L = 4 sin²(pi/L) -> 0\` for L→∞; at fixed unit physical box with \`a=1/L\`, \`lambda_L/a² -> 4pi²\` is finite-box infrared energy from its boundary, **not** a generated YM mass. A massless linearized transverse Fourier mode cannot certify a mass gap.
3. **P0.OS**, actual gauge-invariant observable cylinder dense algebra, original interacting noncollapsed continuum RP/OS measure and full same-H nonvacuum spectral gap D2 from **those** original source W3 bounds; N1/G1 still separate.

The "three rounds" are (1) source linearized Fourier acceptance, (2) actual original nonlinear-coordinate/source-index time-k commuting square, (3) the physical CMP119/W3/OS source application. (1) local exact PASS, (2) source-written + local exact PASS **kernel pending**, (3) PHYSICAL unproved analytic obligation. Do not claim the Clay Yang–Mills theorem solved in three elapsed steps or source code commits.

**Trust, provenance:** no Agda 2.9 available locally and no GitHub CI used; full continuous SU(N) Haar is an explicit authority input; exact local SymPy/Q8 tests are not actual weak-coupling RG analytic estimates. Reuse Wilson, Haar, Bałaban, the original DASHI SU(N)/F19/R445/CMP119/122/OS owners and RH #1533/H05 #1291 only as indexed chart donors. Preserve P0 status E1/D1/D2/N1/G1 open.
