# Yang–Mills Clay P0 — native side-two axial patch, exact Wilson source gauge disintegration and physical CMP122 Eq.(1.71) identification filter

24 November 2026. **The Clay objective is a nontrivial interacting four-dimensional continuum quantum Yang–Mills theory with a strictly positive mass gap on ONE same OS Hilbert space. Not acceptance counts.** \`YangMillsClaySolved=false\`. No Agda/Lean kernel or CI. Local SymPy 1.14.0 extended original-source checker **46,192/46,192 exact assertions PASS**; the executed reference is downloadable from the conversation, while this repository ledger is the mathematical proof, native geometry and exact remaining physical gate. Do not claim the executable file is GitHub-committed until readback confirms it.

## Current proof owners and literal source provenance

Reuse original L=4 4D SU(N) Wilson/Gibbs action and native gauge transport \`YMClaySUNVariablePeriodicGibbsGaugeExact\`, F19 globally unique 1/F/G/FG, noncommutative R445 64 coarse pair W and all 896 interacting spectators \`YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact\`, original rooted full-tree Haar quotient \`YMClayP0OriginalWilsonRootedTreeHaarGaugeW3OSSourceCut20261124.md\`, original ordered F19 one-pair T \`YMClayW0OriginalF19CandidateEquation171TExact\`, and conditional \`BalabanClayGate4TreeBackgroundSliceTransitionExact\`.

**Source localization pinpointed:** Balaban CMP122 (*Large Field Renormalization II*, 1989), source extract \`Docs/support/reference/balaban-source-extracts/cmp122-rg-lattice-gauge-ii.txt\` around original printed pp.377–379: (1.70) precedes the source-localized composite T, (1.71) contains an axial tree \`rT\`, admissible history sum, characteristic/delta/gauge constraints and an exponential including boundary/action terms; (1.72) assembles the R-operation. The **reversed Faddeev–Popov** passage immediately preceding Eq.(1.71) says that eligible first-class component gauge deltas can be removed only when integration over gauge variables is retained at least on those full components, and only because the other relevant characteristic factors/action are gauge invariant. It explicitly describes equivalence of densities, not pointwise equality. This is the *actual source conditional*, not a licence to erase the physical FP determinant, ghost/Jacobian, nonlinear Q_B, source E/R/B/V, or R-modified constraints.

## Exact localized original 4D Wilson SU(N) Haar change of variables

Take original periodic side-four graph E=1024 oriented positive links on 256 sites and 1536 original Wilson plaquettes. Select the **actual side-two R445 site block** \`B={0,1}^4\` (16 original sites). There are 32 original internal positive-link edges, 64 original edges crossing its boundary, and 96 original edges incident to B. Choose the boundary anchor edge \`e_anchor=((1,0,0,0),axis0)\` to the outside site (2,0,0,0), plus any spanning tree of the 16 interior sites rooted at (1,0,0,0) (15 internal native edges). The resulting 16 selected original links form a rooted forest attached to the fixed outside site. For an arbitrary field U of **all 1024 original links**, use gauge transformations h_x at all 16 sites B and h=I outside; the source endpoint formula is

    U'_e = h_{source(e)} U_e h_{target(e)}^{-1}.

Because the anchor and internal links are a tree, there is a **unique** h_B setting all 16 selected original links to identity. The solution is exact for every compact SU(N) and for arbitrary noncommuting U. The triangular map

    G^(1024 original links)  <->  G^16 (block gauge parameters) × G^1008 (rest of original links)

is a measure-preserving bijection for normalized product Haar. The measure Jac is **one** because every step is left or right Haar translation/inversion, *not* because the determinant of a physically selected background gauge is assumed one. Explicitly, for every integrable f

    ∫_{G^1024} f(U) dH^1024(U)
      = ∫_{G^1008} dH^1008(X)
           ∫_{G^16} f(h^{-1}·X_fixed_tree) dH^16(h).

The exterior-site gauge is held fixed; this quotient removes precisely the block gauge orbit, leaving all other original links and their interactions. It is NOT a block-spin decimation, not 64 F19 fibre integrations, and not a CMP119 ordered scale T.

For the genuine original Wilson action S and original spatial plaquette marks F,G (both gauge invariant), apply this identity to each of \`exp(-beta S)\`, \`F exp(-beta S)\`, \`G exp(-beta S)\`, \`FG exp(-beta S)\`. Their **common original full 1/F/G/FG coefficients** agree exactly after the axial tree gauge, for ALL beta≥0. The same original native original-positive-plaquette words and **all 896 R445 spectators** remain. Consequently the global two-mark mixed log also agrees wherever K(s,t)≠0, and every finite bare labelled Mayer activity with gauge-invariant plaquette factors commutes termwise with the gauge change. Neither an all-polymer absolute bound nor any nontrivial physical beta(a) follows.

At the true original R445 pair \`U_0(x),V(x+e)\` and coarse \`W=U_0 V\`, for every local h supported on B,

    W' = h(x) W h(x+2e)^{-1},
    V' = h(x+e) V h(x+2e)^{-1}.

Thus a fixed coarse W conditional source is **covariant**, not pointwise invariant under a fixed W label. Do not use a fake fixed-W equality; only the matching transformed endpoints or the globally integrated Wilson source is invariant.

## Source-level necessary-and-sufficient orbit-average condition (decisive for reversing FP)

The exact identity above works for *every* integrable source integrand, not merely gauge-invariant tests, provided its full group-orbit average is retained. Let \`A(U)\` be any selected density, insertion, characteristic function, gauge slice constraint or residual and let \`X\` be the rooted gauge-fixed representative. Define

    (P_B A)(X) := ∫_{G^16} A(h^{-1}·X) dH^16(h).

Then

    ∫_{G^1024} A(U) dH^1024(U)
      = ∫_{G^1008} (P_B A)(X) dH^1008(X).

A **pointwise source-localised replacement** \`A(X)\` for \`P_B A(X)\` is valid exactly when \`A(X)=P_B A(X)\` for Haar-a.e. rooted gauge-fixed X (or a weaker equality only after integrating X if the intended claim is merely a scalar partition). Gauge invariance of A is sufficient; an ungauged scalar source equality or merely invariant bare Wilson action is NOT sufficient when A includes a gauge-dependent delta, background minimizer, source-dependent characteristic, or FP factor.

**Sharp original continuous-Haar negative control:** choose the normalized real trace of one **open original tree link** \`A(U)=ReTr U_e/N\`. Its true full-source Haar integral equals zero for SU(N≥2): integrate its single independent link, or use the nontrivial central element \`e^{2πi/N}I\` to kill the first matrix moment. On the anchored axial slice the same tree link equals I, so \`A(X)=1\`. Therefore

    ∫_(original full) ReTr(U_e)/N dH = 0 ≠ 1 = ∫_(axial slice) ReTr(I)/N dH.

Dropping orbit integration/FP from an arbitrary gauge-dependent integrand produces a **strict false equality**, even though the Wilson action/closed loop markers are invariant. It is precisely the residual gauge dependence of CMP122's internal source terms and history-selected deltas that must be audited before applying its reversed FP operation. The finite Q8 check independently obtains 0≠1; the actual continuous-Haar proof uses SU(N) centre invariance, not Q8 replacement.

## Separate exact local standard Landau Dirichlet FP calculation (never identify with source rT)

The **auxiliary standard Landau**, not Balaban's selected axial or nonlinear background gauge, functional \`R(h;U)=Σ_e ReTr(h_x U_e h_y^{-1})/N\` restricted to gauge h=I outside B has quadratic Hessian at flat U=I given by the original native **Dirichlet** graph Laplacian D_B=8I−A_B on the 16 sites. Here A_B is the adjacency of the genuine 4D hypercube B; each site has four internal and four outgoing original nearest neighbours. Its COMPLETE scalar spectrum is

| eig | mult |
|---:|---:|
| 4 | 1 |
| 6 | 4 |
| 8 | 6 |
| 10 | 4 |
| 12 | 1 |

This differs from the earlier full-volume periodic L4 scalar FP spectrum (minimum nonzero 2 and a zero global gauge mode): pinning h outside B removes the zero mode and has **Dirichlet minimum 4**. The 4D block tangent dimension is \`D=16(N²−1)\`, and the determinant at U=I is \`[4⋅6⁴⋅8⁶⋅10⁴⋅12]^ (N²−1)\`.

For every original link **incident to B**, suppose \`||U_e-I||_op≤δ\`. With \`ω_x=0\` outside B, each original incident-link trace quadratic form differs from its flat value by no more than \`δ(||ω_x||+||ω_y||)^2\`. The full original incidence gives \`K_B=8I+A_B\`, spectral maximum \`12\`. Thus, for arbitrary original SU(N) link matrices and any tangent ω supported on this block,

    |Q_U(ω)−Q_I(ω)| ≤ 12δ||ω||²,
    Q_U(ω) ≥ (4−12δ)||ω||²,

and the sufficient positive-local-Hessian condition is **δ<1/3**. In this condition,

    (1−3δ)^D ≤ det(M_Landau(U)|B)/det(M_Landau(I)|B) ≤ (1+3δ)^D.

This ratio is positive, and assumes the actual local gauge condition is at a stationary point if used as an FP matrix for a gauge-fixed path integral. Mere positivity of the *Hessian of the functional* at a nonstationary U does not itself establish the nonlinear gauge-fixing solution or its FP weight.

For an ordinary anchored native hypercubic side-b block B⊂(Z/LZ)^4 with b+2≤L, the exact Dirichlet eigenvalues are \`2Σ_(μ=1)^4 [1−cos(πn_μ/(b+1))]\`; hence

    lambda_min(b)=8(1−cos(π/(b+1))),
    ||K_B||=8(1+cos(π/(b+1))),
    δ_b^suff=lambda_min/||K_B||=tan²(π/[2(b+1)]) ~ π²/(4b²).

The **fixed 2-site block** margin δ<1/3 is independent of overall periodic lattice volume, unlike the raw global Landau Hessian. However, if a selected physical block has side b(a)≈R/a with R>0, the sufficient small-field radius shrinks as O(a²). Neither the bare high-beta local energy-excess estimate nor the source's actual \`Q_B\`/R-bound has been shown to guarantee this δ(a) for every link. This is a true physical-scale tradeoff, not a claimed mass gap.

Crucially, the exact axial gauge transformation does **not automatically preserve the small-field norm condition** used by the different Landau local-Hessian estimate. They are separate mathematically valid source diagnostics; composition requires a *source-specific gauge slice map and quantitative field control*, not juxtaposition.

## Executed original native regression and exact remaining physical lemmas

The independent extended [local script](../../scripts/check_ym_p0_original_block_axial_dirichlet_source_20261124.py) was **executed** with SymPy 1.14.0 (46,192/46,192 assertions), uses 1,536 original native Wilson plaquettes for 8 noncommuting full field configurations, 16 interior block gauges, all 64 original R445 pairs in each test, and checks full-action and two true plaquette marks. It additionally performs full 8^5=32,768 versus tree-fixed 8^3=512 Q8 small-graph normalized source-Haar comparisons on all 1/F/G/FG columns, explicitly different from a full L4 continuous-Haar integral; checks open-link noninvariance; verifies all 16 Dirichlet modes and exact b-dependent half-angle threshold. **GitHub code producer now exists and has been read back**: `scripts/check_ym_p0_original_block_axial_dirichlet_source_20261124.py`, blob `c089cf0312fa6b92d446dde1dff8d22402ed7546`. The committed checker is a **compact source-equivalent edition** of the separately executed 46,192-check extended local script; the GitHub bytes have **not** been executed locally, so the extended acceptance total is not claimed for that compact edition. The full executed version and JSON receipt are available as conversation downloads. Local regression checks geometry/group algebra/FP spectra; the all-group Haar and all-N operator-norm claims are derived analytically from standard compact-group Haar and trace matrix inequalities. No Agda/Lean kernel or CI.

**Remaining mathematical P0 endpoints, exact step:**

1. \`CMP122 Eq171 rT\` — instantiate the **source-selected** rT for one nonempty actual admissible Omega/Lambda/S component and identify its exact graph/anchor, actual background \`Q_B\`, delta constraints, source action/normalization, FP/ghost/Jacobian, rotated coordinate axes and E/R/B/V. Prove the TRUE source component's full integrand either is gauge invariant on the whole integrated component or that the true orbit-average/FP identity holds including each noninvariant factor and history sum. SOURCE DOES NOT CLAIM THAT ITS rT IS THE 16-edge block tree used here.
2. \`CMP119 Eq2.18–2.23\` — assemble that source-selected operation and all other legitimate large-field/regular histories with the correct \`S_j\` internal in \`T_k\`, preserving original full Wilson and F19 same-operator four source insertions and gauge-invariant marks, and prove quantitative four-column errors including differentiated genuine physical residuals; the existing compiler consumes these inputs.
3. \`CMP116 W3\` — attach full **normalized log-Ursell/incompatibility** two-support differentiated physical activities, absolutely dominate all rooted shells at actual weak-coupling \`beta(a)→∞\`, including exceptional/large-field and SU3 baryonic channels, entropy/prefactor and fixed-positive SI physical rate. Bare termwise equality under tree gauge is **not** the absolute estimate.
4. \`Clay E1/OS/D2/N1/G1\` — construct one noncollapsed original SU(N) 4D interacting continuum, RP/OS, SAME positive Hamiltonian, dense centered gauge-invariant local-word core, common positive physical exponential time rate and full-sector spectral gap (not just one Wilson observable). Only then \`YangMillsClaySolved=true\`.

Attribution: original Wilson/Haar, SU(N) standard group/trace/gauge invariance, Bałaban CMP98/99/109/116/119/122 and published reversed FP/axial rT, Faddeev–Popov, classical Dirichlet Laplacian, Osterwalder–Schrader and existing original DASHI F19/R445/W3/OS proof consumers.
