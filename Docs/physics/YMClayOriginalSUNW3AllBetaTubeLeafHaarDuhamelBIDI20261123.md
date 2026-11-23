# YM P0 / W1–W3 — original SU(N) all-coupling Wilson tube, Haar leaf removal and full-source Duhamel return

23 November 2026 · SOURCE-FIRST continuation, no duplicated original finite F19 operator, no physical gap claimed.

## 0. Precedence, artifacts and honest proof boundary

**Read and reused, rather than rebuilt:** original four-dimensional 1024-link/1536-plaquette native Wilson source; original two-mark 1,F,G,FG on F19 64 noncommutative coarse pairs and all 896 spectators in \`YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact\`; original arbitrary-weight 64-pair/896-spectator Haar disintegration \`YMClaySUNWeightedDisjointPairFibreReparamExact\`; physical Wilson/F19 partition \`YMClayOriginalWilsonPhysicalF19PartitionExact\`; earlier [original eight-face source certificate](YMClayOriginalSUNW3TwoTimeEightPlaquetteHaarSurface20261123.md), original 17 Nov exact polynomial/Haar low-degree source checker, \`BalabanCMP119Equation218FactorizedFunctionalDensityExact\`, \`BalabanCMP122Equation171TOperationSemanticsExact\`, \`BalabanLiteralTwoWilsonCMP116ConnectingTailExact\`, \`BalabanLiteralWilsonMarkedLocalizationSourceExact\`, R573/R576/R551/R552 and [P0 physical-source audit](YMClayP0CMP119122W3SameHActualSourceInstantiationAudit20261123.md). No duplicate generic source/cumulant/Hamiltonian record.

**Independent locally executed full source checker:** [check_ym_original_sun_tube_allbeta_leafhaar_20261123.py](../../scripts/check_ym_original_sun_tube_allbeta_leafhaar_20261123.py), exact original geometry and SymPy 1.14, mpmath SU2 Weyl integral and Bessel checks at \(\beta=.2,1,3,8\); a separately executed longer local checker tests all four cutoffs L3–L6, all 1≤d<L, original 3 transverse planes, global 5^8 surface search, source Duhamel and eight-moment necessity. Distinct independent 800k-sample **gauge-fixed SU2 S² simulation** at beta 3 and 8 agrees with exact formula within statistical error; it is a numeric check, NOT rigorous 4D global Haar integration. GitHub compact script fetched, source-equivalent; no claim compact script was run byte-for-byte locally or Agda/Lean/CI tested.

## 1. FULL original Wilson 4D link/plaquette source; only eight action couplings active

For every \(N\ge2\) use genuine original finite periodic \((\mathbb Z/L)^4\) lattice \(L\ge3\): \(4L^4\) positively oriented independent \(\mathrm{SU}(N)\) links with normalized Haar, \(6L^4\) ORIGINAL positive-oriented plaquettes. No factors removed from the original product Haar integration. For a spatial plane (axes \(a<b\) among \(1,2,3\)) and \(1\le d<L\), select the TWO ORIGINAL closed gauge-invariant plaquette marks
\[
F=t_{(0,\vec0;a,b)},\qquad G=t_{(d,\vec0;a,b)},\qquad
t_p(U)=N^{-1}\operatorname{ReTr}P_p(U).
\]
Choose the original \(4d\) side plaquettes \(T_d\) on the four faces of the \(1\times1\times d\) temporal prism. Their caps are F and G; all other \(6L^4-4d\) physical source plaquette couplings are SET TO ZERO **only in this inhomogeneous restricted-source experiment**, not discarded from the homogeneous Wilson theory or physically renormalized \(T\). The authentic ORIGINAL finite source is
\[
Z_{L,T_d}(s,t;\boldsymbol\beta)
=\int_{\mathrm{SU}(N)^{4L^4}}
\exp\left(sF(U)+tG(U)+\sum_{q\in T_d}\beta_q t_q(U)\right)\prod_{\ell\in E}dH(U_\ell),
\]
with \(\operatorname{Cov}_{T_d}(F,G)=\partial_s\partial_t\log Z|_{s=t=0}\). The standard original Wilson deficit density \(e^{-\sum_q\beta_q(1-t_q)}\) differs only by a source-constant factor, which cancels in this normalized response. At \(L=4,d=2\) there are 1024 links, 1536 native plaquettes, two marks on t0 and t2, and eight side interactions. **Time** here is an original Euclidean lattice coordinate, not H05 k, RH horizontal x, a Hamiltonian evolution, or RG scale.

## 2. Original Haar-leaf theorem: all 255 proper tube subsets are EXACTLY decoupled, at arbitrary wall coupling

A plaquette P whose original 4-link word contains a physical link \(\ell\) absent from every other currently chosen plaquette can be integrated first: for fixed all other fine links, its holonomy \(P=A U_\ell^{\pm1}B\) has full independent normalized \(\mathrm{SU}(N)\) Haar law by left/right invariance. Thus for ANY bounded measurable function \(\phi(P)\),
\[
\int_{\mathrm{SU}(N)}\phi(AU_\ell^{\pm1}B)\,dH(U_\ell)
=\int_{\mathrm{SU}(N)}\phi(V)\,dH(V)
\]
and the chosen plaquette class observable is independent of ALL other selected face observables, even with nonlinear weights \(e^{\beta_q t_q}\), not merely at Taylor order 8.

The full original \(L=4\) source has EXACTLY 256 subsets of the eight original temporal side plaquettes. A complete source-native greedy leaf-link elimination terminates on every one of the 255 PROPER subsets for the selected 2 caps F,G, but cannot even begin on the FULL 10-face sphere. Removing either marked cap from the full sphere leaves a nine-face disk and likewise eliminates all nine faces. Hence
\[
\boxed{\operatorname{Cov}(F,G)=0}
\]
for ALL real finite source wall couplings whenever \(T'\subsetneq T_2\) is the only activated wall set. This is an actual SU(N) full finite product-Haar theorem, not a probabilistic independent-plaquette assumption in the full homogeneous Wilson model.

The original \(L=3,4,5,6\), all \(1\le d<L\) and all 3 spatial transverse planes pass actual 4D incidence tests: \(4d+2\) source faces, \(8d+4\) links each occurring exactly twice, \(4(d+1)\) vertices, \(\chi=2\); deletion of any one side face and deletion of either cap leave a peelable complex. By the same topological disk/leaf proof the statements extend to each nonwrapping embedded original prism for general \(L\ge3\), \(d<L\); the checked finite set is not a replacement for a machine-verified universal original Agda theorem.

## 3. Exact all-beta W1 connected source, for genuine continuous SU(N)

Define the original one-link compact \(\mathrm{SU}(N)\) fundamental-character integrals
\[
z_N(\beta)=\int_{\mathrm{SU}(N)}e^{\beta t(U)}\,dH(U)>0,\qquad
m_N(\beta)=\frac{z'_N(\beta)}{z_N(\beta)}
=\frac{\int t(U)e^{\beta t(U)}\,dH(U)}{z_N(\beta)}.
\]
Schur/Peter–Weyl fundamental orthogonality gives \(v_N:=\int t(U)^2dH(U)=1/4\) for SU2, \(1/(2N^2)\) for N≥3, and \(m_N(0)=0,\ m_N'(0)=v_N\).

**EXACT source theorem for arbitrary finite \(\beta_q\) on the selected original walls:**
\[
\boxed{
\operatorname{Cov}_{L,T_d}(F,G;\boldsymbol\beta)
=v_N\prod_{q\in T_d}m_N(\beta_q).
}
\]
Proof: the 2-mark sphere has a connected dual-face graph, EVERY original source link belongs to exactly two selected faces, and each cap carries the FUNDAMENTAL/DUAL fundamental normalized character. Integrating any common link forces the SAME irrep on neighboring faces (Haar orthogonality). Connectivity forces that fundamental representation through ALL \(4d\) actual Wilson walls. All higher character terms in \(e^{\beta_qt_q}\) are killed by this source contraction. For SU(N), the surviving fundamental Fourier coefficient of the wall weight is \(N z_N(\beta_q)m_N(\beta_q)\); multiply the normalized 2-cap trace coefficients and the original \(E=8d+4\) Haar link contractions / \(V=4(d+1)\) colour-index loops. SU2's self-dual trace is REAL; N≥3 has a pair of coherent fundamental/antifundamental orientations. This gives exactly \(v_N\prod m_N\), no unknown cluster error. Removing a cap yields an original leaf-Haar disk, so \(\mathbb E F=\mathbb E G=0\) and no disconnected subtraction. The zero-source partition is independently the product \(\prod_q z_N(\beta_q)\) by full leaf-Haar elimination of the 8 wall faces. Thus this is the actual normalized mixed-log Hessian, not an unnormalized moment.

For a common wall-only coupling β on \(4d\) faces:
\[
\operatorname{Cov}_{L,T_d}(F,G;\beta)=v_Nm_N(\beta)^{4d},
\qquad
[\beta^{4d}]\operatorname{Cov}=\frac{v_N^{4d+1}}{1^{4d}}.
\]
For d=2 this reproduces the previous SELECTED eightfold MULTIVARIATE derivative \(C_N^{[8]}=v_N^9\). The coefficient of the SINGLE bare \(\beta^{8}\) term in the wall-only Taylor series equals \(v_N^9\), because the only surviving degree-eight monomial uses every one of the eight walls once. It is NOT the homogeneous full-1536-plaquette coefficient.

For SU2, original Haar on \(S^3\) has \(\theta\)-weight \((2/\pi)\sin^2\theta\,d\theta\) and \(t(U)=\cos\theta\), giving EXACTLY
\[
z_2(\beta)=2I_1(\beta)/\beta,\quad
m_2(\beta)=I_2(\beta)/I_1(\beta),\quad
\operatorname{Cov}_{T_2}(F,G;\beta)=\tfrac14[I_2(\beta)/I_1(\beta)]^8
\]
(continuous at β=0). SymPy 1.14 exact series:
\[
m_2(\beta)=\beta/4-\beta^3/96+\beta^5/1536-\beta^7/23040+O(\beta^9),
\]
\[
\operatorname{Cov}_{T_2}=\beta^8/262144-\beta^{10}/786432+
5\beta^{12}/18874368+O(\beta^{14}).
\]
Independent local 55-digit SU2 Weyl integral vs Bessel ratio passes at β=.2,1,3,8; selected covariance values respectively ≈9.6364945798e-12, 2.7697033187e-6, 0.00270557538581, 0.0507304959978. An independent 800,000-sample gauge-fixed original surface SU2 Monte Carlo at β=3/8 gives 0.00265055 ±0.00028 / 0.05071710 ±0.000275, consistent with the exact numbers, but is NOT an original 1536-face numerical measure.

For β>0, compact Haar variance shows \(m'_N(\beta)=\operatorname{Var}_\beta(t)>0\), while \(m_N(0)=0\) and \(m_N(\beta)\to1\) as \(\beta\to\infty\). The RESTRICTED tube-only lattice decay rate per original native time step \(-4\log m_N(\beta)\to0\) as β grows; SU2 evaluations at β=2,20,200 are about 3.3468932, 0.3075771, 0.0300751. **No β-uniform native step decay** follows, and the physical mass \(-4\log m_N(\beta(a))/a\) has a distinct cutoff scaling. It is invalid to read any physical interacting OS gap from this restricted-source expression.

## 4. COMPLETE original eight-boundary-link minimum-surface enumeration: EXACTLY TWO

For the \(L=4,d=2\) original marks, each of the 8 positive boundary links (4 on F, 4 on G) lies in exactly SIX original source plaquettes, and exactly FIVE are legal nonmarked side candidates. A previous proof shows an eight-face square-free mark-excluding mod-2 closure must choose ONE distinct adjacent original face per boundary link. Hence *all possible* eight-face source completions are within \(5^8\) configurations. The new exact checker builds all 1536 source 4-link plaquette words, maps all 1024 original positive link ids to Python integers, encodes mod-2 boundaries as 1024-bit XOR integers and uses a complete \(5^4+5^4\) meet-in-the-middle match against \(\partial F+\partial G\). Precisely **TWO solutions**, the forward t=0→1→2 and reverse periodic t=2→3→0 eight-face tubes. They are distinct, each has two cap faces + eight walls and \(\chi=2\). This is exact exhaustive finite combinatorics, NOT an MILP assumption, and is stronger than constructing one tube.

The geometry does NOT establish that the full original homogeneous Wilson \(\beta^8\) covariance has coefficient exactly \(2v_N^9\): full original action also contains mark-plaquette activities, repeated plaquettes, source normalization and every other connected cluster; there is no proved exclusion of all those terms in the common-beta log expansion here. In particular TWO genuine physical periodic-time routes for ONE selected spatial plane are not the unrelated H05 six indexed cube faces, and three spatial planes times two time routes do not identify six new physical DOFs.

## 5. Exact return to the WHOLE original homogeneous 1536-plaquette Wilson action: source Duhamel = three-mark connected covariance

Keep the SAME ORIGINAL \(L=4\) product Haar source and marks F,G. Let all eight selected wall plaquette couplings remain β and turn on the other \(1536-8=1528\) ORIGINAL (including caps F,G, remote plaquettes and all spectator link interactions) uniformly with \(\tau\in[0,1]\):
\[
d\mu_\tau \propto\exp\big[\beta\sum_{q\in T}t_q+
   \tau\beta\sum_{p\notin T}t_p\big]\prod_{\ell=1}^{1024}dH(U_\ell).
\]
The source Wilson deficit constants cancel in every normalized expectation. The literal finite compact-group \(\mu_\tau\) partition is positive/analytic for all finite real β. Let \(\kappa_{\mu}(A,B,H)\) be the THIRD joint cumulant
\[
\kappa_\mu(F,G,H)=\mathbb E[FGH]-\mathbb E[FG]\mathbb E[H]
-\mathbb E[FH]\mathbb E[G]-\mathbb E[GH]\mathbb E[F]
+2\mathbb E[F]\mathbb E[G]\mathbb E[H].
\]
Differentiating the ACTUAL source normalized log-Hessian (under finite compact integral, no uniform limit) gives the **exact non-surrogate restoration equation**
\[
\boxed{
\operatorname{Cov}_{\mathrm{FULL},L=4,\beta}(F,G)
=v_Nm_N(\beta)^8
+\beta\int_0^1\sum_{p\notin T}^{1528}
\kappa_{\mu_\tau}(F,G,t_p)\,d\tau .
}
\]
The finite three-state exact rational SymPy fixture checks the normalized derivative/cumulant identity, but the equation itself is analytic differentiation of this ORIGINAL continuous SU(N) finite measure. For variable original L the residual sum contains \(6L^4-4d\) source plaquettes, with the same physical original \(d\) Euclidean lattice separation. This is a precise bidirectional source restoration equation: bare tube primitive + FULL original coupled Wilson remainder = FULL original response. The 1,528 three-mark terms are NOT known to be small or absolutely summable; this formula alone does NOT pay W3. A source-independent \(|t_p|\le1\) bound gives only an extensive-in-volume bad estimate, not the W3 rooted shell. Cancellation in a SIGNED third-cumulant sum is also not the required ABSOLUTE marked-cluster estimate.

### Eight original observation coefficients, not four, are required for source-restoration

The original F19 fine two-mark source correctly transports 1,F,G,FG. But each \(\kappa(F,G,t_p)\) additionally consumes \(H=t_p\), \(FH\), \(GH\), \(FGH\), for the **SAME original physically weighted measure at each \(\tau\)**. A concrete exact rational source negative control: F,G are independent symmetric ±1; model A takes H=FG, model B takes H independent symmetric ±1. Their seven moments \(1,F,G,FG,H,FH,GH\) are IDENTICAL (all nonconstant ones zero) but \(\mathbb E_A[FGH]=1\ne0=\mathbb E_B[FGH]\). Thus no generic four-source (indeed seven-source) sufficiency theorem may recover the full W3 restoration derivative. The local exact rational checker passes. This is an **observer/consumer cardinality**, not a new physical species or an eighth dynamical DOF.

**Reuse existing sources, DO NOT build a duplicate eight-source operator:** \`YMClaySUNWeightedDisjointPairFibreReparamExact.originalAllPairsGeneralWeightedChange\` transports ANY fine integrand under the original 64-pair/896-spectator reparametrization, and \`YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact\` already exposes arbitrary fine tests. Instantiate those for 1,F,G,FG,H,FH,GH,FGH at each \(\tau\), retaining the actual entire Wilson source weight and all link spectators. **Remaining kernel/source realization:** actual common admissible CMP119/122 constrained T with \(\Omega,\Lambda,S\) (S INTERNAL to T), original background/FP/Jacobian/density, large field, factorized ordered components; no equation here has proved these analytic facts or their identification with the full native Wilson F19 source.

## 6. P0/W3/OS present owner and precise OPEN endpoints

- Original \`BalabanLiteralTwoWilsonCMP116ConnectingTailExact\`: connecting-cluster absolute charge and finite rooted-shell sum are compiler-owned but \`twoWilsonPointwiseCMP116ChargeLevel = conditional\`, \`twoWilsonChargeSumBelowRootedTailLevel = conditional\`. The exact source coupling restoration must be reorganized into actual CMP119/122 E/R/B/V cluster activities with termwise ABSOLUTE bound, both small- and large-field, physical distance/time and a cutoff-independent ROOTED shell. Proving only a signed Duhamel remainder is not enough.
- Original \`BalabanCMP119Equation171PhysicalTOperationRealizationExact\`: applying full original \(T\) equals Eq1.71 constrained mass and Eq1.71 equals literal physical Gate4 remains conditional; \`BalabanCMP119Equation218FactorizedFunctionalDensityExact\` original component/step/domain extraction remains conditional. Original \`YMClayD1OriginalFullWilsonSmallLargeFieldExact\` keeps full-original vs selected small-field and frustrated large-field distinct.
- Original \`YangMillsSourceFirstWilsonCovarianceRound556Exact\`, \`YangMillsWilsonContinuumClusteringRound551Exact\`, \`YangMillsWilsonSameHMassGapRound552Exact\`, original interacting OS/Hamiltonian same-object constructors: already present and NOT to be duplicated. Physical mass-gap input and continuum same H remain conditional; one finite nonzero two-mark tube source or a one-tube decay rate is not an interacting four-dimensional Yang–Mills gap.
- **Next true P0 maximum cut:** instantiate a single \(\tau\)-dependent physical CMP119/122 localized \(\Omega/\Lambda/S\) T on the original all-plaquette \(\mu_\tau\); transport the eight original finite Wilson marked coefficients through existing arbitrary-weight F19; identify and prove the source pointwise ABSOLUTE two-Wilson connecting charge and the 4D original rooted-shell entropy/large-field bound in SI physical time uniformly under \(\beta(a)\to\infty\). Then consume R556→R551→R552 on the SAME interacting OS reconstructed H. Do not equate a one-tube bare strong-coupling formula with high-\(\beta\) renormalized W3.

**Source attribution:** Wilson original periodic 4D SU(N) lattice and character action; compact Haar / Schur / Peter–Weyl / 2D spherical lattice gauge character contraction (pure mathematical identity of this embedded face subset, NOT a replacement 2D physical theory); Bałaban CMP109/116/119/122, Osterwalder–Schrader, original DASHI F19 and marked KP source. Native 4D physical time and H05 signed-index coordinate remain distinct. No Agda/Lean kernel/CI, original global W3, YM or RH Clay claim is implied.


## 7. Source-written original third-mark F19/W0 W3 receiver

NEW [source-written Agda W3 original third-mark F19/W0 proof](../../DASHI/Physics/YangMills/YMClayOriginalWilsonW3ThirdMomentF19W0BIDIExact.agda) advances the SAME original finite 8-slot W3 source past a prose suggestion. It specializes **existing** \`YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact.originalFineCoefficientEqualsF19\` to four entirely native additional weighted source-integrands H,FH,GH,FGH, with \`FineTest\` on actual 64 original noncommutative fine pairs and 896 original spectator links and an arbitrary fine source weight. The new \`sourceHIsF19\`, \`sourceFHIsF19\`, \`sourceGHIsF19\`, \`sourceFGHIsF19\` use only prior all-integrand equality terms, not guessed factorization or a second measure. The \`sourceFGHIsOriginalW0CandidateT\` and \`sourceFGHOriginalW0FirstPairTStep\` reuse the **existing W0** \`candidateMassIsExistingOriginalF19\` and \`sourceF19MarkedFirstPairLocalizationExact\`, retaining the triple product INSIDE the original first-link SU(N) Haar V fibre and all 896 spectator marginals. The module is imported by the existing [native physical regression root](../../DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda); no disconnected theorem graph.

This is a source-written, TYPE-INTENDED finite original F19/W0 candidate T transportation theorem and consumes NONE of the source-specific CMP119/122 physical missing lemmas. In particular W0 explicitly calls itself a candidate and does not prove \(\Omega,\Lambda,S\) (S inside T) or Faddeev-Popov/R/E/B/V, same-beta active-scale source history or original absolute W3. The connector GitHub saved/readback proves files were committed, **not** that an Agda kernel has typechecked this new module or its imported owners. Agda/Lean/Nix not installed in the local check environment. Local SymPy/mpmath/Python source tests verify finite mathematical formulas only. The next source payment is original CMP119/122 physical same-object identification and absolute connecting shell, not another fixed-cutoff F19 observation wrapper.
