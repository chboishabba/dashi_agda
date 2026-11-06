## 2026-11-06 follow-on: finite original Wilson two-source jet (Y.01/Y.02)

**Golden source:** `DASHI/Physics/YangMills/YMClayOriginalWilsonFiniteTwoSourceJetExact.agda`, in parent [PR #1444](https://github.com/chboishabba/dashi_agda/pull/1444). **Independent exact reference:** `scripts/check_ym_original_wilson_two_source_jet_reference.py`. Canonical TOE import, dedicated physical root `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda`, and targeted Agda CI now name the two finite source owners. The physical root is deliberately not `--safe`, because the legacy real/Haar analytic authorities are a transitive proof boundary. No Agda kernel or transitive trust receipt has been observed.

| Exact ID | Source term | Status and remaining physical payment |
| --- | --- | --- |
| `Y.FIN.01` | `originalWilsonDensityIsSelectedWilson`, `originalWilsonPartitionIsSelectedProductHaar`, `originalWilsonFiniteIntegrationLaws`, `originalWilsonUnitNumeratorIsPartition`, `originalWilsonInsertionNumeratorAdd`, `originalWilsonExpectationOfUnitIsOne` | Source-written: literal changing-cutoff SU(N) Wilson/Gibbs density and partition are anchored to the *same* previously constructed finite product-Haar measure; finite numerator additivity and unit partition follow from existing cylinder algebra. The unit-normalization proof additionally takes an explicit positive-denominator division-cancellation law; one-link compact Borel Haar realization is still an explicit input. |
| `Y.FIN.02` | `originalWilsonMomentAlgebra`, `originalWilsonNormalizedJet`, `originalWilsonLiteralJetDirections` | Source-written: define the formal two-source coefficients directly from one original finite Wilson normalized expectation; no independent moment/covariance object. The *analytic derivative* of the actual continuous-Haar source functional is not inferred. |
| `Y.FIN.03` | `originalWilsonMixedJetIsSameFiniteCovariance`, `originalWilsonMixedJetIsOriginalConnectedCumulant` | Source-written: literal finite formal mixed-log jet equals the same Wilson connected covariance by the original cumulant compiler. Kernel acceptance pending. |
| `Y.FIN.04` | `check_ym_original_wilson_two_source_jet_reference.py` | Exact rational BIDI reference: 19,683 exhaustive three-state cases and six simultaneous relabelings; changed-measure negative control rejected. This is not an SU(N) Haar integration or Agda check. |

| `Y.FIN.05` | `YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact.originalVariableN3IsNativeR445FineMeasure`, `originalN3CumulantIsNativeBlockedFineCovariance`, `originalN3LiteralMixedLogJetIsNativeBlockedCovariance`, `originalN3LiteralMixedLogJetIsActualR320PushforwardCovariance` | Source-written: at actual side-four n=3 the variable-cutoff Wilson measure is definitionally the original R445 1024-link fine Gibbs law. Both source marks pull back along the original non-Abelian native block; the finite jet equals the actual *weighted* R445→R320 pushforward covariance. No bare-coarse Wilson-law assertion or analytic CMP116 source bound. Kernel pending. |

**Revised original physical max-cut (do not promote from Y.FIN):** `Y.01` identify the entire real Wilson/gauge-fixed E/R/B/V/ghost/counterterm source with the selected CMP119/122 density/physical T-operation at every renormalization scale, not just the original finite Wilson action. `Y.02` prove that selected positive-time gauge-invariant local/loop insertions are admissible CMP119/116 analytic J directions, identify the genuine differentiated `log Z` with this formal jet, and preserve root/distance/normalization. `Y.03` derive *actual* cutoff/volume-uniform source decay, RG/continuum tails and reflection-compatible limits. `Y.04` construct the same limiting OS Hilbert/Hamiltonian and quantitative nontriviality/Clay scope. Reuse the CMP119/122/116, R344/R467/R482, Bishop/T5 and original Wilson–Gibbs owners rather than copying them.

**Acceptance:** new formal theorem = `SOURCE_PENDING_AGDA`; reference arithmetic = `VERIFIED_REFERENCE`; original CMP116 source applicability and physical estimates = `OPEN_PHYSICAL`. CI is a checker command, not a green receipt. Parallel-checker exact-head execution and transitive axiom audit remain required.

---


### 3a. Exact real/Bishop-facing nonGaussian compiler interpretation

The golden \`YMClayRGLossBudgetToNonGaussianExact.agda\` has now been sharpened: the rational \(c_n\) is **a certified numerical lower enclosure**, NOT an assertion that a continuous Wilson–Gibbs cumulant is rational. \`ActualRGContinuumChargeLimit r Scalar\` is parameterized over the actual continuum \`Scalar\` (intended to be the vendored Bishop/fast-Cauchy completion), with \`actualFiniteCumulant : Nat→Scalar\`, order-preserving embedding \`embed : ℚ→Scalar\`, and the required original-source witness
\[
\operatorname{embed}(c_n)\le \kappa_{4,n}^{\text{actual}}(O_{f_1},\ldots,O_{f_4}).
\]
A *single derived* proof \`referenceRGUniformNoncollapse\` supplies \(\eta\le c_n\). Its composite with \`selectedFiniteChargeLower\` yields the **actual** \(\operatorname{embed}(\eta)\le\kappa_{4,n}^{\rm actual}\); then true same-source finite-cumulant convergence and a closed interval in the completed real order feed the ORIGINAL T5 nonGaussian theorem. This avoids the important false move of identifying a rational interval certificate with a physical real expectation. Exact Agda/physical instantiation remains subject to receipts.

---

# YM Clay — constructive 4D continuum steelman and same-source BIDI programme

**Date** 2026-11-06. **Owner** YM PR #1444 (R443/R445/R320/R333 + Clay). **Status** mathematical conjectural programme with real finite and conditional Agda components, not a claimed Millennium solution. **Companion** [exact phase / deliverables ledger](../roadmaps/YMClayExecutionPhasesDeliverablesExactLemmas20261106.md). This is **not** an observer→Lorentz/KK construction: those belong to #1460. Do not import #1460 into the #1444 parent.

## 0. Strongest imagined theorem

For **each prescribed compact connected simple** gauge group \(G\), choose a faithful finite-dimensional unitary representation \(\rho_G\), normalized Wilson plaquette character, and selected renormalized running coupling \(g_G(a)\) fixed by one physical reference-scale condition. Define
\[
a_n=2^{-n}a_0,\quad
d\mu^G_{n,L}(U)=Z_{n,L}^{-1}\exp[-S^G_{\rm Wilson,n,L}(U)]\prod_{e\in E_{n,L}}dH_G(U_e).
\]
For SU(N), \(\beta_n=2N/g_G(a_n)^2\), tending to infinity in the UV along the asymptotically free trajectory. That by itself is *not* the contraction hypothesis. We propose to prove all of the following **for that same family**:

1. A source-renormalized gauge-invariant local observable algebra \(\mathfrak A_G^{\rm phys}\), with one fixed physical renormalization prescription and selected reflected positive-time domain.
2. A uniquely selected Schwinger functional \(S_G\) obtained from \(\mu^G_{n,L}\) with explicit UV and IR error moduli, whose normalization, gauge invariance, reflection positivity, Euclidean covariance, regularity, temperedness, locality and Ward/stress semantics survive the same limit.
3. A **noncollapsed interacting** OS sector, e.g. at least one reflected local OS norm \(\|[O_f]\Omega\|^2\ge\eta_2>0\) and one same-source connected fourth cumulant (with selected sign) \(|\kappa_4(f_1,\ldots,f_4)|\ge\eta_4>0\) at fixed nonzero physical resolution.
4. For the reconstructed *same* Hamiltonian \(H_G\) and full gauge-invariant physical excitation sector,
\[
  \mathrm{spec}(H_G|_{\Omega^\perp})\subseteq[m_G,\infty),\qquad m_G>0.
\]
5. The compact-simple-group quantifier: construct each group's physical witnesses; constants may depend on \(G\). Do not infer all groups from an SU(2) quaternion or SU(N) matrix example.

The theorem would prove the constructive nontrivial continuum Clay endpoint if **all** physical hypotheses below are paid. Until then, it is a falsifiable proof programme.

## 1. Existing actual source donors — reuse, do not reconstruct

| Lane | Golden repo owner | Concrete value | Physical weld needed |
|---|---|---|---|
| R443 Wilson field, Haar/Fubini and C3 | `YMClaySUNVariablePeriodicProductHaarExact`, `YMClaySUNMatrixSpatialC3RealFubiniExact`, `YMClayNativeClosedThreeEqualitiesCandidateExact` | Native side-four six-plane Wilson, finite normalized one-link product-Haar and source-written original C3 1024-bond certificate | Genuine SU(N) Borel Haar on original matrix test algebra; transitive kernel; full E/R/B/V action |
| R445 non-bare physical block pushforward | `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact`, `YMClaySUNWeightedDisjointPairFibreReparamExact`, `YMClayNativeSideFourTwoLinkPairSameObjectExact` | Original Wilson weighted pushforward functional and 64-pair + 896-spectator Fubini change | Same measurable regular conditional, scale-general original decoder and RP compatible physical block |
| CMP119/CMP122 perturbative UV | `BalabanBetaDrivenCMP119FunctionalOperatorExact`, `BalabanPublishedUVStabilityNonlinearRGCoreExact`, `BalabanCMP122PublishedFourDimensionalUVStabilityExact` | Selected E/R/B/V RG operator/finite-volume and published-source stability interfaces | Show chosen original running coupling and renormalized sources satisfy the published hypotheses at all physical scales, including large fields |
| Continuum Cauchy *already in Bishop-style completion* | `BalabanClayT5TypedContinuumDefectCauchyExact` | Dyadic absolute one-step defect + SAME-observable telescope gives an actual FastCauchyReal of selected rational expectations | Construct one-step original renormalized Wilson defect and typed telescope; do not postulate a generic limit |
| Compactness | `BalabanClayT5Path4ToSelectedDiagonalTightnessRound433Exact`, `BalabanClayT5BoundedWeakCompactnessRound439Exact`, `BalabanClayT5MarkovToProkhorovTightnessExact` | Path4 coercive/Markov → compact containment → Prokhorov/unique selected limit | Original physical energy/expectation semantics and true compact sublevels of the selected configuration topology |
| RP and OS, same continuum | `BalabanClayOSWilsonReflectionPositivityExact`, `BalabanClayT5SameFamilyContinuumRecoveryRound425Exact`, `BalabanClayT5OSReconstructionCyclicityExact` | Link-plane and site-plane positivity authority, finite Gram → continuum Gram, same-family OS recovery and dense local vectors interface | Literal original Wilson weight, preserved positive-time support, true OS reconstruction and strong semigroup |
| CMP116 source and positive gap | `BalabanCMP116PublishedLiteralSelectedRound467Exact`, `BalabanCMP116PublishedLiteralToGapRound479Exact`, `BalabanCMP116ModeSelectedSubgapClusteringBidiExact`, `YangMillsDirectSourceOSSameHGapExact` | Same mixed-J derivative ABI, rooted-shell envelope→selected gap and same-H consumers | Actual uniform source theorem, time-to-distance and dense full physical spectral coverage |
| Nontriviality | `BalabanClayPlaquetteNoncollapseContinuumCalibrationExact`, `BalabanClayT5CumulantLowerBoundNontrivialityExact`, `BalabanContinuumNontrivialityAsymptoticFreedomGateExact` | OS-norm 1/16→1/32→1/64 calibration, finite uniform cumulant lower→continuum non-Gaussian; AF survival margin | One actual selected observable, original physical covariance/cumulant lower bound and limit identity |
| Finite→infinite dimension controls | `YMClayVoyagerDimensionSignatureForkExact`; in separate #1460: `YMClayFiveSectorBidiSteelmanExact` | 2/3/4/5-dimensional coupling dimensions, explicit cross-fibre curvature loss | Keep distinct 4D action and spectrum. 5D KK is NOT a continuum YM proof |

## 2. One effective-action mechanism for four results

**My strongest conjecture (not a known established theorem):** there is a tuned, gauge-covariant stable renormalized manifold in the true R445 blocked Wilson measures. At UV scale \(a_n\), decompose the selected effective action
\[
S_{n}^{\rm eff} =
 \frac{1}{4g_n^2}\int\mathrm{tr}F^2+
 \sum_{\alpha}\lambda_{\alpha,n}\mathcal O_\alpha
 +\sum_{X}K_n(X;J).
\]
This is a *schematic chart* of the actual non-bare R445 effective density, not a claim that an exact compact-link action already equals the displayed continuum expression. Preserve the exact original action in the source. Gauge/BRST/Ward constraints tune or exclude forbidden relevant operators; \(g_n\) is marginally running.

We seek a single **weighted, differentiated, two-marked polymer norm**
\[
\|K_n\|_{\rm phys} =
 \sup_{J,\;\text{source supports}}\
 \sum_{X\ni x} |K_n(X;J)|\,
   e^{\sigma\,{\rm length}_{\rm phys}(X)}
   \mathrm{cost}_{\rm sources}(X,J)
\]
whose precisely defined norm controls one-step effects, boundary/IR tails, physical connected \(J\)-responses, and fourth-source cumulant stability. The source cost must use CMP116's actual mixed-\(J\) derivative class, not an invented covariance.

Suggested testable multiscale inequality (the central research wager):
\[
\|P_{\rm irr}K_{n-1}\|_{\rm phys}
 \le \theta\|P_{\rm irr}K_n\|_{\rm phys}
    +C_G g_n^{p}+\mathcal E_{n}^{\rm holes/large\ field},
\qquad 0<\theta<1.
\]
The marginal direction is **not** assumed contractive. At UV, perturbative flow is
\[
g_{n+1}^2=g_n^2-2b_0(G)\log(2)\,g_n^4+O(g_n^6),
\quad b_0(G)=\frac{11C_2(G)}{3(16\pi^2)}>0.
\]
The physical gap comes from matching to a finite physical \(\ell_*\) and a nonperturbative terminal-scale rooted-cluster contraction, **not** from extending the bare \(\beta\ll1\) estimate into \(\beta(a)\to\infty\).

Do not replace generated multi-loop interactions by the bare Wilson action. The original R445 fibre density is non-bare and must be retained.


## 2a. Specific four-dimensional AF improvement — subtract marginal drift, then sum \(g^4\)

**This is the nontrivial falsifiable conjecture I favor:** the *same-source renormalized* observable error after solving the marginal running-coupling and source-anomalous-dimension equations can be bounded by
\[
|\delta_n(F)| \le
\frac{A_F}{(n+1)(n+2)}+
C_F\,2^{-(n+1)}+h_{F,n},
\qquad \sum_{n\ge0}h_{F,n}\le H_F.
\]
Why target this and not a generic geometric gap? In 4D asymptotic freedom the inverse squared coupling grows linearly with UV depth if the exact \`BalabanYM4RunningCouplingDriftExact.inverseCouplingRobustPositiveDrift\` source hypotheses hold, hence \(g_n^2=O(1/n)\) but \(g_n^4=O(1/n^2)\). The order-\(g_n^2\) unrenormalized correction has a divergent harmonic history; a properly subtracted order-\(g_n^4\) remainder is summable. The repo's \`BalabanBetaHistoryLocalizedInfluenceExact\` already warns not to force exponential forgetting on the marginal coupling and reserves geometric decay for the irrelevant-memory channel. This is exactly the split demanded here.

Algebraically, for all \(N\),
\[
\sum_{n=0}^{N-1}\frac{1}{(n+1)(n+2)}=1-\frac1{N+1},\qquad
\sum_{n=0}^{N-1}2^{-(n+1)}=1-2^{-N}.
\]
Consequently the original physical RG influence family satisfies one \(q<1\) if the *actual source-specific* coefficients satisfy
\[
\kappa_0\le q_0,\quad
\kappa_{n+1}\le\kappa_n+\delta_n,\quad
q_0+A+C+H<1.
\]
An explicit **toy BIDI arithmetic certificate** chooses \(q_0=1/4\), \(A=1/16\), \(C=1/32\), \(H=1/64\), producing \(q=23/64\), with exact rational checks through 512 refinements and a harmonic counterexample. The solver is \`scripts/check_ym_marginal_subtracted_uv_tail.py\`. These numbers are **NOT fitted to Wilson SU(N)** and are not physical facts.

To turn this into a theorem, prove the actual O(g⁴) remainder on the original CMP119/CMP122 T-operation and all conditioned boundary sectors, including large-field holes; show the selected marked-J source-renormalization and Ward identities really cancel the O(g²) marginal insertion and that the resulting operator norm controls the full original physical two-marked CMP116 weight. If this fails, use the direct original CMP116 rooted-shell route rather than choosing smaller constants.

## 3. Four source-native estimates (the actual theorem cut)

**A. Full UV observable convergence.** For the same renormalized positive-time test \(F\) at all \(n\), uniformly over admissible physical volumes:
\[
|\mathbb E_{\mu_{n+1,L}}F_{n+1}-\mathbb E_{\mu_{n,L}}F_n|
 \le A_F\,2^{-\alpha n},\quad \alpha>0.
\]
This is the actual missing input of `BalabanClayT5TypedContinuumDefectCauchyExact`. It supplies fast-Cauchy/Bishop expectation data once telescoping semantics are proved. To lift from selected rational approximation to completed real expectation use the already-owned completion, then R433/R439 and R425 for measure/OS same-object recovery. We should NOT demand a second generic measure limit.

**B. IR/two-marked rooted-shell estimate.** For any physical \(R=\mathrm{dist}(\mathrm{supp}F,\partial\Lambda_L)\),
\[
|\mathbb E_{\mu_{n,L'}}F_n-\mathbb E_{\mu_{n,L}}F_n|
 \le B_F e^{-\mu R}.
\]
Use `BalabanClayT5PhysicalRootedShellInjectionExact`, `BalabanClayT5TwoMarkedConnectedClusterTailExact`, `BalabanClayT5PhysicalTwoWeightKoteckyPreissExact`; prove actual absolute connecting-cluster weight inequality with holes and large-field domains. No assumption that a source-free one-marked tail controls a connected two-marked response.

**C. Actual literal CMP116 source bound.** For every declared selected physical test and the *original* \(Z_{n,L}(J)\),
\[
|D_{J_F}D_{J_G}\log Z_{n,L}(0)|
 \le C_{F,G}e^{-m\,d_{\rm phys}(F,G)}
\]
with \(m>0\) **uniform in both** \(n,L\), including continuum-scale source normalization. Reuse R467's `literalSelectedCMP116Localization` and `sourceEnvelopeBelowPhysicalClusteringEnvelope`, or direct R342→R467 compiler if source-native. Preferred terminal physics is source localization/KP; weighted block Dobrushin \(\|C^{n,L}\|_w\le q<1\) is a **backup sufficient criterion**, not an additional mandatory gate.

**D. Noncollapsed interacting witness.** For one selected reflected positive-time curvature composite \(O_f\), prove
\[
\|[O_f]\Omega\|_{\rm OS}^2\ge\eta_2>0
\]
and for a selected fourth cumulant with a fixed sign \(s_f\in\{-1,+1\}\),
\[
s_f\kappa_{4,n}(O_{f_1},O_{f_2},O_{f_3},O_{f_4})\ge\eta_4>0.
\]
The 4pt sign MUST be selected by the actual Wilson source; equivalently prove \(|\kappa_4|\ge\eta_4\) and a stable sign. `BalabanClayPlaquetteNoncollapseContinuumCalibrationExact` already proves 1/16 − 1/32 − 1/64 = 1/64, conditioned on original Gaussian, interaction and cutoff errors. `BalabanClayT5CumulantLowerBoundNontrivialityExact` already promotes a **finite uniform** fourth-cumulant lower bound to non-Gaussian continuum. New `YMClayRGLossBudgetToNonGaussianExact.agda` attempts to *derive* that finite uniform lower input from one reference charge and bounded losses:
\[
c_0\ge\eta+B,\quad c_n\le c_{n+1}+\delta_n,\quad
\sum_{k<n}\delta_k\le B\quad\Longrightarrow\quad
c_n\ge\eta\quad(\forall n).
\]
It then compiles the result into the existing original T5 non-Gaussian theorem. This is algebraic/conditional and needs pinned Agda acceptance.

**Physical source matching requirement:** every inequality must refer to the same \(G,\mu_{n,L},S_{\rm Wilson},Z_{n,L},g_n,\mathfrak A^+,\ell_*\), and source-label map. A family of unrelated finite models satisfying each inequality separately has no Clay meaning.

## 4. Reflection positivity, Euclidean invariance, and locality: do not manufacture them

The original finite Wilson measure has a standard link/site-plane RP proof (Menotti–Pelissetto source recorded in repo). For \(F\) in the *actual positive-time gauge-invariant algebra*, reflected \(\mathbb E_{n,L}[(\Theta F)^*F]\ge0\). A limit of complete finite reflected Gram forms preserves positivity provided their entries converge and the same positive-time algebra survives the limit. `BalabanClayT5SameFamilyContinuumRecoveryRound425Exact` is the chosen owner.

**BIDI test:** gauge fixing or a temporal smearing across the reflection plane may break the selected positive-time test class; a positive Gibbs density or reflection-compatible density equality is not by itself RP. Preserve the original ungauge-fixed measure in the positive-time OS route. Spatial-only or suitably supported time-separated probes can be safer at finite regularization.

Hypercubic symmetry is not \(E(4)\). For each rotation/translation \(h\) of a smooth physical test, prove
\[
|\mathbb E_{n,L} F_n-\mathbb E_{n,L}(hF)_n|
   \le C_{F,h}a_n^\zeta+\mathcal B_{L,F,h},
\qquad\zeta>0,
\]
after correct renormalized source matching; then remove the errors. Path4/Poincaré, the selected C3 six-plane case and first-variation/stress/Ward donors are valuable geometry, but C3 alone does not give continuous rotations. Establish locality of composites and their distributional test topology as separate consequences of the uniform physical source bounds.

**Local field choice:** bounded holonomies/Wilson loops are good for a first countable projective observable subsequence, but their boundedness alone may yield a trivial/perimeter-collapsed limit. To recover local curvature, use source-normalized shrinking loops, transported/renormalized \(F_{\mu\nu}^2\), or an equivalent gauge-invariant distributional field; prove its tightness and tempered test-space continuity. Fixed nonzero physical spatial smearing radius is a control stage, not automatically a local point field. 

## 5. Same \(H\), actual spectral gap

Once A–C give same-family convergence of every reflected pair needed for a dense OS core, set \(\mathcal H_{\rm OS}=\overline{\mathfrak A_+\Omega/\mathcal N}\), prove the selected physical Euclidean-time translation gives a strongly continuous positive contraction semigroup \(T(t)=e^{-tH_{\rm OS}}\), and derive for dense centered local \(F\)
\[
0\le\langle F\Omega,T(t)F\Omega\rangle
 \le C_F e^{-mt}.
\]
The positive spectral measure \(\nu_F\) then has no support below \(m\); density eliminates an invisible subgap sector. Existing `BalabanCMP116PublishedLiteralToGapRound479Exact`, `BalabanClayT5OSReconstructionCyclicityExact` and `YangMillsDirectSourceOSSameHGapExact` should finish that *implication*. This proves a physical gap only when (i) the marked-source spatial bound is correctly converted to **physical OS time**, (ii) the selected semigroup is positive, and (iii) the dense core detects every excitation. Do not apply a graph metric without its time calibration.

A different free-scalar OS control, finite transfer matrix, flat KK model or an invented generator \(H'\) cannot be substituted for \(H_{\rm OS}\).

## 6. 2D / 3D / 5D donors and falsifiers

The #1460 `YMClayFiveSectorBidiSteelmanExact` establishes exact 10→6→3→1 curvature-plane accounting and an explicit nonzero cross-fibre counterexample. Reuse this as a falsification test: projecting a 5D gauge action onto 4D does **not** preserve the measure and physical Hamiltonian if the discarded four cross-fibre planes carry nonzero action. 2D/3D heat-kernel, Markov and stochastic results are candidate *techniques* for conditional/compactness bounds; their different canonical coupling dimensions mean they cannot be directly lifted to the marginal 4D theory. Keep Lorentz/TSVF/KK identification on #1460, not as a prerequisite to proving #1444 YM.

## 7. Concrete bidirectional adversarial programme

- **Forward UV:** original Wilson source → exact R445 blocked effective density → one-step expectation defects → fast-Cauchy/Bishop completion → selected R425 continuum → OS Hilbert.
- **Forward IR:** same R445 marked \(J\) → two-marked CMP116 shell weights → uniform physical exponential envelope → selected R479→R333 gap.
- **Forward interaction:** same physical \(J_f\) and Ward-normalized local composite → one reference nonzero OS charge and fourth cumulant → RG loss budgets → original T5 continuum non-Gaussian witness.
- **Backward OS:** for any proposed \(H\), test the exact reflected Gram matrix and Hankel moment positivity; check \(e^{-tH}\) returns the **same** selected Wilson source correlators, not merely similar dimensions or a spectral gap.
- **Backward gauge:** gauge invariance, Ward/stress and all selected six plaquette planes must hold on the actual original fields; test coordinate rotations not generated by the finite C3 subgroup.
- **Backward universality:** repeat parameterized source proofs for each prescribed compact simple \(G\) using its faithful representation, conjugation class and \(C_2(G)\); do not assert \(G\)-independent numerical constants without a separate proof.
- **False-positive controls:** small β only, q(a)<1 pointwise but sup q(a)=1, disconnected polymer bound applied to a connected cumulant, nonzero two-point Gaussian control with vanishing \(\kappa_4\), pointwise positive correlations with non-PSD OS Hankel Gram, raw Wilson loop perimeter collapse, and source split into two non-unitarily-equivalent Hamiltonians. These controls must fail.

## 8. Exact max-cut / next executable leaves

| ID | Exact source-physics lemma | Required output |
|---|---|---|
| CLAY4.F1 | Three native source 1024-bond equalities `YMClayNativeClosedThreeEqualitiesCandidateExact` | Actual kernel certificate, no normalized `refl` timeouts; source trust |
| CLAY4.A1 | Original same-renormalized-source `T5.TypedContinuumDefectCauchyData.oneStepDefectAbsoluteBound` | UV dyadic bound on original \(F_n\) at all physical volumes |
| CLAY4.A2 | `telescopingExpectationDifferenceExact` for the actual renormalized observable | Original Wilson E difference = true finite signed defect sum |
| CLAY4.A3 | Physical Path4 moment/coercive compact sublevels and determining bounded tests | Original Prokhorov/R439 continuation, or direct completed-expectation uniqueness |
| CLAY4.B1 | Original two-support CMP116 connecting cluster expansion and absolute weight sum | Physical \(B_F e^{-\mu R}\) uniformly in \(n,L\) |
| CLAY4.C1 | R467 `literalSelectedCMP116Localization` | Literal original two-J log Z derivative uniformly localized |
| CLAY4.C2 | R467 `sourceEnvelopeBelowPhysicalClusteringEnvelope` | Physical time rate + prefactor and source norms |
| CLAY4.D1 | One selected Wilson plaquette local OS Gaussian floor and interacting error budget | \(\eta_2>0\) on SAME reconstructed OS vector |
| CLAY4.D2 | New `YMClayRGLossBudgetToNonGaussianExact.referenceRGUniformNoncollapse` | 4th-cumulant signed charge survives UV finite stages from q0 + loss budget |
| CLAY4.D3 | New `asOriginalT5Nontriviality` plus T5 cumulant convergence | \(\eta_4>0\) non-Gaussian continuum, same \(J\) |
| CLAY4.E1 | Original finite Wilson RP, continuous geometry/E(4), regular/tempered Ward/stress | R425 continuum OS core from SAME measure, no source-replacement |
| CLAY4.E2 | R333 same dense OS time semigroup and R479 full spectral conclusion | strictly positive \(m_G\) in physical units |
| CLAY4.E3 | Compact-simple-group quantifier + no hidden source/representation switch | selected actual \(G\)-wise witnesses to full Clay endpoint |

**Acceptance codes:** `PROPOSED_TEST` (mathematical hypothesis), `SOURCE_PENDING_AGDA`, `REFERENCE_EXACT`, `KERNEL_ACCEPTED`, `PHYSICAL_SOURCE_PROVED`, `CLAY_ENDPOINT_PROVED`. Do not turn `SOURCE_PENDING_AGDA` or `REFERENCE_EXACT` into the last two.

### Algorithm — same-family maximum-cut execution

```text
for each selected compact simple group G:
    choose faithful rep, original Wilson Haar/action and physical g_R(ell*)
    pin original bond/link source, normalization and +time algebra

    for each UV refinement n and physical volume L:
        derive (not assume) original R445 blocked weighted density
        construct same-source effective action including generated terms
        prove UV one-step delta_{n,L}(F), two-marked CMP116 polymer tail
        prove boundary/IR tail, Ward/rotation/locality defects
        construct selected RG OS-charge and fourth-cumulant deficits

    certify summability uniformly in n and L (Bishop-fast-real producer)
    certify positive-time reflected Gram convergence and E(4) limit
    certify nonzero OS norm and one signed nonzero fourth cumulant
    instantiate original R467 selected marked-J response with physical time
    reconstruct exactly ONE OS H and exclude every subgap vector
    validate SAME SOURCE both ways and per-G original action
```

**Highest alpha:** do not redo finite Haar, Fubini, Prokhorov, Markov, OS implications, or generic KP mathematics. Pay **the original-source one-step defect**, **literal two-marked CMP116 absolute tail**, **one reference noncollapse + UV loss**, **physical metric/OS test class**. These are mutually coupled enough to drive the continuum result without six disconnected arbitrary records.

## 9. Independent exact controls

`scripts/check_ym_rg_noncollapse_steelman.py`: 192 exact rational refinements, five rejection controls, 64 exhaustive small signed-charge fixtures. `scripts/check_ym_clay_continuum_bidi_controls.py`: 4x4 OS Hankel principal-minor necessary condition, physical transfer geometric bound, 128-stage RG noncollapse, seven false-positive controls. These are test harnesses **only**, no claims of original 4D Wilson inequalities or Agda acceptance.

**Next acceptance:** pinned `agda` for every new golden module and TOE root, exact original Wilson/CMP116 witness lemmas, independent physical proof receipts, full trust audit. No CI run has been observed for the newly added code at the time of writing.
