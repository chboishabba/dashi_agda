# The world as a selected history: a speculative (3,1) Yang–Mills/KK steelman

**3 November 2026 — research conjecture, NOT a theorem, publication, experimental finding, or kernel-checked Agda result.** This paper is intentionally audacious. The Golden Agdas are the subsequent BS-test; no conditional source or finite test is promoted to full physics.

> **Companion implementation roadmap (3 November 2026):** [P00–P11: 176 individually numbered exact lemma obligations, dependencies, deliverables, checks and completion contracts](../roadmaps/Emergent31QuantumYMKKExactLemmaRoadmap20261103.md). This proposed article is the research hypothesis; the roadmap is its fail-closed mathematical test. #1444's new variable-periodic Haar code has **not yet been integrated** into the #1460 branch.

## Proposed theorem (the desired endpoint)

A reversible microscopic history algebra, with two admissible boundary conditions and a physically defined accessible-observer quotient, has a distinguished stable macroscopic sector. That sector reconstructs (i) a continuous, time-oriented causal manifold of dimension four with exactly one timelike direction, (ii) a positive complex quantum Hilbert space and strongly continuous one-parameter unitary dynamics, (iii) local gauge fields with an independent pure non-Abelian Yang–Mills continuum sector, and (iv) a same-metric, same-observable reflection-positive Euclidean realization whose Osterwalder–Schrader reconstruction has a strictly positive, infinite-volume gauge-invariant spectral gap. The lower-dimensional selected reductions recover their corresponding existing 2D and partial 3D field theories. A consistent *spacelike* fifth-circle effective extension reduces to the same (3,1) sector, including the associated scalars, radion and gauge sources, and a controlled pure-YM decoupling limit. Optional exotic gravitational responses arise from the same conserved effective stress, with ordinary positive Newton coupling.

Everything in that paragraph after “has” is a **candidate theorem**, not a presently established statement. The construction is specified below so that it can fail.

## 0. The one source

Choose a directed family of finite history/observable systems
\[
\mathfrak X_n=(\Omega_n,\Theta_n,\mathcal A_n,T_n,B_-,B_+,\pi_n),
\]
where \(\Omega_n\) is a finite microscopic history carrier, \(\Theta_n^2=1\) reverses admissible microscopic histories, \(\mathcal A_n\) is the local observable *-algebra, \(T_n\) is a reversible/source-symmetric evolution operator, \(B_\pm\) are selected boundary data, and \(\pi_n\) is the physically measured, lossy quotient. Refinement maps preserve the full microscopic source and admissible observations. The continuum is a controlled projective/inductive limit, **not** a silent declaration that any finite C3/369 model is spacetime.

The specific microscopic finite carriers can use DASHI C3, 369, Heisenberg/Weyl and history owners, but their arithmetic symmetry is **not** itself a proof that physical space has three dimensions or that SU(3) is the physical color group. These are proposed producers subject to the later source identification.

## 1. Time is the physical filtration's directional mode, not an extra coordinate postulated at birth

For a decoherent family of history operators \(C_\alpha\), initial density \(\rho_-\), terminal effect \(E_+\geq0\), define the two-boundary decoherence functional
\[
D_{B_-,B_+}(\alpha,\beta)
=\operatorname{tr}(E_+C_\alpha \rho_- C_\beta^\dagger).
\]
When the relevant histories decohere, the selected conditional probability is
\[
\mathbb P(\alpha\mid B_\pm)
=\frac{D_{B_-,B_+}(\alpha,\alpha)}
{\sum_\gamma D_{B_-,B_+}(\gamma,\gamma)}.
\]
The terminal effect changes hidden-history *smoothing* while the operational no-backwards-signalling theorem constrains accessible *filtering* outcomes. A conditional postselected subensemble is not an intervention-generated signal to its recorded past.

Let \(\mathcal F_\preceq\) be the actual accessible record algebra. The microscopic dynamics remains reversible, but the restricted family of conditional expectation maps \(E_{\mathcal F}\) can be non-invertible. The observed temporal direction is the unique direction in which accessible records compose under the selected positive transfer/filtration system. A thermodynamic entropy-production theorem is a **separate** statement. Finite depth/potential and MDL ranks do not automatically equal thermodynamic entropy; no strict descent is assigned to every microscopic reversal (a reversal fixed point makes this impossible in the existing finite history witness).

**One-clock hypothesis:** In the continuum physical sector, admissible operational traversals have one strongly continuous positive-energy generator. This condition must be derived from the source/refinement and independently compared with the causal order; it must not merely assume (3,1).

## 2. How (3,1) actually appears

Construct an operational causal relation \(p\prec q\) from the possibility of changing a record accessible at \(q\) by an intervention local to \(p\), while maintaining the no-backwards-signal constraint. For refinements \(n\), recover a locally finite causal event system with counting measure \(N_n\). Derive dimension by a calibrated interval-volume limit:
\[
N_n(I(p,q))\sim C_D \,\tau(p,q)^D,\qquad D=4,
\]
on a nondegenerate continuum causal domain. This *dimension result* is a physical target, not a choice of \(D=4\) in the definition.

Independently let \(h\) be the positive quadratic form on the three-dimensional stable transverse correlation subspace, and let \(\vartheta\) be the operational clock covector induced by the one-clock filtration. Construct the physical principal quadratic
\[
Q(v)=h(v_\perp,v_\perp)-c^2\vartheta(v)^2.
\]
Demand that \(h\) have exactly three positive eigenvalues, \(\vartheta\) be nonzero on the complementary clock line, and that **this same \(Q\)** be the principal symbol of the selected effective propagation operator. Thus \(Q\) has three spatial and one temporal directions and a nondegenerate null cone. The future half-cone is selected by the actual filtration, rather than by the arbitrary overall sign convention of the metric.

The local model is the candidate Lorentzian wave operator
\[
\mathcal P_{\mathrm{phys}}
=-c^{-2}\partial_t^2+\sum_{j=1}^3\partial_j^2
+\text{curvature/lower-order terms}.
\]
This is a proposed derivation by **unique stable hyperbolic propagation**; the independent \(D=4\) result, spatial isotropy, principal-symbol identification and uniqueness across physically admissible refinements remain crucial proof obligations. A preinserted \(\mathrm{diag}(-,+,+,+)\) is a regression fixture, not a physical proof.

**Why four might be the selected dimension:** The geometric dimension estimator and local hyperbolic selection must independently give \(D=4\); the physical non-Abelian gauge action then provides a separate scale diagnostic: \([g_D^2]=4-D\), so \(D=4\) is the marginal Yang–Mills dimension, with lower dimensions superrenormalizable and five-dimensional YM a cutoff-dependent EFT. This is a **consistency/selection hypothesis**, not a deduction of four solely from engineering dimensions.

## 3. Why the imaginary unit and Planck–Heisenberg–Schrödinger arise

On the real linearized fluctuation/phase carrier, derive a conserved nondegenerate symplectic form \(\omega\) and a positive bilinear form \(h_{\mathrm q}\). Define \(A=h_{\mathrm q}^{-1}\omega\). Under the requisite boundedness/nondegeneracy/positive-compatibility hypotheses, choose the polar complex structure
\[
J=A(-A^2)^{-1/2},\qquad J^2=-1.
\]
The multiplication operator represented by \(J\) is the quantum \(i\). It is **not** an extra physical time direction. Its compatibility with the microscopic reversible dynamics makes the selected Hilbert completion complex:
\[
\mathcal H=\overline{V/\ker h_{\mathrm q}},\qquad
\langle\psi,\phi\rangle=h_{\mathrm q}(\psi,\phi)+i\,\omega_{\mathrm q}(\psi,\phi)
\]
after fixing the compatible normalization and positivity.

The finite ternary Heisenberg/Weyl system supplies approximating operators \(W_n,V_n\) satisfying a central cocycle \(W_nV_n=\zeta_n V_nW_n\). A **strong, domain-controlled scaling limit**, rather than a finite qutrit alone, must supply the canonical pair
\[
[X,P]=i\hbar I.
\]
With one strongly continuous physical unitary group and Stone's theorem,
\[
U(t)=e^{-itH/\hbar},\quad H=H^\dagger,\quad H\ge0,
\qquad i\hbar\frac{d\psi}{dt}=H\psi.
\]
Planck's \(E=\hbar\omega\), Heisenberg's uncertainty bound \(\Delta X\Delta P\ge\hbar/2\), Schrödinger evolution and positive Born probabilities become faces of the same selected quantum representation. The **numerical value of \(\hbar\)** must be fixed by a valid SI/metrological authority, not derived by naming a discrete lattice size. The CCR and Hilbert/Stone sources remain open at their full continuum physical level.

## 4. From local quantum phase to QED and color

Local changes in the chosen phase frame \(\psi(x)\mapsto e^{i\alpha(x)}\psi(x)\) demand a compatible connection \(A_\mu\) and covariant derivative. The free electromagnetic sector and charged matter couple via an actual local \(U(1)\) representation and gauge-invariant action.

An independent admissible internal three-component complex fiber could carry a Hermitian form and determinant-one transformations, hence a candidate \(\mathrm{SU}(3)\) color connection:
\[
D_\mu=\nabla_\mu+ieA_\mu+ig_sG_\mu^aT_a+\cdots,\qquad
F_{\mu\nu}=[D_\mu,D_\nu]/g_{\mathrm{appropriate}}.
\]
An \(\mathrm{SU}(2)_L\) chiral sector and the Standard Model global quotient \((\mathrm{SU}(3)\times\mathrm{SU}(2)\times\mathrm{U}(1))/\mathbb Z_6\) require independent representation, anomaly, chirality, symmetry-breaking and empirical matching. **A ternary cell count does not derive QCD; a local phase alone derives neither full QED nor matter.**

The speculative claim is that all accepted gauge structures arise as consistent local automorphisms of the **same selected quantum observable algebra**. Distinguish U(1) massless photons from gapped gauge-invariant pure SU(3) excitations. Do not infer a QED mass gap from a QCD/YM one. Pure SU(N) Yang–Mills is an independent decoupling sector of the larger coupled model.

## 5. Exactly the selected Euclidean Yang–Mills cylinder, then OS, then mass gap

The Lorentzian source admits a reflection-positive Euclidean gauge-state family on the actual selected periodic four-dimensional lattice. For link matrices \(U_b\in\mathrm{SU}(N)\),
\[
d\mu_{a,L}(U)
=Z_{a,L}^{-1}
\exp\left[-\beta(a)\sum_{p}
\left(1-\frac1N\operatorname{ReTr}U_p\right)\right]
\prod_b dH_{\mathrm{SU}(N)}(U_b).
\]
This is **the actual variable-periodic Wilson family** from PR #1444, once the genuine compact continuous normalized one-link Haar, vector/bond decoder and real/Gibbs source are supplied. The worker's \`YMClaySUNVariablePeriodicProductHaarExact\` and \`YMClaySUNVariablePeriodicGaugeHaarExact\` give conditional finite-size normalization/positivity and gauge-observable transports, not yet physical measure construction.

Choose the SAME observed time reflection \(\theta\) from the candidate causal sector; prove
\[
\langle(\theta F)F\rangle_{\mu_{a,L}}\ge0
\]
for the admissible positive-time observable algebra and preserve this in the selected continuum limit. Recover actual Schwinger functions as \(a\downarrow0\), \(L\uparrow\infty\). OS reconstructs the **same** Hilbert time generator \(H_{\mathrm{OS}}\) and physical metric as the selected operational \((3,1)\) construction; Euclidean 4D and Lorentzian (3,1) do NOT follow from substituting \(t=i\tau\) alone.

The demanded gauge-invariant spectrum is
\[
\operatorname{spec}(H_{\mathrm{OS}})\subseteq\{0\}\cup[\Delta,\infty),
\qquad \Delta>0
\]
on the infinite-volume physical Hilbert space, with genuinely nontrivial interacting observables. Dimensional transmutation suggests \(\Delta\sim C\Lambda_{\mathrm{YM}}\); the RG relation is only motivation. The proof must supply the physical R443 Haar/CMP119 source, selected R445 cutoff and measure/tail convergence, R320 CMP116 mixed-source rooted-shell decay, and R333 uniform same-\(H_{\mathrm{OS}}\) gap/nontriviality. The Bałaban RG source and the Route-S owners remain separate upstream mathematical sources. This is the **Clay hard wall**; 2D/3D analogues do not pay it.

## 6. Fifth dimension as a spacelike fiber, not the time or imaginary axis

For the successful 3+1 base choose one spacelike compact fiber \(S^1\) of circumference \(\ell\). A candidate Lorentzian 5D EFT has
\[
ds_5^2=e^{-2\alpha\varphi(x)}g_{\mu\nu}(x)dx^\mu dx^\nu+
 e^{4\alpha\varphi(x)}(dy+\kappa B_\mu(x)dx^\mu)^2.
\]
The two gauge connections \(B_\mu\) (graviphoton) and \(A_\mu\) (non-Abelian YM) remain distinct, as do the radion \(\varphi\) and adjoint scalar \(\Phi=A_y\). Start from one covariant 5D Einstein–YM–matter effective action \(S_5[G,A,\Psi]\). A consistent zero-mode/low-energy reduction yields four-dimensional gravity, vector/scalar components and Yang–Mills with leading tree-level
\[
g_4^2=g_5^2/\ell
\]
in the fixed conventional normalization, plus renormalized thresholds from the omitted KK modes. A physical \(\ell\)-dependent mass tower obeys \(m_n^2=m_0^2+(2\pi n/\ell)^2\) when the background circle is flat and untwisted.

DASHI #1241 adds possible E6/trinification/global-quotient/anomaly and KK consumers, but **that branch is not a proof of a fully consistent physical E6 or 5D UV completion**. The 5D action is an EFT. The claimed 4D pure-YM Clay sector requires an explicit gravitational/KK/matter decoupling limit, not the assertion that its degrees of freedom are absent.

**Möbius possibility:** permit a \(\mathbb Z_2\) twist in an INTERNAL orientation or associated bundle around the compact circle. A field can obey \(\Phi(y+\ell)=\rho(\sigma)\Phi(y)\), \(\sigma^2=1\); the correct spin/global bundle and anomaly conditions are separate. A non-time-orientable Möbius-like **physical time** bundle would contradict the selected globally future-oriented (3,1) branch unless handled on an orientable double cover with a physically defined descent. Thus Möbius transport is a potentially useful holonomy/sector selector, not permission to flip the operational arrow globally. The repository \`MobiusOrientationGate\` is target-only, and “Möbius” also labels unrelated number-theoretic inversion in other repo modules.

## 7. Gravity, quantum history and controlled exotic responses

A single selected renormalized effective action \(W[g,A,\Psi;B_\pm]\) generates stress:
\[
T_{\mu\nu}^{\rm eff}= -\frac{2}{\sqrt{-g}}\frac{\delta W}{\delta g^{\mu\nu}},
\qquad
G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G_N T_{\mu\nu}^{\rm eff},
\quad G_N>0,
\]
with the chosen metric-variation sign convention and Ward/conservation identity. Two-boundary history sensitivity may modify \(W\), but a history label or entropy density is **not automatically** a physical stress source. A selected state can cause repulsion/defocusing if its renormalized pressure/energy support the correct active-stress sign and the solution passes the physical energy, regularity, and experimental constraints. The strongest antigravity sources are #1120 Local-C/Wightman direct typed stress and same-state four-channel metric, #1132 conditional history/birthmark stress sign, #1045 positive/negative-G comparative scope and #1284 non-promotion firewall.

Demand that **the same metric** predicts clocks, free fall, optical propagation and support forces. A scalar Kottler response is not a transverse-traceless gravitational wave. No negative universal Newton constant is needed for the candidate main theory.

## 8. Four-sector known results as adversarial witnesses, not extrapolation

- **2D:** Recover the legitimate pure-YM Wilson-loop area law in its known simple-loop/planar/representation/normalization scope, once the adjoint scalars and KK modes are consistently removed.
- **3D:** Recover the renormalized gauge-covariant local stochastic Yang–Mills–Higgs operator and the known counterterm constraints in their actual (partial) scope, not a fictitious global equilibrium theorem.
- **4D Euclidean:** Match selected finite compact Haar/Wilson/Gibbs sources and physical Schwinger functions to the real 4D YM continuum/OS source.
- **(3,1):** OS-reconstructed Hilbert time, observed causal order, physical metric and unitary generator agree as the SAME object.
- **5D/KK:** Physical action/stress/metric and Wilson observables agree with the matched low-energy 4D EFT, within proved KK threshold errors. A 5-Euclidean-axis lattice is a different physical construction.

The source of every equality is specified. An admissible mismatch must produce a numerical/scaling residual or an obstruction, not merely a “different regime” label.

## 9. Testable signatures of the completed proposal

1. An independent causal interval-volume estimator selects four dimensions; a separately derived principal symbol has three positive and one negative directions with an operational future cone. Fail if either is hard-coded or has wrong count.
2. A physical one-parameter transfer family yields a complex, positive Hilbert/CCR/Stone structure from the chosen micro dynamics, with \(\hbar\) independently metrologically calibrated. Fail on domains, positivity, or nonunitary evolution.
3. On the same physical Euclidean Wilson source, the exact finite variable-size product-Haar/gauge invariance is realized, the Schwinger continuum exists and is OS positive. Fail if the vector bond decoder or Haar source is fake, or if changing-cutoff limits disagree.
4. The selected \(H_{\mathrm{OS}}\) equals the positive Lorentzian generator and retains one uniform positive pure-YM mass gap at infinite volume. Fail on zero gap, triviality, wrong Hamiltonian or missing full Clay scope.
5. Correct 2D and scoped 3D source observables follow from controlled reductions. Fail if an adjoint scalar is dropped without proof or if threshold/coupling matching fails.
6. KK action, radion, graviphoton, gauge scalar, global chirality/anomaly and physical gravitational tests pass. Fail if the 5D EFT is claimed UV complete on dimensional grounds.
7. Möbius/internal twists leave the physical 3+1 base time orientable or define a lawful double-cover construction. Fail if a closed timelike orientation flip is silently declared to be the observer's arrow.
8. The same source action produces a conserved stress and one metric across clocks, light, free-fall and support-force channels. Fail if history-only labels are used as stress or if an anomaly is mistaken for repulsive geometry.

## 10. Repo receipt / attribution / scope

Existing original owners: \`FiniteHistoryOrientationExact\`, \`HistoryWeightFiltrationExact\`, \`TSFVFiltrationArrowLorentzBridgeExact\`, \`Signature31Canonical\`, \`Signature31FromIntrinsicShellForcing\`, \`CausalForcesLorentz31\`, \`LargePosetContinuumLorentz31\`, \`TSFVKKSameMetricTransportExact\`, \`CCRFromAdmissibleFlow\`, \`TreeHeisenbergScalingLimit\`, \`SchrodingerSelfAdjointEvolutionReceipt\`, \`MobiusOrientationGate\`, \`YMClaySUNVariablePeriodicProductHaarExact\`, \`YMClaySUNVariablePeriodicGaugeHaarExact\`, \`BalabanClayGate4CombinedRGUVIterationExact\`, \`BalabanClayConcreteUVToMassGapDependencyExact\`, \`YMClayFiveSectorBidiSteelmanExact\`, \`QCDRunningFromCarrierScaleReceipt\`, \`StandardModelGaugeCouplingAuthorityFrontier\`. No existing proof is re-attributed to this proposal.

Original scientific authors/sources retain priority: Planck, Heisenberg, Schrödinger, Weyl, von Neumann, Stone, Yang–Mills, Wilson, Bałaban, Osterwalder–Schrader, Kaluza–Klein, Aharonov/Bergmann/Lebowitz and Aharonov/Vaidman, rigorous 2D YM (Ashtekar–Lewandowski–Marolf–Mourão–Thiemann), stochastic 3D YM–Higgs (Chandra–Chevyrev–Hairer–Shen; Chevyrev–Shen), and the original gravitational quantum-field/renormalization sources. The speculative integration is a DASHI conjecture, not an attribution of established theorems to DASHI.

**PR stack:** #1440 Route-S -> #1444 finite variable-size Wilson/Gibbs/Haar conditional construction -> #1460 same-metric TSFV/KK, five-sector BIDI. Independent 5D KK/E6 #1241 and antigravity #1120/#1132/#1045/#1284 are not assumed merged. Latest #1444 head checked 2026-11-03: \`5bb34d44bac92dfe16544fcde07c65e37d875172\`. Source-written or owner-reported local tests do not imply an Agda compiler receipt.
