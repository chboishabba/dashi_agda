# OCT369 P0.38 — True continuous SU(3) Haar fibre pushforward into a native Wilson observable

**22 November 2026 — P0 MAX-CUT, source-owned.** 96/96 locally executed exact SymPy assertions on the selected **finite two-layer interval slab**. This is a controlled *new local source-specific integration*, not a reconstruction of the pre-existing 5D KK/E6 gauge theory or original 4D SU(N) Wilson/Gibbs/OS programme. No original repo Agda kernel or CI was run. **No 5D full circle, 4D continuum YM, continuum gap, gravity modification or levitation is proved.**

## Original owners, and what is actually new

- **Original 5D non-Abelian candidate:** KK/E6 #1241, `Docs/physics/KKE6TrinificationInteractingActionParityVacuumMaxCut20261024.md`, real 5D local interacting EFT with `SU3c × SU3L × SU3R × U1_B`, charged Dirac matter, physical scalar and two-VEV Higgs source, plus KK metric and parity/CS. E6/Albert #1106 owns associated 27/78/VEV/group data. This is not merely a single abelian metric KK field. The colour `SU3c` Yang–Mills connection is **distinct** from the 5D KK-metric graviphoton `U1` and the independent `U1_B`.
- **Original 4D Yang–Mills owners:** #1444 and current #1536, `YMClayOriginalWilsonTwoPlaquetteMarkedSourceExact.agda`, `YMClayOriginalWilsonNativeOSPullbackExact.agda`, R445 E1/W1/W3/F19 and CMP116/119/122 OS/source machinery. Their actual source is a full 4D finite periodic SU(N) link measure, not the one plaquette in this diagnostic. `YangMillsDirectSourceOSSameHGapExact.agda` still requires an inhabited literal CMP116/OS spectrum and positive gap; source-written conditional compiler does not close Clay.
- **Earlier OCT369 P0.37:** existing non-Abelian finite classical Wilson restriction, mixed SU3 fifth plaquette, correct tree-level `1/g4²=L/g5²` and Feshbach/nonuniform-gap counterexamples. Its previous (4/7,3/7) fibre marginal was an explicitly declared **two-state toy**, not actual continuous SU3 Haar.
- **External prior art**: Schur/Haar character orthogonality, Weyl integration, Wilson lattice gauge theory, standard higher-dimensional Yang–Mills and dimensional reduction, Osterwalder/Schrader. Original publication/theorem authors retain discovery; the precise bounded local fifth-source comparison on DASHI source carriers and audit is the OCT369 integration.

## Physical geometry — first check that the source is the right object

Take **two copies of one square plaquette** (layers `y=0,1`, four spatial vertices, four independently oriented group links `U_e^0,U_e^1` on each layer), plus four genuinely distinct fifth-direction SU(3) links `W_v` connecting corresponding vertices. **This is a 5D interval/slab regularization, not a periodic `S¹` circle**. It is a deliberately selected local cell of a potential 5D lattice discretization; it is not the entire #1241 quantum partition function. For oriented edges `e:v→v+1` modulo 4:

\[
P_0=U^0_0U^0_1U^0_2U^0_3,\qquad
P_1=U^1_0U^1_1U^1_2U^1_3,
\]

\[
Q_e=U^0_e W_{e+1}(U^1_e)^\dagger W_e^\dagger.
\]

With independently selected `g^0_v,g^1_v∈SU3`, transforming `U^l_e→g^l_v U^l_e(g^l_{v+1})†` and `W_v→g^0_v W_v(g^1_v)†` sends `Q_e→g^0_v Q_e (g^0_v)†`. All ten gauge/trace square checks use explicit noncommuting exact SU3 Cayley-rotation matrices.

The selected compact and *well-defined finite* source is

\[
Z_5(\beta_0,\beta_1,\eta)=\int\prod_{e=0}^3 dU^0_e\,dU^1_e
\prod_{v=0}^3dW_v\;
\exp\left[\frac{\beta_0}{3}\mathrm{ReTr}P_0+
\frac{\beta_1}{3}\mathrm{ReTr}P_1+
\frac{\eta}{3}\sum_{e=0}^3\mathrm{ReTr}Q_e\right].
\]

All Haar integrals are actual **normalized continuous SU(3) Haar integrals**, not the subgroup/finite toy. The source uses standard Wilson plaquette weights up to the configuration-independent `-β` normalizer. The 4D reference is exactly the **local** Wilson measure on `U^0_e`, NOT yet the actual full cutoff-`n` R445 original measure. Positive finite integrand and a compact domain guarantee a finite strictly positive fibre integral.

## First truly integrated fibre source, with independent SU(3) Haar checks

Fix the bottom physical links and integrate **all eight remaining link variables**:

\[
K_{\beta_1,\eta}(U_0)=\int\prod_e dU^1_e\prod_vdW_v\;
\exp\left[\frac{\beta_1}{3}\mathrm{ReTr}P_1+
\frac{\eta}{3}\sum_e\mathrm{ReTr}Q_e\right].
\]

This is an *actual* fifth-direction quantum-source marginal, unlike imposing `W=I` and dropping the spectator links. By local Haar gauge covariance, `K` is gauge-invariant as a function of the bottom links. It is exactly constant when `η=0` (independent sheets), and on this **open interval slab** it is also constant for any `η` when `β1=0` (independent upper link integration absorbs each bottom link; a compact periodic fifth dimension needs a separate treatment).

The key nontrivial Wilson geometry is a 4-edge loop. Using the exact Schur orthogonality

\[
\int_{SU(3)} W_{ij}\overline{W_{kl}}\,dW=\frac{\delta_{ik}\delta_{jl}}3,
\]

one insertion of each appropriately oriented mixed plaquette gives

\[
\int \prod_{v}dW_v\;\prod_{e=0}^3\mathrm{Tr}Q_e
=\frac{\mathrm{Tr}P_0\,\mathrm{Tr}P_1^\dagger}{3^4}.
\]

This is verified again by an **independent summation over `3^8` colour-index possibilities** for two different sets of original-type noncommuting SU3 external links. Subsequent normalized upper-link Haar integration gives `∫TrP1†TrP1=1`, and center-character symmetry gives `∫(TrP1)^2=0`.

For independent verification rather than merely assuming those moments, the program also evaluates six exact **continuous SU3 Weyl integrals** on the maximal torus `z1*z2*z3=1`, with Weyl factor `∏_{i<j}(1-z_i/z_j)(1-z_j/z_i)/6`: `∫1=1`, `∫χ=0`, `∫χ²=0`, `∫χχ†=1`, `∫(Reχ)²=1/2`, `∫χ³=1`. The nonzero cubic character moment distinguishes SU3's baryonic center selection from a naive U(3) replacement. Its lower-order group-invariant local baryonic terms are not mistaken for a nonconstant bottom **plaquette** Wilson mark.

At the specifically selected order **one upper plaquette insertion and four mixed fifth plaquette insertions**, orientation factors and the quartic expansion factorial give the exact nonconstant coefficient:

\[
\boxed{[\beta_1\eta^4]\,K(U_0)\big|_{\mathrm{nonconstant}}
=\frac{\mathrm{ReTr}P_0}{16\,3^9}.}
\]

The same coefficient holds in `log K` at this order; the normalizing source-dependent constants cancel. Under the original Wilson normalization `exp((β0/3) ReTrP0)` this means the leading **local** effective coupling shift is

\[
\boxed{\delta\beta_0=\frac{\beta_1\eta^4}{16\,3^8}
=\frac{\beta_1\eta^4}{104976}.}
\]

This is a **Taylor coefficient and a finite-slab operator computation**, not a fully effective one-plaquette action: further terms generate other gauge-invariant and multiloop interactions, so exact all-order equality to the bare original Wilson Gibbs source is NOT established.

The original normalized local Wilson **deficit mark** `F0=1-ReTrP0/3` has Haar mean 1 and `Var(ReTrP0)=1/2`. Thus its first induced expectation shift is

\[
\boxed{\delta\langle F_0\rangle=-\frac{\beta_1\eta^4}{32\,3^{10}}
=-\frac{\beta_1\eta^4}{1889568}.}
\]

A nonzero analytic Taylor coefficient proves that the selected 5D pushforward and the original bare 4D local Wilson measure are **not identically the same family on any open neighborhood of the decoupled source**, without a compensating effective action/counterterm. This is a source-specific finite mathematical obstruction, **not** a failure of KK physics or the original YM machinery.

## Same-source quantum BIDI into the existing CMP119/OS owner

For any selected original 4D gauge-invariant observable `F(U0)` and positive fibre kernel `K(U0)`, with `μ4` the original local Wilson reference, the **exact all-orders** identity is

\[
\langle F\rangle_{\pi_*\mu_5}-\langle F\rangle_{\mu_4}
=\frac{\mathrm{Cov}_{\mu_4}(F,K)}{\langle K\rangle_{\mu_4}}.
\]

It is exact simply by change of measure; a correct physical 5D measure must supply the **actual** `K` and its gauge/measure/normalization, including all fifth-axis links, scalar `A5`, ghosts/gauge quotient, the **eight Dirac fundamental colour flavours**, other SU3/E6 matter and any boundaries/tuning. The full effective action is `S_eff(U0)=S4(U0)-log K(U0)` with the full induced linked and disconnected polymer/source terms. The #1536 CMP119/122 renormalized effective action, marked observables and selected 4D source response would be the natural original owners to consume that kernel, but **the one-plaquette kernel in this file has NOT been shown to equal their full original source**.

To promote the 5D source into original YM **quantum** identity, the next same-object lemmas are:

1. Build/identify **one actual 5D gauge/Higgs+matter measure** with native selected geometry and full periodic/orbifold conditions; select a measurable physical quotient/projection `π` and explicit original finite 4D Wilson/Haar `μ4` at **every cutoff**, not one isolated plaquette; account actual `SU3c` vs `U1_B`, 5D graviphoton and physical 4D photon separately.
2. Source normalization and **exact/quantified** density transfer: compute/estimate `K`, its marked log-derivatives, connected cumulants and the source-dependent counterterms uniformly in cutoff; prove equality/controlled covariance of **all** original gauge-invariant Wilson cylinder observables, not just one source mark.
3. Use the **existing** R445 native reflected coarse pullback; require that `π` commute with physical reflection and pull back positive-time observable algebra. Only then transfer the same RP/OS Gram, null/radical and spectral content, including complex observables. Classical action equality and a finite gap do not do this.
4. Require a genuine physical OS Hilbert/intertwiner (not a naïve zero-mode projection) that preserves the actual transfer semigroup, energy, vacuum and dense gauge-invariant sector, and a strictly positive limit gap `Δ>0` uniform as `a→0,L_box→∞` with original CMP116/119 source estimates.
5. Only after same `T_AB` from the same 5D action and a validated 4D metric may the separate gravity/clock/freefall observations be derived. A non-Abelian SU3 quantum kernel is **not** the metric's abelian KK graviphoton nor evidence that the original Yang–Mills mass gap is the EM cavity frequency.

**Important scale-accounting:** tree-level `1/g4²=L/g5²` remains the original 5D source relation under a constant zero mode. The pure-SU3 heuristic one-loop `b0=11` applies only to a **justified pure-gauge 4D decoupling**; keeping eight active 4D Dirac fundamentals instead gives `b0=17/3` *before any other matter threshold*. Neither supplies a positive nonperturbative continuum spectral gap automatically.

## Verification and file receipts

Locally executed exact file `scripts/check_oct369_p038_su3_haar_fibre_pushforward.py`: **96/96 programmed assertions PASS**, SymPy 1.14.0; actual SU3 Cayley gauge transformations, true Weyl class integrals, four independent 5D mixed plaquettes, gauge covariance, 3^8 exact index contraction, exact leading source coefficient and original mark shift, pure/nonpure running and zero-mode spectral negative controls. Some programmed checks are scope or bookkeeping guards; **96 is not 96 independent theorems**. No Agda kernel/CI or physical material calculations. Git source blob SHA and SHA256 are in the committed JSON receipt. Full native #1241/#1444/#1536 suites were read but not rerun in the local Python environment.
