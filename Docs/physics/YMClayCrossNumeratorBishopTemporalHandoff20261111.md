# YM original RG cross numerator × Bishop parity × temporal structure — proof-oriented handoff

**Status (2026-11-11):** mathematical handoff / candidate architecture. Not a claim that the Yang–Mills Clay gates, uniform Wilson RG error, continuum limit, or OS gap are solved. The original PR #1444 source remains the authority for finite Wilson physics. Other programme analogies are not substituted for same-object witnesses.

## 1. The exact original-source cancellation and its missing rate

Let the actual original n=3 interacting SU(N) Wilson-Gibbs measure be `mu_f`, the native ordered 4-to-2 Wilson block be `B`, and the independent original n=1 bare Wilson-Gibbs measure be `mu_b`. Let

- `N_f(F) = ∫ F(BU) exp(-S_f(U)) dH_f(U)`;
- `N_b(F) = ∫ F(V) exp(-S_b(V)) dH_b(V)`;
- `Z_f = N_f(1)`, `Z_b = N_b(1)`;
- `X(F) = N_f(F) Z_b - N_b(F) Z_f`.

The source-written owner is `YMClayE1A3OriginalR445WeightedCrossNumeratorExact.agda`; it proves the finite source expansion and `X(1)=0` (kernel receipt pending). The natural **next finite algebra lemma** is

`X(F + c*1) = X(F)`, hence `X(F - c*1) = X(F)`,

derived from the ORIGINAL two numerator linearity/scale theorems, the literal original partitions, and the selected real-ring laws. This does not require dividing by either partition. In particular take `c = E_b[F]` when that expectation is already defined. This is an exact recentering, not a decay theorem.

The actual normalized discrepancy (under the genuine positive partition and standard ordered division field laws) is

`E_eff(F) - E_b(F) = X(F)/(Z_f*Z_b)`.

An estimate `|X(F)| ≤ K(a,L,F) Z_f Z_b` therefore requires a **real physical source producer** for the nonconstant F and a lower-bound/quotient law as appropriate; the existing algebra cannot manufacture a rate. The current PR #1444 quantitative covariance theorem reduces the two-source discrepancy to the three original moment errors at F, G and FG; positivity/complement and product test closure cover certified unit-bounded tests.

## 2. Proposed P0 finite plaquette lemma and precise type contract

Suggested file: `YMClayE1D1PlaquetteFluctuationBoundExact.agda`. Do **not** declare an arbitrary polymer estimate as a theorem, or insert a hidden source-independent F. The next source producer must select a literal `p : PeriodicPlaquette 1` and

`F_p = Words.originalWordObservable ... 1 (p :: [])`

on the *actual coarse side-two SU(N) links*; `N_f(F_p)` uses `F_p ∘ Push.actualBlockedLinkMap` and the existing original fine density. If the trace is not already certified [0,1], an explicit normalized/affinely shifted observable and its original real order proof must be constructed first; do not infer it from the rational SU(2) quaternion trace bound for arbitrary matrix SU(N).

The kernel-facing theorem target is an inequality of the form

`absℝ (X(F_p)) ≤ error_p *ℝ (Z_f *ℝ Z_b)`,

with `error_p` an **explicit physically derived**, nonnegative scale-dependent quantity from an original Wilson effective-action comparison or an original anchored polymer expansion. A fixed 4-to-2 block is only one finite coarse-graining step, so an `O(a^delta)` or `O(beta^-1)` claim is **not** implied by the existing R445 map. Strong-coupling expansion is a different coupling regime from the usual asymptotically-free weak-coupling UV continuum target.

Relevant existing sources: `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact`, `YMClayOriginalWilsonFiniteTwoSourceJetExact`, `YMClayE1A3OriginalR445WeightedCrossNumeratorExact`, `YMClayOriginalWilsonFiniteNumeratorOrderExact`, `BalabanCMP119FactorizedDensityApproximationExact`, `YangMillsPreferredWilsonWEXTSourceRound576Exact`. The decisive unpaid step is matching the **actual** effective blocked fine Wilson integral to the **actual** independently chosen coarse theory, not the formal algebra of numerator differences.

## 3. B4 orbit compression and the central-void analogy: candidate, not quotient theorem

The proposed 240-cell B4 shell count 64+96+64+16=240 can be tested as a finite combinatorial carrier. However the selected Wilson original links and their nonabelian holonomy are not automatically functions of four shell/orbit moments. A correct reduction needs:

1. A literal B4 action on the selected **original gauge links/plaquette paths**, with signed orientation and periodic quotient compatibility;
2. invariance/equivariance of the Wilson source Gibbs density, product-Haar integral, native 4-to-2 block and test class under that action;
3. either a sufficient-statistic theorem showing the selected insertions factor through the four orbit moments or a rigorously bounded residual for what is discarded.

The void/excised-cube is not thereby a gauge-fixed vacuum or a physical deleted region. Constant-mode cancellation `X(1)=0` holds independently of that geometry. Local gauge invariance alone does not imply shell-orbit sufficiency.

## 4. Bishop finite parity and OS time: the exact finite statements

Finite even/odd reindexing of the complex exponential polynomial is a useful algebraic lemma. But `U_N(t) = sum_{k=0}^{2N-1} (itH)^k/k!` is **not exactly unitary** at finite N in general. Already at N=1, `U_1(t) = I+itH`, and for nonzero self-adjoint H one gets `U_1(t)^* U_1(t) = I+t²H²`, not I. A finite parity split preserves bookkeeping, not norm/unitarity or the OS reconstruction axioms.

Credible alternate routes are: prove a convergent unitary group `exp(itH)` by spectral calculus or bounded-operator norm limits (with uniform domain control for unbounded H), or use rational Cayley transforms under resolvent/domain hypotheses. For OS, first construct the SAME selected reflection-positive Hilbert space and self-adjoint positive H. Do not identify its real-time unitary group with its Euclidean contraction semigroup without a Wick/OS theorem and matching observables.

Chronological data need not reside *entirely* in odd imaginary coefficients: a fixed-time cosine/sine parity split can still lose path ordering, while noncommuting path signatures, lagged Gram, and iterated commutators may retain information. PR #1480's proposed temporal non-identification comparison is at most a motivation for a separate same-trajectory sufficiency theorem, not an OS transfer proof.

## 5. Ternary/Golay/Monster and situated agency

The arithmetic `196884 = 10*3^9+54` by itself does not produce a 54-dimensional physical or cognitive residual. Ternary Golay and finite-group module theory may give code- or symmetry-theoretic constructions, but there is no established map here from those modules to an OS Hilbert space, a decoherence channel, or an individual's agency. Any proposed code interpretation needs explicitly defined carrier, stabilizers/check operators, syndrome, noise model, correctability, and the same-object application map. Do not infer physiological coherence from metaphor.

## 6. Ranked next proofs

- **P0/A:** source-linear original Wilson cross-numerator centering `X(F+c)=X(F)` for the actual finite Gibbs numerator (algebra; no physics rate).
- **P0/B:** a single original side-two plaquette trace source, physical SU(N) trace bounds/normalization for the selected [0,1] class, and a genuine nonconstant blocked-vs-bare numerator estimate `|X(F_p)|` with its actual scale domain and coupling regime.
- **P0/C:** compare at least three actual insertions `F,G,FG`; use the existing original Wilson covariance quantitative theorem, then iterate the controlled physical RG step consistently.
- **P0/D:** source-first R576 mixed-log connected-cluster expansion and connecting-tail bound for the same selected E1 cylinders; R577 OS physical time with the same H.
- **P1:** only after establishing exact carriers, test the B4 equivariant compression and Bishop parity/operator convergence transports as **separate** proof attempts with negative controls.
- **P1:** keep R563 same-family continuum noncollapse and R571 compact-simple-group quantitative extensions independent.

**Acceptance:** handoff note; no new Clay theorem, no Agda kernel claim. Max-cut principle is to prevent unearned promotion of finite/structural equalities to continuum physical authority.


## 2026-11-11 implementation: original Wilson P0 constant-mode centering

Committed `DASHI/Physics/YangMills/YMClayE1D1CrossNumeratorCenteringExact.agda`, imported into `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda`.

This uses the **actual original** side-four SU(N) Wilson Gibbs/Haar and its two-link native blocking map versus the **independent actual** side-two bare Wilson Gibbs/Haar, with original numerator scale and addition laws, rather than an invented linear functional.

- `weightedCrossShiftCancellation`: scalar bilinear cross-numerator identity, from the selected real-ring distributivity, commutativity, associativity and subtractive cancellation
- `fineConstantNumerator` / `bareConstantNumerator`: same-original-source Haar numerator of a constant scalar insertion equals scalar times that source's actual partition
- `fineShiftNumerator` / `bareShiftNumerator`: actual source-specific scalar addition laws
- `originalWilsonCrossNumeratorConstantShift`: **unconditional source-written** `X(F + c * 1) = X(F)` for every original coarse test and scalar
- `originalWilsonCrossNumeratorNegativeCentering`: unconditional `X(F + (-c) * 1) = X(F)`
- `fineNumeratorCongruent`, `bareNumeratorCongruent`, `crossNumeratorCongruent`: literal pointwise-to-Haar integrand congruence, so no hidden function-extensionality axiom
- `originalWilsonCrossNumeratorSubtractionCentering`: `X(F-c)=X(F)`, taking the standard `x-c = x+(-c)*1` scalar identity as an **explicit authority argument**, because the currently selected `RealAnalysisAxioms` module does not provide that particular additive-inverse equation

The stronger centered one-sided formula `X(F)=Z_b N_f(F-E_bF)` is **not yet promoted** merely from the previous centering lemma: it also needs a proof that the selected division operation satisfies `N_b(F)=E_b[F] Z_b` and a genuine bare centered numerator cancellation using the selected scalar laws. The existing normalized expectation is abstracted by a `divide` function, so standard quotient cancellation must be justified, not smuggled in.

Next physical producer remains a source-native nonconstant plaquette bound on `X(F_p)`, followed by actual scale/volume error propagation. **No uniform decay rate is claimed.** Kernel Agda 2.9 receipt remains outstanding.


The new centering module also specializes directly to `originalCoarsePlaquetteTrace` (`Words.originalWordObservable ... 1 (p :: [])`) and proves `originalPlaquetteCrossNumeratorConstantShift` for arbitrary original side-two plaquettes. The subtraction-spelled specialization, `originalPlaquetteCrossNumeratorSubtractionCentering`, retains the same explicit selected scalar subtraction identity argument. This pays the specific plaquette *centering* algebra, not any nonconstant physical RG error bound.
