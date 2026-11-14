# Original Wilson F19/P0/R445: corrected A/B/C local-TV and continuum maximum cut

**14 November 2026.** Owns the exact follow-up to the user-supplied R445 argument, preserving the actual original 1024-link Wilson F19 source, the R445 3→1 blocked beta(3) coarse observables, and its different original bare beta(1) coarse law. **This document does not promote a Clay endpoint.**

## Original-source authority

- `YMClayOriginalWilsonPhysicalF19PartitionExact.agda`: canonical 1024-link fine Wilson partition, original 64 coupled pairs + 896 spectator link factorization, physical positive effective density and positive normalizer. This **does not alone prove** the cross-branch R445 beta(3) physical-blocking map and its target reference are the same mathematical object.
- `YMClayE1A3OriginalR445CrossCutoffSourceExact.agda`: `originalR445EffectiveCoarseExpectation` equals the *original* beta(3) fine pushforward on the 2^4 coarse carrier; `originalE1BareCoarseExpectation` is the *different* bare beta(1) Wilson normalized law. Equal normalized units **do not imply** equal nonconstant moments.
- `YMClayE1D1OriginalR445BoundedMomentMajorantsExact.agda` and `YMClayR445OneLocalTVThreeMomentsSourceWeldExact.agda`: original bounded tests and F,G,FG moment controls; `OriginalBoundedObservationLocalTV` is an uninhabited source-dependent physical assumption.
- `Docs/physics/YMClayR445SharpLikelihoodRatioMaxCut20261114.md`: exact, sharp **finite same-carrier** density-ratio TV inequality and growing tensor-volume TV counterexample.
- New `YMClayR445LocalizedTVInferenceNoGoExact.agda` and `scripts/check_ym_r445_localized_tv_maxcut_countermodels.py`: pure safe finite negative controls and exact conditional-mixture audit. They are **not** SU(N) Wilson models. Axioms/kernel must be reviewed separately for the true R445 source.

## Attachment audit: classification and proof status

| Claimed lemma | What is genuinely proved | Correct unresolved requirement | A/B/C |
|---|---|---|---|
| `originalR445F19P0LocalizedMarginalSameSource` | Each of F19 and R445 has native physical effective expectation/normalizer facts on its respective source carrier | Prove the **same physical coarse map**, conditional fibers, Wilson weights, normalizer identification and observation pullback between F19 and R445. For the *renormalized target* build its actual density, rather than replace it with beta(1) bare Wilson | A **OPEN** |
| `originalR445ConditionalActionOscillationBound` | Sharp finite density-ratio osc→TV bound is known | Prove the actual **effective minus target** local conditional action variation with uniform environment; physically construct source small-field Hessian/resolvent + normalized large-field control + polymer boundary estimates | B **OPEN** |
| `originalR445ActualLocalizedEffectiveTargetTVBound` | Conditional-pair comparison theorem on finite probability spaces (below); source-level original TV→three-moment compiler already exists | Control the physical conditional-kernel TV **and the external-marginal influence term**. Unconditioned marginal is **not** determined only by polymers literally meeting X | B **OPEN** |
| `originalR445LocalTVCutoffUniformSummable` | Geometric-series summation is standard once actual per-scale geometric estimates exist | Produce a **scale-dependent** physical irrelevant-factor `theta^k` (or summable comparable envelope) with constants uniform in cutoff, volume, boundary and target-counterterm flow | B **OPEN** |
| `originalR445ThreeMomentRGDecay` | Conditional TV≤d implies the actual original source F,G,FG errors ≤d, covariance discrepancy ≤3d (R445 previous owner) | Supply the same physical measure d_k and compatible counterterm-target flow. Small source expectation errors alone do not imply spatial or temporal clustering | A after B **CONDITIONAL** |
| E1 interacting continuum | Finite Wilson Haar normalized measures, some exact partition identities | Projective consistency of *the same* scale laws; tightness/regularity, OS RP in limit, covariance, nontrivial interacting witness | C **OPEN** |
| D1/D2 gap | F19/OS algebra and some finite positivity compilers | Actual all-separated physical connected-covariance exponential decay; same-H OS reconstruction, uniform positive spectral gap and stable physical mass units | C **OPEN** |

### Correct finite conditional-mixture theorem

Let P,Q be positive probability laws on the same finite product X×Y. Their Y marginals need not coincide. Define `K_P(x|y)=P(x,y)/P_Y(y)` and `K_Q(x|y)=Q(x,y)/Q_Y(y)`. Introduce the genuine intermediate probability law on X,

`M_X(x)=∑_y P_Y(y) K_Q(x|y)`.

Then by an **exact telescoping** and contraction of signed probabilities under a Markov kernel,

`TV(P_X,Q_X) ≤ E_{P_Y}[TV(K_P(·|Y),K_Q(·|Y))] + TV(M_X,Q_X)`

and

`TV(M_X,Q_X) ≤ TV(P_Y,Q_Y)`.

Therefore

`TV(P_X,Q_X) ≤ sup_y TV(K_P(·|y),K_Q(·|y)) + TV(P_Y,Q_Y)`.

This finite mathematical inequality is correct and was independently checked on **6,561** pairs of strictly positive 2×2 rational joint laws. The physical Yang–Mills path requires a **better** estimate for the outside influence than total exterior TV (which may approach 1 in extensive volume). For instance: a source-specific Dobrushin/influence-kernel spatial bound or an actually convergent local polymer expansion, uniformly in boundary and cutoff, **without assuming the desired D1 cluster conclusion**.

If, conditional on a *fixed* outside configuration, the **actual** source effective-vs-target local density quotient has likelihood-ratio range `m≤s≤M`, then the sharp finite conditional bound is

`TV(K_P(·|y),K_Q(·|y)) ≤ (sqrt(M)-sqrt(m))/(sqrt(M)+sqrt(m) = tanh(osc(log s)/4)`.

But the original Wilson effective action difference, the *target* counterterms, and the constants m,M remain unconstructed/unchecked. Neither `log` nor `tanh` on a generic Bishop scalar can be inserted by naming this bound.

### Independent no-go 1 — unconditioned outside action changes local TV

Q has mass table `Q(00),Q(01),Q(10),Q(11)=(3,1,1,3)/8`. Perturb only the **outside** y site by `w(0)=1, w(1)=3`. Its exact normalizer is 2. Then `Q_X=(1/2,1/2)`, `P_X=(3/8,5/8)` and `TV(P_X,Q_X)=1/8`, although the perturbing action does **not** touch X. Indeed

`E_P[1_(x=1)]−E_Q[1_(x=1)] = Cov_Q(1_(x=1),w(y))/E_Q[w(y)] = (1/4)/2 = 1/8`.

Thus, dropping all outside-only terms merely because they don't intersect X is **false** in the presence of cross-correlations. One must pay a physical conditional-influence bound.

### Independent no-go 2 — rare bad region does not control oscillation or TV

For any N>1, take `Q_bad=1/(N+1)`, `Q_good=N/(N+1)`, with likelihood weights `s_bad=N`, `s_good=1`. The reweighted law has `P_bad=P_good=1/2`, so

`TV(P,Q) = 1/2 − 1/(N+1)`

approaches 1/2 although the **reference** probability of the bad region tends to 0. Boltzmann smallness under a reference source is insufficient without normalization and both-measure control. In particular a small probability cannot generally bound a **supremum** action oscillation.

### Independent no-go 3 — incorrect 16^(-k) factor and non-summable 1/k

If at each scale `a_k/L_k=1/4`, then `(a_k/L_k)^2=1/16` for *every* k. At k=2, `(1/4)^(2k)=1/256`, already a different assertion. From `g_k^2≤C/k` and the fixed ratio one obtains an error **upper envelope** `C/(16k)`; the envelope is not summable. For all j≥0, its dyadic block from k=2^j to 2^(j+1)−1 has sum **strictly greater** than C/32 (for C>0). No power `16^-k` is available until a genuine per-RG-step irrelevant-direction contraction has been established.

This does **not** prove the actual physical d_k is nonsummable; it invalidates the *argument* that its proposed bound implies summability.

### Independent no-go 4 — zero local TV does not imply projective Cauchy or mass gap

(i) Take `P_k=Q_k` alternating deterministically between delta_0 and delta_1. Then **all** comparison distances `TV(P_k,Q_k)=0`, yet every successive `TV(P_k,P_(k+1))=1`. Target-scale consistency cannot be omitted.

(ii) Take `P=Q` on two arbitrarily separated sites supported fairly on all-zeros and all-ones. Then `TV(P_X,Q_X)=0` for every X, but their separated covariance is identically `1/4`, at **every distance**. No `Ce^(-mR)` estimate for fixed C,m>0 follows.

(iii) An anticorrelated two-time positive probability law on (+,-),(-,+), each with mass 1/2, has OS reflection Gram `E[theta(f)*f]=-1` for the spin test f. Ordinary normalized positivity and projective cylinder consistency do not imply OS reflection positivity. In the real Wilson lane, use original RP certificates and prove preservation in the *same* continuum source instead of inferring it from Kolmogorov–Prokhorov.

## Exact corrected original-source lemma list

These names are **proposed NEW declarations**, not falsely reported as in-repo theorems:

**A.** `originalF19R445SamePhysicalCoarseMap`, `originalR445F19PushforwardCylinderEquality`, `originalR445TargetCountertermNormalizedDensity`, `originalR445ConditionalKernelDisintegration`.

**B.** `originalR445PhysicalConditionalActionOscillation`, `originalR445BadFieldTwoMeasureNormalizedBound`, `originalR445ExteriorInfluenceKernelBound`, `originalR445PhysicalLocalTVFromConditionalAndOutside`, `originalR445GenuineScaleIrrelevantContraction`, `originalR445LocalTVUniformSummable`.

**A-after-B.** `originalR445OneLocalTVThreeMomentsUniform`, `originalR445CoarseTargetProjectiveSameFamily` and the already source-written `originalPhysicalR445CovarianceFromOneLocalTV`.

**C.** `originalR445OSPositiveProjectiveContinuum`, `originalR445NontrivialInteractingCylinder`, `originalR445OriginalWilsonRootedPolymerCovarianceDecay`, `originalR445SameOSGeneratorPositiveGap`.

The shortest source-first maximum cut is:

1. Prove the F19 ↔ R445 actual physical coarse-map / target normalization identity (do not confuse beta(3) with beta(1)).
2. Prove a physical cutoff/volume/boundary-uniform conditional-kernel comparison and exterior influence bound for the **actual** Wilson effective/renormalized target; use established F19/Haar/gauge/P0 modules.
3. Produce a **genuine source-derived** summable scale envelope, not a fixed 1/16 or an asserted `16^-k` factor.
4. Reuse original three-moment/covariance compiler, then independently prove original physical projective OS reflection positivity, nontriviality and exponential correlations. A positive OS gap must refer to the same reconstructed H with a cutoff-independent physical lower bound.

## Reproduce / trust

Run:

```sh
python3 scripts/check_ym_r445_action_oscillation_tv.py
python3 scripts/check_ym_r445_localized_tv_maxcut_countermodels.py
```

The second checker uses exact rational arithmetic for the conditional mixture decomposition (6,561 positive rational pair cases), exterior-only counterexample, rare-region reweighting, alternating-target non-Cauchy example, non-clustering same-measure example, OS negative Gram and dyadic harmonic blocks.

Focused source Agda acceptance root:

`DASHI/Physics/YangMills/YMClayOriginalF19P0CommonOSSourceConvergence20261114.agda`

The new `YMClayR445LocalizedTVInferenceNoGoExact.agda` has only native Nat arithmetic; **Agda 2.9 pinned kernel acceptance has not run**. Original R445/F19 imports still rely on legacy `RealAnalysisAxioms` and remain not `--safe`. No universal Clay terminal endpoint should be marked closed.


## Additional A proof: original physical F19 all-cylinder normalization

`DASHI/Physics/YangMills/YMClayF19OriginalAllCoarseCylinderNormalizationExact.agda` is a new actual source theorem (introduced on #1503, accepted by original F19/P0/R445 import root) with two explicit declarations:

1. `originalF19AllCoarseNumeratorsSamePhysicalSource`: for **every** coarse `F : Vec Link 64 → ℝ`, the original interacting 64-pair/896-spectator nested Wilson weighted numerator equals the product-Haar expectation of the **same** original full physical F19 effective density multiplied by `F`. Proof is a direct instantiation of the pre-existing `Fibre.selected64Pair896SpectatorWeightedDisintegration` with `Original.physicallySortedWilsonWeight` and the literal original pair/spectator packing.
2. `originalF19AllCoarseNormalizedSamePhysicalSource`: applies `cong₂ divide` to that numerator theorem and `F19.originalFinePhysicalPartitionEqualsActualEffectivePartition`. The denominator is the **actual original canonical 1024-link Wilson partition** on the fine side and the **actual effective F19 density partition** on the coarse side; both are already proved equal in the original F19 source and separately physical-positive given the original strictly positive SU(N) Haar integration premise.

**Precise status:** this pays the *F19-internal* A-level source normalized cylinder identity. It does **not** establish `originalF19R445SamePhysicalCoarseMap`: the selected R445 `SUNBlock.nativeSUNBlockLinks {m=1}{l=1}` must still be proved pointwise identical to the F19 sorted-64-pair block map after the original codec/reindex, and the actual R445 renormalized target must be constructed. No cutoff-uniform TV/physical RG estimate follows from this new theorem. Legacy `RealAnalysisAxioms` and Agda 2.9 exact-head kernel acceptance remain outstanding.

The main logical no-go and correct conditional-mixture inequality above are unchanged.
