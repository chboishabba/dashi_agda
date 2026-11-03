# Dust / Noise × Sophontic: reuse-first exact max-cut (26 October 2026)

**Status:** source-written integration, finite Python certificates; *not* a kernel-checked Agda/Lean theorem, not an independently reproduced GPU benchmark. CI intentionally not requested.

## Source and claim attribution

- **Q Labs Dust** (Dahal, Mandal, Gülbahar, Vegesna): forward-only transformer training by activation-space perturbation. Primary https://qlabs.sh/research/dust/ and https://github.com/qlabs-eng/dust
- **Q Labs Noise** collaborative community and contributors named in project histories: speedrun and structured Hadamard improvements. Primary https://qlabs.sh/noise and https://github.com/qlabs-eng/noise
- **Sophontic / Julian D. Michels**, independently: paired load-bearing-fact perturbation, flip-rate evaluation and proposed training of internal reasoning geometry. Primary https://sophontic.ai/ (methodology, 2026); vendor performance claims are *not* accepted as external reproduction.
- **LILA**, independently: scientific experiment and verifier feedback loop, not the same organisation or algorithm. Primary https://www.lila.ai/tech
- **DASHI integration**: crosswalks and proposed experiment programme below, not a transfer of upstream authorship.

## Prior-art owner routing (no competing ontology)

- Agda #1094 `DASHI/Reasoning/SemanticInterventionEquivarianceExact.agda` (paired semantic interventions), `GeometricReasoningCandidateSelectionExact.agda` (action comparison), `GeometricReasoningSurfaceResidualExact.agda` (surface + reopenable residual).
- Agda #1095 / Lean #44: Sophontic/LILA/teleodynamics geometric-reasoning integration.
- Agda #541: neural learning, attention, weighted future kernels, learning provenance.
- Agda #575: Walsh symmetry/cancellation; use *finite-character orthogonality*, without equating its Yang–Mills carrier with a transformer.
- Agda #671: canonical proof-search and experiment design.
- Agda #882: local-optimisation compiler, related-state and observational equivalence.
- Agda #902: canonical structural owner selection.
- Agda #1207 / Lean #75: claim-relative verification, abstention, authority boundaries.
- Lean #61/#76, Agda #1128: quantum same-global-state geometry; *optional analogy*, no physical quantum advantage follows.
- Agda #1200: `dashi-repo` DB for exhaustive source-owner discovery.

These records were found in GitHub PR descriptions. Source availability in stacked branches and proof receipts need a separate exact-head audit.

## Three NON-identical uses of perturbation

1. **Sophontic semantic intervention**: pair `(x,y)`, `(T x,y')` with a changed load-bearing fact. A useful diagnostic requires **both answers correct**, not merely `predict(x) != predict(Tx)`. Also include invariance pairs `y'=y` and nuisance controls.
2. **Dust training intervention**: perturb internal activation `h` by `sigma*u`, measure downstream loss difference, estimate activation credit and outer-product a weight update. No semantic change guarantee.
3. **Noise structured probe schedule**: arrange the perturbations as orthogonal Walsh–Hadamard directions to reduce directional sampling noise and share computation. This is a *design of training experiments*, not itself an explanation of reasoning.

Typed bridge:
```
ObservedPair {original, transformed, truthOriginal, truthTransformed, transformKind, provenance}
InternalProbe {layer, activation, direction, amplitude, lossBefore, lossAfter, provenance}
ProbeDesign {directions, orthogonalityCertificate, cost, hardwareAndTimingReceipt}
ObservedPair --[explicit model / intervention connection]--> InternalProbe
```
**Do not promote** a high flip rate to paired correctness; paired correctness to learned geometric mechanism; or fast activation training to general reasoning improvement.

## Exact finite mathematics

For `G=(Z/2Z)^k`, `n=2^k` and Walsh characters `H[a,x]=(-1)^(a dot x)`:
`sum_x H[a,x]H[b,x]=n * indicator(a=b)` and `H^T H=n I`.

For affine `f(z)=c dot z+b`, any nonzero rational sigma, and Walsh rows `u_i`:
`g_j=(1/(n sigma))sum_i (f(z+sigma*u_i)-f(z))*u_ij = c_j`.
This is exact finite algebra: no statistical inference, no derivative/backprop prerequisite.

For nonlinear `f`, directional finite differences introduce bias. For the explicit 1D cubic, symmetric difference gives `(f(x+s)-f(x-s))/(2s)=3x²+s²`: order-two bias exactly, **not** zero.

For probes with covariance `Sigma`, the linearized uncorrected expected direction is `Sigma grad(f)`, not `grad(f)`. Geometry-aware credit needs an inverse-covariance correction or a deliberate preconditioned-objective contract. A Hermitian C3 Fourier frame is algebraically related, but not performance-equivalent to real Walsh probing.

## BIDI experiment design: required matched comparators

A. Baseline backprop/Adam; baseline Dust random activation probes; full Walsh schedule; partial/random orthogonal cycles; geometry-adapted schedule. Equal tokens, model architecture, validation sets and seeds, with both step-time and *total end-to-end* time.

B. Sophontic paired tests split by label-changing, label-invariant and nuisance-only interventions, leakage-controlled by transformation family. Report per-item accuracy, pair accuracy, label-change recall, valid flip rate, false flips and held-out transfer. The primary metric is **paired correctness**, never flip rate alone.

C. Cross-factorial compare probe schedule × semantic pair training/evaluation. Test whether improving credit efficiency changes robust paired correctness after controlling for loss and compute. Avoid assuming a positive causal link.

D. Report vector `(heldoutLoss, pairError, wallTime, FLOPs, GPUhours, memory, energy, tuningCost)` as a Pareto frontier. Keep raw benchmark rules (excluded warmups/validation) explicit.

E. Scale widths, token counts, sequence lengths, and training steps; measure `O(n)` full-frame probe costs and overfit transition points. Explicitly handle different architectures/activation widths.

## Minimal verified finite executable

Run locally: `python3 scripts/check_dust_noise_sophontic_finite.py`.

It checks exact Walsh Gram identities for n=1,2,4,8,16; exact affine credit recovery for rational examples; cubic central-difference bias; and a synthetic Sophontic pair fixture demonstrating **flips are not enough**. Finite tests are *not* universal proof terms.

## Remaining maximal mathematical proof cut

Reuse native group/character owners and prove a general finite tight-frame reconstruction theorem, then instantiate Walsh, optionally C3 Hermitian, and connect it through the existing typed semantic intervention interface. Extend to stochastic bias/variance under stated smoothness assumptions, rather than introducing general-purpose quantum or neural ontology. Exact branch imports and Agda kernel checking remain unclaimed.

## Provenance of this work

Original scientific claims belong to named original authors and institutions. DASHI owns only this integration and finite certificate. Evidence levels: source statement ≠ code description ≠ independent benchmark reproduction ≠ Agda/Lean kernel theorem.


## 26 October algorithm implementation tranche

New source: `DASHI/Reasoning/DustNoiseAlgorithmExact.agda`. It explicitly models Dust equations (1)-(4): population-centred loss differences, future-token reward weighting, negative reward/noise activation credit, tokenwise outer-product coordinates, attention-output surrogate credit, and distinct direct/attention/head/residual-scalar paths. `NoiseProbeSchedule` records orthogonality as a **required supplied proof**; it does not claim an instantiated Hadamard construction. The `dustOuterProductEquation` proof composes the explicitly provided aggregation and sum-congruence laws; it does **not** prove those laws from arbitrary opaque sum operators. Any mathematically stronger theorem requires genuine finite-sum algebra.

A second executable source `scripts/check_dust_reference_equations.py` gives rational two-token causal fixtures for the actual Dust population-centering/reward/update equations and attention surrogate. No hardware benchmark or publication result is reproduced. Those Python examples do not establish global gradient unbiasedness, convergence or neural scaling.

**Important branch reality:** `master` does not currently contain `DASHI/Reasoning/SemanticInterventionEquivarianceExact.agda`; this code lives in the #1094/#1095 stack. Therefore there is no honest direct Agda import of the Sophontic code on this master-based branch yet. The semantic intervention crosswalk remains a downstream stacked-branch obligation.

**Verified vs unverified:** files are committed and GitHub-read; a fresh local Agda kernel run and execution of the newly committed second Python script have not been reported. This is algorithm specification plus conditional structural mathematics, NOT completed formal proof of the paper's forward-estimator statistics.

## 26 October further source-equality audit: exact centering correction

The original Dust text explicitly defines `c_s = mean_population(perturbed_loss_s) - perturbed_loss_s`. Earlier DASHI code mistakenly described `baselineTokenLoss - perturbedTokenLoss`; fixed in `DustNoiseAlgorithmExact.agda` as `populationMeanPerturbedLoss`. This is a substantive correction, not a cosmetic rename. The baseline loss need not equal the perturbed population mean. The Python rational reference always used the population mean already.

Under a complete four-draw Rademacher population on two token activations `h0,h1` with perturbed losses `ell0=2*h0`, `ell1=5*h0+3*h1`, and `r0=c0+gamma*c1`, `r1=c1`, exact symbolic rational evaluation yields activation-credit coordinates:
- gamma=0: `(2,3)`
- gamma=1/2: `(9/2,3)`
- gamma=1: `(7,3)`.

This is an **exact finite affine fixture**, checking causally correct reward assignment and population centering for this example; it does not establish the estimator unbiased for all nonlinear or jointly perturbed networks. The same source file exhibits the cubic symmetric-difference discrepancy `sigma²`, so any proposed blanket exact-gradient theorem is false.

Original source for the corrected loss definition and equations: https://qlabs.sh/research/dust/ , section 2.2. Original code: https://github.com/qlabs-eng/dust . Upstream methodology owns the equations, DASHI the independent toy instance and corrective crosswalk.

**Remaining genuine maximal cut:** instantiate orthogonality over an imported finite-character carrier with a real kernel proof; replace supplied abstract sum-congruence with proved finite-sum functoriality; construct actual discrete probability law / Gaussian smoothing and variance bound on declared perturbation model; validate numerical coupling to real reference implementation; and graft into the Sophontic stacked branch before calling the integration complete. No CI requested.


## 26 October finite proof core continuation

`DASHI/Reasoning/DustNoiseFiniteProofCoreExact.agda` adds **source-written proofs** of bitwise XOR identity/associativity, a recursively defined bit-vector XOR/self-cancellation lemma, a two-probe cancellation algebraic theorem, and an explicit sign-flip involution. These are *prerequisite algebraic leaves*, **not** yet the general finite Walsh Gram identity, a nontrivial probability law or an estimator-validity theorem. A full Hadamard-frame construction remains open.

An Agda executable was not available locally in this run, so the new source is **kernel-unverified**. No CI requested. A theorem's appearance in this source file is not a kernel proof receipt.

Future required gates, in order: finite bit-vector enumeration; character orthogonality over actual ring scalars; concrete NoiseProbeSchedule witness; finite affine estimator reconstruction with proved finite-sum congruence; smoothing/expectation and variance theorem; actual source-code refinement for Dust and Noise; then Sophontic stacked-branch import and held-out empirical comparator. Avoid claim promotion.


## 26 October canonical Walsh owner correction (user-requested prior-art reuse)

**Do not implement a new Walsh foundation.** Existing Agda #575 provides the actual rational 16-point owner, already present in PR #1265's current branch:
- `DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact`: `walshCharacter`, `walshCoefficient`, nontrivial character cancellation.
- `DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshInversionExact`: `walshReconstruct`, `walshReconstructionExact`, `walshTransformInjective`, `walshReconstructCong`.
- `DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact`: `sumRational`, `sumRationalCong`.
- `DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact`: literal sixteen-element `Subset4` and enumeration.

Removed the duplicative `DustNoiseFiniteProofCoreExact.agda`. Added `DustNoiseWalshCanonicalAdapterExact.agda` importing the existing owner: direct complete-probe Walsh inversion, exact recovery and injectivity from the original Agda theorems, plus a *conditional* measured-response-to-credit theorem requiring an explicitly supplied measurement law. The exact 16-coordinate theorem is **not** a theorem for arbitrary activation widths; general width follows only with dimension-specific orthogonality and a compatible response law.

IMPORTANT: the original mathematical Walsh theory is classical; Serre (1977), Matolcsi (2015) sources in #575 retain provenance. The Agda #575 implementation is the DASHI proof owner. The new Dust/Noise adapter is a downstream consumer and does not transfer mathematical authorship to Q Labs.

Prior older text referring to a new Walsh theorem as missing is superseded for the **finite 16-point carrier only**. The new file has no fresh Agda kernel receipt, and no empirical forward-response identification is asserted. No CI run.
