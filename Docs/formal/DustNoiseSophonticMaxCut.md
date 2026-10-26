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
