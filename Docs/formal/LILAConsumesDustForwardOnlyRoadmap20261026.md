# LILA consumes Dust/Noise forward-only optimisation: implementation boundary (2026-10-26)

## Direction corrected
The target is not only a comparison between LILA, Sophontic and Noise. It is an actual **LILA task/objective consumer** of Dust/Noise gradient-free perturbation updates. Distinguish the scientific-laboratories LILA name (if present in source context) from the repository's semantic-action/geometric-reasoning LILA usage; no identity implied by spelling.

Existing generic theorem already satisfies the observer-refinement requirement:
`DASHI.Core.ObserverRefinementLatticeExact` supplies `pairObserver`, `pairRefinesLeft`, `strictPairRefinement`, `addingObserverShrinksResidualFibre`, `strictFamilyRefinementBlocksCoarseSeparation`. Do not duplicate these.

## Source-written adapter
`DASHI/Reasoning/LILAForwardOnlyDustAdapterExact.agda` imports both canonical refinement and `DustNoiseAlgorithmExact`, and specifies:
- coarse/semantic observer pair and its canonical refinement;
- LILA objective and paired semantic-intervention loss;
- a forward-only probe that proposes a new parameter without reverse AD;
- equality of the observed loss-at-probe and the declared objective-at-proposed-parameter;
- a literal `Dust.ForwardOnlyTrace` dependency;
- explicit empirical calibration and held-out test flags.

This is an interface for a real producer, not itself an optimiser implementation or benchmark proof.

## Implementation/experiment work that must be paid
1. Choose an actual LILA objective from #1094/#1095 and specify which trainable parameters are changed (action encoder, decoder, intervention comparator, candidate-policy layer). Avoid accidentally passing a label-only semantic score as a differentiable/forward-only learning objective.
2. Implement sampling a perturbation seed and running *the same* paired semantic actions through baseline and perturbed parameter settings. The same test pair must be held fixed within the finite difference, while training and validation examples remain disjoint.
3. Consume Dust's noise-credit and update equation rather than merely using two arbitrary evaluations. The present generic adapter does NOT yet prove it composes an unbiased or descending estimator for the actual LILA loss.
4. Track K forward passes, total tokens/examples, hardware joules, latency, memory, number of failed searches, and selected hyperparameters.
5. Baselines: matched full backprop, straight zeroth-order random-direction estimate, Dust activation-credit, Dust orthogonal probe schedule. Evaluate paired semantic correctness, equivariance error, held-out generalisation, nuisance invariance and resource cost.
6. Split-scoped authority: prove finite operator identities in Agda; computational checks and empirical training receipts separate; no promotion of speedrun success to causal identity or verified semantic action.

## Acceptance gates
- **Formal**: literal same-object objective and Dust trace/candidate-update computation; typed refinement already imported; no new observer calculus.
- **Numerical**: fixed-seed finite toy task where Dust-proposed directions are actually evaluated against the LILA objective; compare objective improvement and operation counts.
- **Scientific**: held-out semantic pairs, nuisance shifts and quality-matched baselines on representative LILA experiments.
- **Scale**: longer horizons and realistic model layers without relying on the 10M-token benchmark speedup figure.
- **Attribution**: original Dust authors/Noise contributors, LILA/Sophontic prior owners, and DASHI adapter author each preserved distinctly.

No CI requested. No Agda kernel check claimed.
