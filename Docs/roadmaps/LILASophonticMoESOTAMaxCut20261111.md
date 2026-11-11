# LILA–DASHIg–Sophontic–MoE / LLM Architecture: Maximum-Cut Roadmap and Exact Lemma Ledger

**Updated:** 2026-11-11. **Status:** source-attributed specification and dependency plan; *not* a claim of Agda kernel acceptance, neural correspondence, experimental superiority, or current benchmark replication.

## Scientific target and attribution contract

Test the *original* LILA hypothesis, not a substituted architecture: equal or better quality with faster time-to-quality, lower active neural computation, less memory/energy, improved generalisation, reliable steerability and/or better compression. Track the quality/resource Pareto front rather than final accuracy alone. Distinguish (i) original model and upstream claim, (ii) mathematical donor, (iii) DASHI finite proof/adapter, (iv) real source-bound implementation, (v) independently measured empirical effect, (vi) interpretation. Never promote a donor analogy, finite witness, reported benchmark, source-file naming, or LLM-generated steering label into ownership, verified implementation, causality, or LILA scientific success. Preserve provenance: authors, publication/version, original repo and commit, licence, exact experimental configuration, seed, data splits, baseline and hardware.

Upstream/external references (not DASHI inventions):
- Turner et al. (2023), **Steering Language Models With Activation Engineering**, https://arxiv.org/abs/2308.10248 — ActAdd/contrastive activation directions.
- O'Brien et al. (2024), **Steering Language Model Refusal with Sparse Autoencoders**, https://arxiv.org/abs/2411.11296 — SAE feature steering and off-target performance risks.
- Mayne, Yang and Mahdi (2024), **Can sparse autoencoders be used to decompose and interpret steering vectors?**, https://arxiv.org/abs/2411.08790 — OOD and signed-projection limitations.
- Cho, Wu and Koshiyama (ICML 2026), **CorrSteer**, https://proceedings.mlr.press/v306/cho26h.html — correlation for candidate selection, intervention for causal validation; published benchmarks are author claims, not local replications.
- DeepSeek-AI (2024/25), **DeepSeek-V3 Technical Report**, https://arxiv.org/abs/2412.19437 — fine-grained shared/routed experts, auxiliary-loss-free load-balance bias, MLA, MTP; report claims belong to authors.
- Qwen team, Qwen model family documentation https://qwen.moe/ — dense/MoE architecture family and active/total parameter distinctions; verify individual checkpoint/config/revision before using numeric comparisons.
- Attribution Patching / AtP* (2024), https://arxiv.org/abs/2403.00745 — component-level causal-localisation methods and limitations.

These works are *design comparators*; they do not establish that LILA improves them. “SOTA” here means selected recent primary technical developments, not an exhaustive ranked leaderboard as of 2026-11-11.

## Existing owner atlas (inspect/reuse before adding declarations)

1. `DASHI/Biology/SparseExpertRoutingCoalition.agda`: finite sparse production/conditional addressability, explicitly a brain/MoE **analogy**, not real transformer routing.
2. `DASHI/Reasoning/FibreRoutingGrokkingMoEBrainCrossPollinationExact.agda`: fibre-routing composition, hard-winner information-loss witness, MoE/grokking/geometry interpretation firewall; *not* a proof of LILA router.
3. `DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda`: pinned DASHIg Phase-2 data, preliminary Leech/plain experiment and explicit attribution/non-promotion. Recorded p=97, WD 0.22/0.30, t50 and t95; both architectures achieved final 100% in recorded cases, no consistent advantage.
4. Existing `SemanticInterventionEquivarianceExact` work (Agda PR #1094), model-facing bridge (PR #1095), Dust/Sophontic paired-perturbation work (PR #1265), federated expert BIDI (PR #1442). PR descriptions are *candidate ownership*, not current-master inclusion or successful kernel proof: fetch exact heads/files before relying on them.
5. Prior whole-learner AdamW/Dust, E8→369, trialectic/pants, future quotient and LILA geometric-loss contracts: validate exact path/revision and distinguishing original-source proof status. Do **not** duplicate the abstract theory.

## Unified original-object state

For a selected train/infer implementation, specify
`S_t = (theta, m, v, scheduler, data_cursor, rng, geometry, router, expert_state, activation_semantics, intervention_policy, signed_history, provenance, numerical_config)_t`.
An input-dependent layer executes shared experts plus top-k routed experts with score calibration, tie rule, capacity/overflow policy and conditional dispatch. The steering action is **site-indexed**: before router / on router logits / on expert input / on expert output / on residual stream / on downstream weights. Pre-route and post-route interventions are *not* assumed equivalent. Explicitly distinguish individual neuron coordinate, learned feature, expert selection, semantic behavioural target and training-trajectory intervention.

Reference architecture variants: dense plain transformer; original LILA checkpoint and geometry; identical-model gauge-only control; nonzero geometry regularisation; shared+routed MoE; pure routed MoE; optional alternative attention (GQA/MLA/hybrid) and MTP isolated as independent switches. Every ablation must match data, training budget, precision, optimiser, seeds, evaluation and material model differences.

## Exact remaining lemma ledger

A lemma is **OPEN** until the selected source, theorem signature and kernel/runtime evidence are recorded. Proposed names below are *new candidate obligations*, not assertions that definitions are absent in all branches.

| ID | Priority | Exact obligation / proposed name | Acceptance evidence |
|---|---|---|---|
| A01 | P0 | `selectedOriginalModelIdentity` | Original LILA architecture, weights, tokenizer, loss, version, provenance pinned |
| A02 | P0 | `adamwStateRoundtripSameFuture` | Full optimiser/scheduler/RNG/data/router replay, not weights-only |
| A03 | P0 | `adamwReferenceStepImplementsSelectedKernel` | Math vs finite-precision backend refinement; scoped tolerances |
| A04 | P0 | `sameCheckpointSameTokenScheduleComparison` | Matched intervention and baseline evidence |
| A05 | P0 | `sharedOrthogonalGaugeCancelsAttentionScores` | Exact attention score invariance under simultaneous Q/K orthogonal rotation; no stronger claim |
| A06 | P0 | `originalResonanceSourceLossSameFormalLoss` | Real training regulariser/gradient identity on source |
| M01 | P0 | `moeDenseSpecialCaseExact` | Formal dense limiting/full-routing case, with normalization conditions |
| M02 | P0 | `moeRouterDeterministicReplay` | Top-k, ties, capacity, overflow, batch dependence, RNG, load-balance state |
| M03 | P0 | `moeSelectedKernelRefinement` | Original routing/dispatch/combination equals selected backend semantics |
| M04 | P0 | `moeBalanceBiasUpdateRefinement` | If selected: load accounting, routing-only bias update, unchanged mixing weights |
| M05 | P0 | `adamwMoESparseUpdateRefinement` | Selected/unselected experts, decay, zero/none grads, moments and router update |
| S01 | P0 | `steeringOriginalActivationWeld` | Selected hook/activation identity, layers, heads, neurons, SAE dictionaries |
| S02 | P0 | `sophonticPairedSemanticCorrectness` | Paired intended label/action and unrelated task preservation defined independently |
| S03 | P0 | `sophonticSemanticActionSound` | Actual injected action and held-out decoder semantics commute under stated preconditions |
| S04 | P0 | `steeringSiteSeparationCounterexample` | Witness that pre-router vs post-router actions do not generally commute |
| S05 | P1 | `steeringRouterCommutationCriterion` | Sufficient *and necessary when possible* conditions on selected routing margins/action |
| S06 | P1 | `steeringCompositionSound` | Composition with signs, time, noncommutativity, side effects and provenance |
| S07 | P1 | `featureSteeringSignedReconstructionBound` | SAE OOD/signed feature residual and failure detector; no semantic identity from SAE alone |
| S08 | P1 | `steeringProposalIndependentCausalValidation` | LLM/correlation proposes; held-out paired intervention identifies effect; random/equal-norm controls |
| G01 | P1 | `geometricRouterEquivariance` | Same-object E8/Weyl or claimed transform and actual top-k dispatch; tie boundary handled |
| G02 | P1 | `originalNeuralE8ChartRefinement` | Real activation/weights identified with chart; no analogy promotion |
| G03 | P1 | `expertSpecialisationIdentifiableModuloPermutation` | Invariance under expert permutation and admissible representation gauges |
| G04 | P1 | `trialecticExpertSeamSound` | Typed face/context composition of actual expert actions |
| G05 | P1 | `signedHistorySteeringEquivariance` | Time-indexed interventions, signed fibres and replay preserve selected consumers |
| O01 | P1 | `dustAdamwMatchedTrajectoryComparison` | Full-model comparison with budget and stochastic traces aligned |
| O02 | P1 | `grokkingRoutingTrajectoryBridge` | Time-to-quality / threshold censoring / expert entropy / spectral invariant measured jointly |
| O03 | P1 | `grokkingMechanismNonPromotion` | Finite time-rescaling fits do not entail universal mechanisms or causal geometry advantage |
| R01 | P1 | `moeResourceAccountingSound` | FLOPs incl. router/dispatch, active vs total params, bandwidth, KV, VRAM, energy |
| R02 | P1 | `matchedResourceParetoDominanceSound` | Explicit quality and resource constraints; seed dispersion and censored runs |
| R03 | P2 | `futurePreservingExpertCompression` | Pruning/merging/quantisation preserve specified future observations or return counterexample |
| R04 | P2 | `hyperfabricExpertGluingSound` | Typed local-global expert gluing, overlap, source identity and consumer adequacy |
| R05 | P2 | `conditionalComputationNoFreeSavings` | Counterexample: fewer active experts need not imply lower walltime, memory, energy |
| F01 | P0 | `selectedSourceAgdaKernelAccepted` | Agda 2.9 actual command, version, logs, no postulates/metas for selected closure |
| F02 | P2 | `wholeSystemBidiCommutingDiagram` | Both directions between source execution and formal semantics on same model and consumer |

Dependency maximum cut: **A01–A04 + M02–M03 + S01–S03** → source-bound execution/steering, then **A05–A06 + M04–M05 + G01–G03** → geometry/expert mechanism, then **O01–O03 + R01–R02** → defensible empirical efficiency, followed by **G04–G05 + R03–R04 + F02** → composition/preservation. F01 applies at every proof gate rather than being postponed.

## Phases, concrete deliverables and exit conditions

| Phase | Deliverable | Gate to proceed |
|---|---|---|
| 0 — Source audit | Revision-pinned donor/claim ledger, current PR/master status, originals and licences | Every cited in-repo declaration has source path and exact version |
| 1 — Full learner | Actual LILA architecture and complete AdamW/forward-state contract; exact numerical boundary | A01–A04, A06, M01–M03, F01 for modules |
| 2 — Routing + steering | Named neuron/feature/router/expert sites, paired semantics, replay and counterexamples | S01–S04, M04–M05, S07–S08 |
| 3 — Geometry + composition | Gauge/resonance controls, actual E8/369 representation, valid/invalid commuting cases | A05, G01–G05, S05–S06 |
| 4 — Optimisation + grokking | Stage-indexed learning-state and expert-specialisation time-series, AdamW/Dust controls | O01–O03 plus reproducible matched runs |
| 5 — Original empirical claims | TinyStories/BPC, time-to-quality, active-neuron/FLOP, compression, steering and energy Pareto report | R01–R02, multiple seeds, common task/data, variance and off-target effects |
| 6 — Consumer-preserving deployment | Fidelity-checked pruning/merging/federated signed history and explicit failures | R03–R05, provenance and future sufficient quotients |
| 7 — Kernel/source acceptance | Agda 2.9 results + source-to-theory BIDI trace with negative controls | F01–F02; no assumed full correctness from finite proof |

## Experiment factorial and go/no-go criteria

Run LILA as originally implemented, plain dense baseline, same-model orthogonal gauge, nonzero geometric regulariser; then introduce MoE with geometry off/on; then steering off/on with matched vectors and independent semantic tests. Compare MoE-only against geometry×MoE interaction: do not assign the effect of new expert capacity or router to geometry. For architecture comparisons keep a model-same controls lane and an engineering system lane separately. Include original reported TinyStories result as an attributed claim until source-checkpoint evaluation reproduces it.

For steering: random unit and equal-norm control, shuffled labels, layer/site sweeps, prompt distribution shift, held-out source/target pairs, unchanged-task quality, adversarial controls, intervention reversibility, time-indexed checkpoints before/during/after grokking. An SAE feature is a candidate decomposition, not a mechanistic identification. For MoE: balance entropy, expert collapse, capacity overflow, dropless/dropped tokens, batch-size sensitivity, dispatch overhead and total GPU memory. For claimed sparse energy saving: report measured Joules and walltime on same hardware in addition to FLOPs.

## Negative-control theorem candidates to pay early

1. A one-dimensional signed-permutation/gauge change can preserve dense scores while changing a coordinate-specific top-k router unless the router transforms covariantly.
2. Pre-route activation steering can cross a top-k decision boundary, while same action post-route cannot retroactively change selected experts.
3. Two different fine semantic/overlap profiles can share an identical hard expert winner; winner identity is not future-sufficient for every consumer (reuse existing finite fibre collision owner).
4. A lower selected-expert count can coexist with greater total parameter memory or dispatcher latency.
5. Perfect final test accuracy in a finite set of grokking runs does not establish faster learning, causal E8 advantage or improved steering.

## Immediate work order

(1) Fetch exact PR #1094/#1095/#1265/#1442 heads and source owners, resolve master vs branch without treating PR text as kernel proofs. (2) Build A01/M02/S01 source maps and F01 kernel receipts. (3) Prove S04 and R05 finite counterexamples by reuse before proposing a universal positive theorem. (4) Complete A05–A06 and actual original-model loss weld. (5) Only then commission matched geometry×MoE×steering execution using existing DASHIg training evidence and original LILA checkpoints.

**Release firewall:** No claimed LILA superiority, neuron semantic identity, expert-to-brain equivalence, universal grokking mechanism, trained E8 representation or verified neural implementation until original-source, kernel and empirical obligations are separately paid.
