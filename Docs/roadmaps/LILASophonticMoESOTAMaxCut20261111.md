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

## 2026-11-11 continuation: storage-tiered Qwen / out-of-core MoE maximum cut

### Attribution and verified-source comparison

**Qwen Team (original model/architecture):** `Qwen/Qwen3-Next-80B-A3B-Instruct` model card https://huggingface.co/Qwen/Qwen3-Next-80B-A3B-Instruct and original Qwen3-Next architecture blog https://qwen.ai/blog?from=home.latest-research-list&id=e34c4305036ce60d55a0791b170337c2. Reported 80B total, ~3B active per token, 48 hybrid DeltaNet/attention layers; 512 routed experts, top-10 plus one shared expert per MoE layer. **3B active ≠ 3B resident**. Benchmark comparisons are Qwen author's reports, not DASHI replication.

**oLLM:** https://github.com/Mega4alik/ollm (author's primary repo; do not assign ownership based on an unattributed search summary). Reports 80B bf16, 50k context on 8 GB RTX 3060 Ti, ~7.5 GB VRAM / 180 GB SSD, about **0.5 token/s**; layer-wise streaming and SSD KV offload. Numbers must remain benchmark-configuration-local.

**AirLLM:** https://github.com/lyogavin/airllm. Author reports layer streaming, Qwen3-235B ~3 GB VRAM and 405B Llama 3.1 ~8 GB VRAM; these are **peak accelerator memory claims**, NOT claims of 3 GB system RAM/disk or conversational throughput. A large slow experiment is not a winning efficiency point without speed/energy/quality measurements. Source version and modern claims need pinning.

**Swiftlet** (not “Swiftlit”): https://github.com/leonickson1/Swiftlet. Author reports Qwen3-Next-80B-A3B 4-bit ~42 GB disk, ~4.3 GB peak RAM and ~4.5–5 tokens/s on an **M5 Mac**, not arbitrary Apple hardware; retains small dense core, pages selected experts. Unified Apple memory differs from discrete PCIe VRAM+host RAM.

**llama.cpp:** https://github.com/ggml-org/llama.cpp with upstream discussion https://github.com/ggml-org/llama.cpp/discussions/23324 (demand-paged expert slots, user PoC), https://github.com/ggml-org/llama.cpp/discussions/28248 (persistent expert slot pool and reported speedups), and command surface `--cpu-moe`, `--n-cpu-moe`, `--moe-cache-mib` on current docs. Precisely pin upstream revision, merged status and backend support; RFC measurements/forks cannot be promoted to upstream production or cross-platform facts.

The AI Mode text conflates VRAM, physical RAM, quantised weights, storage footprint, model active compute, and real speed. A 4.3 GB *peak memory working set* with a ~42 GB disk model does not mean an 80B model is compressed losslessly into 4.3 GB. On old discrete AMD gfx803 GPUs, BF16/FlashAttention/CUDA-specific speed figures are **not** transferable: use ROCm/gfx803 compatibility findings, validated Nix builds, verified numerics and explicit CPU fallback as independent gates. No assumption of a working GPU kernel.

### Third execution axis: compute, residency, and semantic control

Let a source MoE run be `F_theta(x,h)`. The out-of-core state extends the earlier whole learner:
`C_t=(model_revision,quant_revision,expert_file_manifest,residency_GPU,residency_RAM,page_cache,slot_map,LRU,dirty_generation,load_inflight,KV_cache,workspace,router_state,rng,backend,precision,provenance)_t`.
For each layer and batch, route IDs `E_t=TopK(router_theta(x_t))`; ensure the matching *weight revision and dtype* is fetched or cached in a valid slot, synchronize all DMA/fences, remap expert indices consistently, execute shared and selected experts, apply gated mixing, then commit cache transitions. A router decision is an input to the scheduler, not an excuse to change the model output. A trained-geometry hypothesis may *predict* expert locality/cache hits but does not prove it.

**Correctness:** under exact non-quantized arithmetic and a lossless storage codec, `F_out-of-core(x,h,C)=F_resident(x,h)` for the same model, routing, KV and outputs. Under quantisation/floating execution, replace equality by separately proved bounded per-layer error **plus** router-margin stability, or compare explicit deviations. Cache hits and misses must not change semantic output absent allowed numerical nondeterminism. When steering changes the pre-router state, recompute expert IDs and invalidate/reselect prefetches; pre-routing steering cannot be treated as post-routing neuron editing.

**Scheduling costs:** let `W_e` be bytes per selected expert, `M` cache misses, `B` effective SSD or PCIe transfer bandwidth, `L` per-fetch latency. A lower bound for sequential miss transfer is `T_transfer >= sum_miss(W_e)/B` (assuming sustained bandwidth B), plus command/latency and any non-overlapped compute, not a blanket model-speed theorem. Decode vs prefill have different unique expert working sets and cache effects; long context adds KV and/or DeltaNet-state requirements. Compare cold start, cold prefill, warm decode, worst-case routing and continuous operation; report SSD wear and read bytes as well as Joules.

### New exact remaining obligations (storage-tiered extension)

| ID | Priority | Proposed exact obligation | Proof / executable receipt |
|---|---|---|---|
| X01 | P0 | `originalQwenConfigWeightAndExpertManifest` | Pin official model, config, tokenizer, weight SHA and expert tensor offsets/layout |
| X02 | P0 | `routeSelectedExpertIsFetchedWeight` | Top-k selected global ID → exact matching loaded expert/revision |
| X03 | P0 | `expertSlotMapInjectiveForResidentSet` | No two live experts overwrite one occupied slot; alias/eviction lifecycle |
| X04 | P0 | `cacheHitMissObservationalEquivalence` | Same model output for hit, miss and eviction against resident reference |
| X05 | P0 | `cacheRevisionInvalidationSound` | Checkpoint/quant/adapter changes reject stale cached experts |
| X06 | P0 | `inflightReadFenceBeforeExpertExecution` | Fetch staging and DMA complete before kernel reads; no stale/torn weights |
| X07 | P0 | `boundedGpuRamWorkspaceAccounted` | Real peak device, RAM, cache, KV and workspaces under configured limits |
| X08 | P0 | `prefillUniqueExpertsCapacitySafe` | Batch/ubatch admits selected distinct experts or safe fallback; no silent drop |
| X09 | P1 | `streamedVsResidentQuantizedErrorBound` | Quant/codecs/numeric accumulation, calibrated tolerance and router-margin caveat |
| X10 | P1 | `steeringPrefetchInvalidationAndReplay` | Intervention before routing invalidates speculative expert selection and replays correctly |
| X11 | P1 | `expertCacheReplacementNoSemanticChange` | LRU/other replacement changes time and state, not model output |
| X12 | P1 | `storageBandwidthLatencyLowerBound` | Fetch volume, locality, transfer and sync overhead expressed with assumptions |
| X13 | P1 | `expertHitLocalityConditionalPrediction` | Geometry/semantic prior predicts routing locality **only when measured and held out** |
| X14 | P1 | `gpuKernelBackendNumericRefinement` | Supported backend and source kernel agreement; gfx803 separate release gate |
| X15 | P2 | `moeOutOfCoreFullExecutionBidi` | Whole-sequence source/model/cache/KV trace with admissible numerical semantics |
| X16 | P2 | `expertPrefetchParetoDominanceSound` | Peak VRAM, RAM, disk, prefill, decode, J/token, SSD traffic vs matched baselines |

**Finite donor delivered in this continuation:** `DASHI/Reasoning/MoEOutOfCoreStreamingFiniteExact.agda`: finite two-expert selected demand-fetch equality, count inequality, changed-revision/stale cache counterexample, and pre-route vs post-route steering counterexample. It is intentionally source-independent, with no imports from Qwen or a runtime; **Agda kernel run not yet obtained**. This is not X02–X06 original-source closure. Do not mistake a synthetic proof for measured SSD/VRAM performance.

### New phase and deliverable

**Phase 2b — storage-tiered execution (precedes any claim of small-RAM deployment):**
1. Pinned source owner atlas and exact weight manifest for original Qwen and relevant LILA/MoE variants (X01).
2. Thin model-generic `StorageTier/Cache/TransferSchedule` interpretation (X02–X08); reuse fibre-routing, history, PNF and future-quotient donors.
3. Kernel/codec correspondence in exact vs quantised modes (X09–X11, X14).
4. Empirical head-to-head benchmark on CPU-only and supported GPU (with hardware capability receipts): resident/CPU-offload/whole-layer-SSD/selected-expert-SSD/LRU+prefetch. Exact training model, prompt, sampling, seed, context, quant, batch and cache policy.
5. Deliver traces for peak GPU/RAM/disk, bytes read, cache hits/misses, prefill, decode, first-token latency, throughput, energy, output fidelity, SSD-write volume, and reboot/replay; meet X12–X16 before a deployment claim.

**New maximum cut:** A01 + M02/M03 + X01–X06 + S01/S04 are first. Then X07/X08/X10/X14 separate safe streaming from an apparently working but corrupt or OOM-prone implementation. Then X09/X11/X12 and measurements; then X13/X15/X16, jointly with original LILA geometric-efficiency gates. **Memory-optimisation and training-geometry are separable scientific claims**. Do not redirect LILA's original causal hypothesis into a mere GPU offload competition.

## 2026-11-11 correction: Federation is the architecture, not a downstream codec

**Recovered authoritative source owners:** DASHI PR #1442 (head `bbb8005b0920921f9dbb95d09f3e60058ceb02b0`, historical branch snapshot), LeechTransformer PR #4 (head `b9f83a638bc24bab046c252cc93a6362c0579666`), original `Docs/LeechFederatedCryptoNetworkBidi20261031.md`, `Docs/WholeSystemJointMoEConsumerQuotientMaxCut20261101.md`, `Docs/DASHILeech369TrialecticWaveSignedLearnerFederatedSystem20261031.md`. Do not silently conflate files on PR branch with modules merged to default branch. Earlier roadmap treated federation as a downstream deployment option and was **incomplete**. This revision restores the original multi-parent, signed-history, source/peer joint-state federation goal, and explicitly connects it to modern selected-expert SSD paging.

### Real machine constraint and interpretation

User-supplied Arch snapshot (2026-11-11): **3.27 GB free**, **5.24 GB available**. These are *reported host memory statistics*, not total installed RAM or the GPU's VRAM; `available` includes memory reclaimable from cache. Do **not** sum free and available. Do not claim a Qwen-80B checkpoint is resident or benchmarked on this host. Govern admission by measured `MemAvailable` minus a reserved safety margin and process peak allocations, swap/page-cache pressure, KV + hybrid state, and in-flight transfers. Design for a **small coordinator / expert worker** with configurable bounded cache and CPU-only fallback; do not assume the old gfx803 GPU is correct or that unified Apple-memory performance transfers to Arch Linux.

### Best-of-all synthesis: the same learner over multiple execution tiers

A coherent model combines:
1. **Original LILA/Leech geometry + DASHIg learning** and optional C2/C3/punctured-nine routing prior as a testable learned model, not a proven benefit.
2. **Sophontic paired intervention semantics**, distinguishing before-router steering (may change selected expert and location) from after-router steering (cannot change past route).
3. **Modern MoE** shared core plus routed experts with source-identical mixing and explicit top-k/capacity history and load balance.
4. **Swiftlet-like demand paging** of exact required experts from NVMe, with checkpoint/revision-keyed cache and memory admission.
5. **oLLM/AirLLM whole-layer streaming fallback**, when a model lacks exploitable expert locality or entire layer cannot remain resident.
6. **llama.cpp-like CPU/GPU hybrid** and quantization, explicitly separate numerical fidelity and observed performance from exact lossless transport.
7. **Original DASHI federation**: a local coordinator retains the global router, mixing weights and authoritative unselected histories; selected peers retain their own expert weights and optionally ACKed selected histories; transports carry one shared activation + only selected histories, or certified consumer-sufficient action/correction, NOT E copies of the shared activation. Selected peers return unweighted expert outputs and updated histories, or an explicitly witnessed alternative remotely aggregated output. Authenticated, versioned packet and history replay are mandatory.
8. **Content-addressed expert manifests and multiple peer replication** for availability with peer/version/precision/quant/adapter/capability admission; authenticated hashes are not themselves signatures; authority and observable equivalence remain separate.

**Placement is dynamic** on each layer and token (or microbatch): local GPU, local CPU, local RAM, local SSD, LAN peer, WAN peer or faithful dense fallback. Under placement decisions, expected cost is modeled as total latency/bytes/energy/quality, not an expert-count proxy. Compute route locally from authoritative complete historical state, then choose location. If expert is on a peer with already ACKed history, avoid retransmitting history; otherwise use a self-contained lossless snapshot or negotiated authenticated recovery. Peer scheduling/caches may be speculative; correctness must not depend on a speculative path being available.

### Formal state and same-object BIDI

`Z_t = (theta, router, x_t, (H_e)_e, modelRev, historyRev, quantRev, kv, optimiser, rng, signed_fibres, provenance)`
is the whole time-indexed model state. 
`D_t = (peers, expertPlacement, modelManifest, tierCache, routingIndex, ownership, leases, ACKs, transportSessions, resourceBudgets, failureState)`
is execution/distribution state.
`Exec(Z_t,D_t,intervention_t)` must observationally refine the original resident learner for each declared consumer, under explicit trust, liveness, finite-precision and data-plane assumptions.

For `S=TopK(r(x,H))`, `Q_S(Z)=(x,(H_e)_{e∈S})` is a **selected consumer quotient**, NOT a copy of full world state. It is admissible iff the relevant worker's computation factors through `Q_S`; the coordinator reopens the full state using its retained inactive histories. Routing depends on the *complete* history at the router's owner. If the router is remote or decentralized, the information/consensus obligation changes; do not assert universal selected-only packets.

The end-to-end response obligation includes exact router selection, expert identity/weights, current history, arbitrary peer/network failures and retries, the source-side mixture and output. Numeric correctness needs an explicit quantisation-error theorem and an expert-routing margin condition; signed orbit action is not the same thing as semantic disagreement or moral polarity.

### Existing failures must constrain the roadmap

Prior user-executed TinyStories pilot (as recorded in `WholeSystemJointMoEConsumerQuotientMaxCut20261101.md`): dense teacher heldout CE 2.58; `c2_invariant` 12-layer MoE CE 8.63, `punctured9_wave` CE 17.30. For that experiment the students failed to preserve model quality; no evidence that those learned students are deployable replacements. JQ1 2048-token captures reopened byte-exactly, but all frames chose zlib rather than purported signed/punctured/temporal reuse; under the chosen 1 Gb/s / RTT assumptions, ~11.42 ms JQ1 versus ~5.16 ms raw. **Do not** claim geometric compression or federation speed advantages from these traces. The recorded dense teacher is not already trained sparse MoE. A new experiment needs faithfully trained source-bound experts and matched quality.

### Additional exact remaining federation obligations (in addition to A/M/S/G/O/R/X/F)

| ID | Priority | Proposed exact lemma | Acceptance condition |
|---|---|---|---|
| N01 | P0 | `federatedWholeJointStateSingleOwner` | Router authority and all E histories represented once, not fictitious independent per-expert global states |
| N02 | P0 | `selectedQuotientRemoteExecutionSound` | For actual selected worker functions, packet projection/worker output/source aggregation commutes |
| N03 | P0 | `inactiveHistoryRejoinExact` | Inactive histories survive source-owned or ACKed peer-held selected execution |
| N04 | P0 | `remoteExpertRevisionQuantManifestAdmission` | Model, weight, tokenizer, quant, adapter, codec and history revisions match; otherwise reject |
| N05 | P0 | `boundedCoordinatorMemoryAdmission` | Free/available distinction, RAM reserve, cache, in-flight buffers, KV/workspace and OOM fallback |
| N06 | P0 | `peerFailureFallbackPreservesState` | Timeout, failed dispatch and retry do not double-commit recurrent history or corrupt outputs |
| N07 | P0 | `authenticatedSessionSequenceBinding` | AEAD/signature for identity, revisions, action, sequence and selected IDs; replay/out-of-order rejected |
| N08 | P0 | `selectedExpertReturnWeightsAtSource` | Unweighted outputs and updated selected histories returned; source mixes with authoritative weights |
| N09 | P1 | `remoteLocalCacheResidentBidi` | Same admitted token trace across placement choices, including revisioned cache misses and peer offload |
| N10 | P1 | `steeringRoutePlacementRevalidation` | Pre-router interventions force routing/placement/prefetch recalculation; post-route edits cannot retroactively route |
| N11 | P1 | `federatedLatencyEnergyParetoSound` | Latency includes queues, RTT, serialization, both directions, migrations, retries, compression, storage, compute |
| N12 | P1 | `historyLeaseAckDurability` | ACKed history reference has correct session, lease, generation and crash-recovery conditions |
| N13 | P1 | `privacyCompressionSideChannelBoundary` | Encryption is not optional on untrusted links; prevent information leaks via mixed-context compression and routing metadata |
| N14 | P2 | `multiPeerReplicaConsistencyAndAvailability` | Versioned ownership, replication, eviction and failover; no split-brain history commit |
| N15 | P2 | `signedPantsFederationConsumerGluing` | Independent face/signed fibre and local peer composition retain specified consumers without unjustified semantic claims |
| N16 | P2 | `sourceBoundFederatedLearnerBidi` | Real original LILA/student learner ⇄ exact execution trace ⇄ formal model, kernel and runtime receipts |

**Finite source artifact for this continuation:** `DASHI/Reasoning/FederatedTieredMoEFiniteExact.agda` has a two-expert, two-peer, two-revision admitted placement specimen, stale model/history rejection, and a pre-routing steering/owner-change example. Its placement equivalence uses the SAME trusted source weight oracle regardless of peer; this is an explicit idealisation, **not** a real network proof. Agda kernel not run; do not promote to N02, N04, N06 or N16 original-source closure.

### Revised max-cut / phase deliverables

**P0 (source and safety):** recover PR #1442 / Leech PR #4 original owners; check actual remote branch heads, verify original source and historical-data receipts; fix new finite module kernel errors (F01); complete A01–A04, M02–M03, S01–S04, X01–X08, N01–N08. *Deliverable:* versioned selected-expert execution and bounded coordinator memory contract with explicit failure fallbacks.

**P1 (effective federation):** tie X09–X14 with N09–N13, original geometry/steering source refinements and experimentally measured candidate policy. *Deliverable:* CPU/RAM/NVMe/LAN/WAN tier decision audit and source-exact identity/replay/transport checks.

**P2 (quality and scale):** repair the actual 12-layer student quality or retain dense fallback; ensure whole-model quality before claimed efficiency; compare SSD-only, RAM-offload, CPU offload, federation-only, hybrid federation+SSD, and selected-expert eager/demand with identical model and prompts, cold/warm runs and failure injection. *Deliverable:* Pareto fronts for CE/BPC, accuracy, first-token latency, steady decode t/s, p50/p95/p99, local peak RSS, GPU VRAM, per-peer RAM, SSD traffic, network bytes and Joules/token.

**P3 (proof closure):** X15–X16, N14–N16, F01–F02; actual crypto and backend implementations separately certified or precisely bounded. *Deliverable:* source-bound whole-system BIDI and a claim ledger showing exactly what is kernel-accepted, tested, inferred or still open.

**Decision policy:** The machine's 5.24 GB available is a *runtime pressure observation*, not a guaranteed allocation. Prefer a tiny local coordinator and on-demand *remote expert ownership* if sufficient peers exist; use NVMe or CPU expert cache only for admitted local experts. Local SSD paging remains useful when network latency makes federation worse; preserve full local fallback where possible. A fixed worldwide ranking of Swiftlet/oLLM/AirLLM/llama.cpp is unscientific because they optimize different memory, quality and transport boundaries.

**Attribution firewall:** Original LILA scientific architecture is Kornienko's. DASHI PR #1442 and LeechTransformer PR #4 contain user's existing federation work; Swiftlet/oLLM/AirLLM/llama.cpp and Qwen authors own their respective runtimes/model ideas. This document records reuse and proposed synthesis only, not an invention-of-MoE or original-source proof claim.

## 2026-11-11 topology maximum cut — miners, workers, model DAG and 512-wide intra-expert shards

### Restored original design and provenance

The original architecture is a **hierarchical, heterogeneous, economic federation**, not merely a local out-of-core MoE. Miners are independently operated service providers, each hosting zero or more CPU/GPU/NVMe worker nodes; workers are not automatically the authoritative economic owner. The inference model is a **content-addressed dependency DAG** of model→layer→(shared computation + selected MoE experts)→optional subexpert shards→aggregate→next layer, not a serial ring nor a four-tier cache diagram. Peer discovery, content routing and execution scheduling are distinct. Authenticated ownership/leases, CID-like immutable weights, model revision, and mutable signed histories have different identity and consistency rules. Restore original `512-wide` proposal only for a concrete expert with intermediate width 3072 (six shards, each 512), not as a universal property of all Qwen models.

Existing relevant donor owners:
- DASHI PR #1442 at head `bbb8005b0920921f9dbb95d09f3e60058ceb02b0`: `LeechJointStateConsumerQuotientExact`, `FederatedExpertTransportBidiExact`, `LeechGenericTopKActionTransportExact`, original full state/history and wire proofs. Source branch only until merged/read against exact head.
- LeechTransformer PR #4 at head `b9f83a638bc24bab046c252cc93a6362c0579666`: real model, hierarchy, selected-expert execution and network codec testing; its historical early sparse-student and network Pareto failures are retained.
- `DASHI/Computation/PathfindingFibreFamilyExact.agda`: distinguish BFS/Dijkstra/A*/BMSSP algorithm certificates; no proof of the topology scheduler without an actual instance.
- `DASHI/Computation/IncrementalShortestPathReopenFibreExact.agda`: typed cost-change/reopening state; reuse for dynamic capacity/peer failures without asserting a proven D* implementation.
- `DASHI/Interop/DistributedEpistemicPlaneSeparationExact.agda` and `DASHI/Reasoning/ContentAddressedVerificationBridgeExact.agda`: transport versus authority and content-identity proof boundaries.
- Existing JMD/CFT/ERDFA, PNF hyperfabric and ITIR typed-world materialisation: candidate future integration for immutable shard DAG and provenance, not a claim that current proof ingestion implements a federated model runtime. No mandatory new world ingestion or CI dependency.

### Actual network and computation objects

A time-indexed network is `N_t=(V_t,E_t,role_t,miner_t,capacity_t,link_t,placement_t,replica_t,lease_t,admission_t,schedule_t)`.
- `role : V → {coordinator,miner,worker,relay,storage}`, `miner : worker → provider` with capability ads CPU/RAM/VRAM/storage/backend and price/energy.
- Directed `E` contains feasible communication channels; separate authenticated peer ID from CID weight ID and from network locator.
- Link capacities `B_e`, RTT `L_e`, contention and failure process `F_e`; measure rather than assume identical links.
- `placement : shard × modelRevision → nonempty set of eligible peer replicas`, constrained by per-peer tier memory/cache/workspace and authenticated revision.
- `compute DAG` contains layer ordering, all selected expert branches, optional intermediate-axis subshard branches, local reductions, and source-owned mixing/history commit. Independent branches can overlap; the next layer waits for its actual dependency cut.
- Economic scheduling optimises constrained Pareto outcomes: cost/served token, p95/p99 time, steady throughput, availability, privacy, energy, and *same model quality*. Miner price is not equivalent to worker compute time.

For an expert `W_down φ(W_up x)`, splitting its intermediate axis into six disjoint 512-wide submatrices gives a sum of six shard outputs **only if** the actual activation is separable over that axis, bias is counted exactly once, and any model-specific gating/normalisation/cross-shard operations are placed at the correct side of the reduction. Nonlinear terms crossing shard boundaries break the naive identity. For standard elementwise FFN gate, shardwise contributions can be summed after independent paired up/gate projection; numerical floating reduction order is not exact.

For each selected expert set `S_t`, the scheduler may choose colocated execution or fan-out across worker nodes. Its makespan is bounded by critical dependency paths and actual link/compute schedules, not simply `Σ_e runtime(e)`, and not simply `max_e runtime(e)` when WAN aggregation and memory contention exist. Include a non-negligible coordination, serialization, retry and reducer term.

### Finite source-level implementation delivered

`DASHI/Reasoning/FederatedMinerWorkerTopologyExact.agda` (new in commit `0dde2c0ab9301faa8c589488d1fe5449a54fdca6`, subsequently strengthened at `b51b48d636f6c4424bef01eef02159ff2673ed51`):
- Directed `Link` and constructive `Reach` for coordinator→two miners→workers, including alternate-parent reachability.
- Separate economic provider `Miner` from physical `Node`; a worker may have multiple dispatch paths without changing who economically owns it.
- Six disjoint symbolic 512-wide shards covering a historical 3072-wide intermediate axis, complete fixed placement and coordinator reachability.
- Hierarchical two-miner sum and exact reference equality over natural-number shard contributions.
- **Compositional soundness:** if every executed shard has an actual per-shard equality receipt, the full hierarchical reduction agrees with reference on all six shards.
- **Negative control:** omission of the last shard changes the result; also a small abstract parallel makespan example 7 versus serial 12, not a general latency win.
- This source has not been run through Agda 2.9 in the current tool environment. It is NOT a source-bound Qwen/LILA runtime/real WAN proof; a Nat reduction is not floating associativity.

### Topology-specific exact remaining lemma ledger

| ID | Priority | Proposed exact lemma | Admission condition |
|---|---|---|---|
| TNET01 | P0 | `federatedMinerWorkerGraphWellFormed` | Arbitrary finite node type, role, ownership, unique ID, typed edges, graph version; witnessed admissible routes |
| TNET02 | P0 | `expertShardPlacementCapacitySafe` | Each shard weight+workspace/cache reservation and concurrent fanout respects distinct local memory tiers; overcommit rejects |
| TNET03 | P0 | `selectedExpertShardCoverageComplete` | For any selected expert, exactly the appropriate source-derived shard index ranges, no overlap/gap, one-off bias, valid activation/gate boundary |
| TNET04 | P0 | `parallelExpertFanoutAggregationSound` | Real per-shard output/quant/activation refinement and actual source-owned mixing/histories commute with reference model |
| TNET05 | P0 | `originalModelExpertTensorPartitionIdentity` | Actual model config and tensor manifest prove 3072↔6×512 on selected target or use a distinct per-model partition |
| TNET06 | P0 | `cidRevisionPeerAuthoritySeparation` | Immutable CID identifies bytes, revision identifies model compatibility, peer admission establishes trust, mutable histories use distinct generations |
| TNET07 | P1 | `multiParentDispatchHistoryConsistent` | Alternate route never grants conflicting commits, ACKs, or split-brain selected-history updates |
| TNET08 | P1 | `communicationAwareCriticalPathSound` | Scheduling's makespan estimate lower/upper receipts include link latency, serialization, per-node contention, reductions, queues |
| TNET09 | P1 | `replicaMigrationPreservesExpertIdentity` | Replica changes preserve signed weight manifest, quant mode, adapter version, immutable CID and admissible workspace |
| TNET10 | P1 | `networkFailureReplanningPreservesSemantics` | Retry/timeout/new owner with exactly-once committed semantic state or explicit abort/no advancement |
| TNET11 | P1 | `minerPriceReliabilityResourceParetoSound` | Price, latency, throughput, availability, energy, privacy and model quality defined and benchmarked under common traces |
| TNET12 | P1 | `aStarDAGScheduleRefinesSelectedCriticalPath` | Reuse existing pathfinding donor only after proving instance, admissible heuristic and actual DAG dependency semantics |
| TNET13 | P2 | `hierarchicalAggregationEqualsReferenceMoE` | End-to-end exact/reference or bounded numeric equivalence with real kernels and remote packets |
| TNET14 | P2 | `topologyOptimiserParetoOptimalUnderModel` | Objective/feasible-set formalisation, exhaustive finite solver or proven bound, no universal real-network optimality |
| TNET15 | P2 | `dynamicPeerReopenFibreSound` | Changed link/worker capacities reopen only invalidated schedule fibres with correctness and full dependency closure |
| TNET16 | P2 | `contentAddressedInferenceDAGWholeRunBidi` | Actual shard manifest, execution DAG, selected consumer/history and signed transport verified for complete token trace |

**Accounting update:** previous 66 planning obligations + these 16 topology-specific entries = **82** names in integrated ledger, not 82 independent unpaid kernel theorems. Finite examples contribute witness fragments to TNET01/03/04/07/08/13 but do not discharge those original-source obligations.

### Revised phase and deliverable gates — topology is now foundational

- **Phase 0 Source/identity:** existing PR #1442 + Leech PR #4, original Kornienko architecture, correct concrete 512 partition and content-addressed manifest. Deliver pinned owner/attribution and model graph receipt. Close TNET05/06 and A01 before any source assertion.
- **Phase 1 Formal network topology:** general finite node/edge/role/ownership graph, multi-parent routes, edge metrics, capacity and exact partition/coverage; reuse JMD/CFT for immutable model shard identity where verified. Deliver topology + admission kernel receipts: TNET01–03, F01.
- **Phase 2 Federated execution semantics:** distributed fan-out, original real expert subcomputations, local reducer, source aggregation, ACKed signed histories, failover; compose existing N01–N10 and X01–X11. Deliver per-shard→whole-output BIDI and fail-closed recovery: TNET04/07/09/10/13.
- **Phase 3 Communication-aware scheduler:** feasible placements, adaptive critical path, A*/incremental reopening, miner economic bids, peer pressure, topology fault handling. Deliver certified optimisation reference and benchmark scheduler: TNET08/11/12/14/15.
- **Phase 4 Original LILA/Sophontic learning:** matched whole-model loss/AdamW/Dust/steering/grokking quality and active compute. Deliver learned-student fidelity and interpretable matched controls: A/S/G/O/R obligations (unchanged; no displacement by transport engineering).
- **Phase 5 Memory-tier and federated Pareto:** same model on local resident / SSD streaming / RAM+CPU offload / single-miner multiworker / LAN / WAN / hybrid, identical prompt, context and fidelity; track memory availability pressure, tail latency, cost and storage. Deliver actual per-tier Pareto and negative-control receipts: X/N/TNET metrics.
- **Phase 6 Full trace source↔theory BIDI:** verified tokenizer, weight CID, hardware kernels, signed history, transport, steering reroutes, consumer observable quality. Deliver Agda kernel and executable integration receipts: F01/F02, N16, X15, TNET16.

**Highest-alpha dependency cut:** TNET05/06 + A01 → TNET01/02/03 + X01–X08 → TNET04/07/09 + N01–N10 + S01/S04 → TNET08/10/12/15 → TNET11/13/14/16 + full-source BIDI. Source-specific tensor partition and semantic equivalence outrank inventing a sophisticated placement optimiser.

### Source attribution and exact closure firewall

The six-512 partition is a user-recovered historical architecture proposal, not a property automatically verified for Qwen3-Next or an original theorem of another upstream project. Miners/providers and workers have distinct identities. Claim only the source-level finite Agda witness until Agda kernel run; claim only same-model implementation equivalence when matched source model and test/trace receipts exist; claim only a scheduling/efficiency improvement when latency, cost, quality, RAM and energy are actually measured. The historical TinyStories student-quality and JQ1 network failures remain live negative evidence, not cleared by a successful synthetic arithmetic proof.

## 2026-11-11 execution handoff — finite topology gate ready for local Nix run

**Implementation:** `DASHI/Reasoning/FederatedMinerWorkerTopologyExact.agda` finite two-miner/six-512-shard graph and conditional aggregation; `FederatedTieredMoEFiniteExact.agda` finite revision/placement admission; `MoEOutOfCoreStreamingFiniteExact.agda` finite source/stream/cache and steering examples. Added `scripts/federated_topology_gate.py` and `scripts/check_federated_topology.sh` on default branch.

**Actual locally executed evidence (assistant CPU environment):** 14/14 dependency-free Python tests PASS (synthetic reachability, provider independence, 3072→6×512 partition, gaps/duplicates, capacity, digest/revision rejection, exact integer elementwise-gated FFN shard reduction, duplicate bias negative control, parallel versus serial cost counterexamples, fail-closed release). Script runs without model downloads, network, GPU or third-party Python packages. The repository copy was checked by read-back from GitHub; the exact user's checkout has not been executed. No Agda binary / Nix environment exists in assistant container, so **Agda acceptance is pending the user's machine**.

**Run from repository root on the user's Arch/Nix machine:**

```bash
git fetch origin
git switch master
git pull --ff-only
bash scripts/check_federated_topology.sh --cpu-only
nix develop --command bash scripts/check_federated_topology.sh --kernel
cat artifacts/federated_topology/finite_preflight.json
```

A Nix devShell is already defined by the repository `flake.nix`; the checker uses its Agda binary and `agda --no-libraries -i .` on the three finite modules. No CI/Docker/venv assumption. It does not run on GPU or allocate significant model weights. If the full gate cannot be launched because Nix flakes/dependencies are absent, preserve the error rather than substituting a system Agda or claiming a kernel pass. The command is **ready to run**, not guaranteed to pass until executed on Agda 2.9.

**Receipt behavior:** CPU-only writes a synthetic JSON receipt with `agda_kernel_checked=false`, `actual_model_checked=false`, `network_measured=false`, `gpu_validated=false`, `release_admitted=false`. The full runner updates the Agda fields *only after* all three checks pass. Any failure exits nonzero. Return both the terminal output and that JSON receipt; never promote this finite gate to source-model or federation release.

**Next source-binding work after Agda receipt:** TNET05 original source weight tensor shapes and activation/partition identity; TNET02 memory capacities for actual worker hardware and available coordinator RAM; TNET04 source FFN/C2/Sophontic and quantized kernel BIDI; N02/N07/N12 authenticated remote joint-state transport, ACKed histories and failover; TNET08/TNET12 multi-peer critical-path scheduler; TNET13/TNET16 full original-token-trace and measured multi-peer cost. The earlier recorded student-quality and JQ1 transport failures remain failed gates, not cured by synthetic shard tests.

**Attribution/status:** existing LILA architecture belongs to Anatolii Kornienko; original signed-wave/federated transport owners remain in PR #1442 and LeechTransformer PR #4. The new topology/focused gate is DASHI-owned finite implementation and conditional proof infrastructure only; no external MoE model ownership, deployed federation or physical speedup claimed.

## 2026-11-12 attached local verification result — dependency failure before Agda; isolated Nix gate

**User-supplied authoritative receipt:** 14/14 CPU-only synthetic preflight tests passed in isolated clean worktree `/home/c/Documents/code/dashi_agda-master-topology`; JSON receipt recorded `tests_passed: null` due to old writer metadata, `agda_kernel_checked: false`, `actual_model_checked: false`, `network_measured: false`, `gpu_validated: false`, `release_admitted: false`. Never infer a kernel result from the 14/14 CPU test report.

**Observed kernel-run.log:** Nix failed building `zkperf-0.1.0.drv` because Cargo could not find `erdfa-publish/Cargo.toml` within the packaged source workspace (exit code 101). The shell environment derivation consequently failed: **Agda never started**. This is an environment/build packaging fault, not a failed proof, invalid theorem, GPU issue, or a reason to change the active dirty checkout.

**Focused correction on default branch:**
- `flake.nix` now offers `devShells.federated-topology` containing the repository-selected Agda toolchain, Python and Bash, but no `zkperfParse` dependency. Leave the broader default devShell/zkperf user environment unmodified.
- `scripts/check_federated_topology.sh` now uses `agda -i . -l standard-library` on all three finite modules. The earlier `--no-libraries` mode was unsuitable for library-dependent modules; use only the repository's declared standard-library configuration.
- After a passing CPU suite, the receipt writer explicitly stores `tests_passed: 14`. The `agda_kernel_checked` flag becomes true only following success of all three actual Agda invocations. `release_admitted` remains false.
- Source changes committed through GitHub; no machine-local service manipulation or Agda 2.9 verification by the assistant has occurred.

**Next local focused command** (when no earlier kernel service is running):

```bash
cd /home/c/Documents/code/dashi_agda-master-topology
git fetch origin
git pull --ff-only
nix develop .#federated-topology --command bash scripts/check_federated_topology.sh --kernel \
  2>&1 | tee artifacts/federated_topology/kernel-run.log
cat artifacts/federated_topology/finite_preflight.json
```

If continuing to run via a `systemd --user` persistent service, update its `ExecStart` to call the new `nix develop .#federated-topology` command, verify the old service has stopped, and preserve the service's journal and exit status. No competing Nix process or repeated full default-shell build should be launched.

**Current actual status:** CPU finite preflight PASS; focused Nix entrypoint SOURCE-WRITTEN; focused Nix build NOT YET VERIFIED; Agda 2.9 finite kernel acceptance OPEN; original LILA/Qwen and distributed execution OPEN. The mathematical maximum cut remains unchanged until we receive a real Agda result; do not spend time on unrelated zkperf repairs to discharge topology gates.

## 2026-11-12 verified finite gate and native-GPU-first policy correction

### Evidence state / provenance

User executed 14/14 finite CPU preflight tests and reports **three focused Agda 2.9 modules kernel/type-check accepted** in the established `run_agda29_parallel_check.sh` environment. The initial `zkperf` Rust package failure is superseded by the user's actual focused proof receipt, not interpreted as mathematical failure. Independently fetched GitHub commit `d92d9ac025a09ed0aab0b9eb922d00d5631ad7ab` from branch `fix/federated-topology-streaming-bound` repairs the streamed-selection `1 ≤ 2` witness by removing an extra `s≤s`. **Record kernel accepted as user-reported, not assistant re-executed**; preserve exact checker version, worktree and logs. Avoid falsely conflating the branch commit with master.

User requests **GPU native from now forward**. Interpret precisely: model *training*, model *inference*, distributed expert GPU kernels, and performance/efficiency claims must run actual native device operations. Retain Agda proof checking, topology Python finite tests, source inspection, static PyTorch skip-reason collection and CPU-oracle numeric references on CPU. CPU-substituted linear layers or mixed CPU/GPU hybrid may diagnose failure but are NOT accepted as native-GPU training or a successful GPU correspondence.

### Actual gfx803 source and fault-boundary status

Relevant owners: `chboishabba/gfx803_compat_graph` master commit `b40e54422a99c3e6683c3260f7f697fb0c8e7867`; `scripts/gfx803_opinfo_skip_reason_probe.py`; `docs/GFX803_OPINFO_SKIP_REASON_RECOVERY_20261112.md`. Existing real LILA bridge in `chboishabba/LeechTransformer` PR #4 (`scripts/gfx803_moe_gpu_gate.py`, `scripts/gfx803_repair_runtime.py`, `scripts/run_gfx803_lila_repair_gate.sh`); use the exact PR branch and commits. Preserve external Schaka WGM1/10.1 attribution and source hashes.

Original 1,774-case PyTorch OpInfo discovery retains 183 `unsupported` cases **without original skip reasons**: float32 147, complex64 30, int64 4, float8 e4m3fn 2 (`_scaled_mm`, `_scaled_mm_v2`). Separate 95 CPU-comparison from 88 variant-consistency. They are **not 183 demonstrated broken GPU operators**. Existing four fault candidates and three normal failures must be treated separately; any unresolved cases retain fail-closed classifications.

Static 183-node skip marker collection is **the next diagnostic gate**: inspect `skip/skipif/xfail` from exactly pinned PyTorch source, no test execution, immutable original audit and new receipt path. The original discovery scheduler only selects `unassayed` and has none left: **do not resume it to recover reasons**. Optional pytest-setup probing may initialise GPU fixtures; run it separately only on an idle and healthy RX 580. A setup skip or blocked call does not prove native op implementation.

Reported native gfx803 6.4 numerical discrepancy remains: first QKV input boundary differences and dense logits max error around 13.89 in existing on-card receipts. WGM1 QKV dispatcher demonstration is **partial**, and the 10.1 SGEMM shim has not been proved physically sound for a complete model through backward and matched AdamW updates. Never promote FP32 output parity of an isolated GEMM to full-model native training permission.

### Native GPU gates added to phase plan (new GPN obligations)

| ID | Priority | Exact remaining GPU-native acceptance obligation | Required receipt |
|---|---|---|---|
| GPN01 | P0 | `gfx803SourceRuntimeAbiAndKernelIdentity` | Pinned ROCm/Torch/device PCI ID/gfx ISA/DSO SHA, no mixed runtime |
| GPN02 | P0 | `gfx803OpInfoSkipReasonFaithfulClassification` | Exactly the 183 retained original identities and static/dynamic reasons, never overwrite discovery |
| GPN03 | P0 | `nativeGpuForwardEarliestDivergenceIdentified` | All original model operators, first divergent QKV input and subsequent logits against CPU oracle |
| GPN04 | P0 | `nativeGpuBackwardGradientReferenceBound` | Real device gradients for the actual dense/C2 model under numerical tolerance |
| GPN05 | P0 | `nativeGpuAdamwTrajectoryReferenceBound` | Original model and optimiser state with repeated device updates, bounded errors, no CPU GEMM substitution |
| GPN06 | P0 | `nativeGpuRepeatedExecutionStable` | 100-repetition or explicitly documented stress receipt, source hashes, no hangs/crashes/corruption |
| GPN07 | P1 | `nativeGpuSelectedExpertKernelBidi` | Original routed IDs, expert weights, shard outputs, source aggregation and true device dispatch |
| GPN08 | P1 | `nativeGpuMultiPeerSelectedHistoryBidi` | Actual model/history revisions, authenticated packet exchange, exact/quantised correspondence, local/remote GPU kernels |
| GPN09 | P1 | `nativeGpuResidentStreamingFederatedPareto` | Resident/SSD/CPU-offload (diagnostic-only)/LAN-peer/WAN-peer comparisons; native-GPU results clearly separated |
| GPN10 | P2 | `nativeGpuReleaseGateNoCpuSubstitution` | Whole-model inference and training/stability receipts; deny release on unresolved backend errors |

**Status:** GPN01–10 are new explicit proposed obligations, not existing kernel declarations or successful benchmarks. With the former 82-item planning ledger, there are now **92 named target obligations** (not 92 independently unpaid theorems). GPU native is an execution release gate, not an assertion that Agda itself runs on GPU.

### Phase/deliverable update

**Phase GPU0 — source and negative evidence (immediate):** run the static 183 skip marker recovery on exact pinned PyTorch source, inspect missing/conditional markers, preserve original matrices and Schaka attribution. Deliver reproducible classification + calibrated remediation queue. Avoid optional GPU setup until card idle.

**Phase GPU1 — native device correctness:** candidate 10.1 shim and/or verified WGM1 path must run the real dense/C2 forward, backward, repeated AdamW update and source/operator trace on gfx803 without CPU linear substitutions. Deliver device/kernel/ABI hashes, first-error locator, repeatability, negative controls and numerical tolerances. If failing, record first operation and remain fail-closed, without claiming LILA training.

**Phase GPU2 — model-native routing and subshards:** validate on the *actual* selected model that top-k router, six-by-512 (only if source tensor manifests admit), selected expert kernels and source aggregation execute on GPU; compare local resident and tiered variants. Deliver TNET05/TNET04/TNET13 + GPN07 acceptance.

**Phase GPU3 — federated native execution:** establish multi-peer GPU selected-expert work with signed history, replay/failure consistency and secure admission; measure full critical-path and throughput under N/TNET/X prerequisites. Deliver GPN08–09 and end-to-end original-model comparison.

**Release policy:** GPU-native training remains DENIED until GPN01 + GPN03–06 pass on a pinned original checkpoint. GPU-native federated release remains DENIED until GPN07–10 and whole-system source BIDI pass. Native-only objective does not erase finite proof and CPU reference lanes. Run no broad GPU tests concurrently with another GPU tenant. Use Nix, not Docker; local receipts are authoritative, CI not required.

### Highest-information next action

Run **only static** skip-reason reconstruction with the already committed command documented in `gfx803_compat_graph/docs/GFX803_OPINFO_SKIP_REASON_RECOVERY_20261112.md`, classify the 183 exact nodes first. Next focus a single real native GPU 10.1 or WGM1 whole-model forward/backward/AdamW fidelity trial when the RX 580 is idle and the corresponding Schaka runtime is actually installed. No speculative GPU throughput claim or immediate training launch.

## 2026-11-12 user correction: consume the provided native ROCm 10.1 environment now

**User directive:** The Schaka native 10.1 runtime is provided and working. STOP treating a new ROCm compatibility audit, 183-skip reconstruction, new platform build, or rediscovery of a GPU fault as a prerequisite for LILA/MoE/federation progress. Those belong to the independent gfx803 compatibility research lane and its owners. The already qualified native GPU wrapper is the baseline for this project. Never fall back silently to CPU GEMM, native 6.4, Docker or a fresh software install.

**Pinned upstream source:** `chboishabba/gfx803_compat_graph/nix/gfx803/schaka101-composed-candidate.nix` defines `gfx803-schaka101-python`, using the selected Schaka 10.1 relocated ROCm root, original imported Python venv, patched Torch wheel and SGEMM shim. Its documented composed store output is `/nix/store/vq1lgpc49im7qvvxgxabykyfs47l2ykb-gfx803-schaka101-torch-candidate-overlay`. Runtime loader and patched TopK ownership remain upstream Schaka/gfx803_compat_graph; no new ROCm correctness work is claimed here. This same store output also supplies a separate `gfx803-schaka101-pytest-python` for original OpInfo research; **do not run the pytest wrapper for ordinary LILA training**.

**Native execution launcher implemented:** `chboishabba/LeechTransformer`, existing PR #4 branch `experiment/consumer-preserving-multiscale-codec-20261031`, `scripts/run_native_schaka101_lila.sh` (commit `d2a1af062ece8071f4638b84771c2912a222bcef`). The launcher runs exactly the already-imported composed native PyTorch, enforces cuda:0 for four existing model-facing modules, rejects CPU GEMM substitution, does not rebuild or audit ROCm. Supports `--probe` (a tiny *actual native GPU tensor operation*) or `--module MODULE -- [real source-model args]`. The launcher has **not been executed on the user machine in this conversation**. Do not claim output before running it.

**Example on existing Leech PR #4 checkout**, with actual source model files/config/splits (do not invent missing paths):
```bash
cd /path/to/LeechTransformer
git fetch origin
git switch experiment/consumer-preserving-multiscale-codec-20261031
git pull --ff-only
bash scripts/run_native_schaka101_lila.sh --probe
bash scripts/run_native_schaka101_lila.sh --module scripts.train_signed_wave_experts -- \
  --checkpoint data/best_model.pt --config /actual/config.json \
  --token-ids /actual/train_ids.npy --layer -1 \
  --epochs 1 --batch 1 --experts 4 --top-k 2 \
  --expert-width 192 --transition-rank 24 \
  --route-geometry c2_invariant --output artifacts/native_c2_adapters.pt
```
This real module uses actual pretrained teacher checkpoint and training tokens. Paths must already exist and match the branch's original model; do not substitute synthetic examples. Due to ~5.24 GB host available snapshot, `--batch 1` is a conservative *starting choice*, not a guarantee of memory fit. Real model size, worker GPU VRAM, optimizer state, activations and CPU RAM are different resources.

**Roadmap priority reordering:** Formal Agda finite 3-module gate user-reported complete; keep F01 receipts. Native GPU path is present: run native LILA sparse student training first (source-trained original teacher) then export and evaluate heldout CE, then record selected expert traces and federation opportunities. Physical GPU runtime qualification is a *supplier-owned precondition already satisfied for the provided scope*, not a new DASHI work package. LILA-specific layer/tensor/activation binding (TNET05) and trained-student quality remain actual DASHI-owned open gates. Proceed to TNET02/TNET04/TNET13 and N02/N08 using the native model outputs. GPU-native scheduler/expert distribution still needs implementation and actual receipts: merely invoking a GPU in one process does not establish multi-peer federation.

**Reclassification of GPN lane:** GPN01–06 are externally supplied environment assurance / optional independent validation, not blocking the native LILA model experiment. GPN02 183 skip-reason research remains in gfx803_compat_graph and off the LILA critical path. GPN07–09 remain model-specific federation and performance goals. GPN10 is a project release/reproducibility status, not permission to ignore actual model crashes or data loss. Report failures if they occur, but do not preempt the user's working runtime with another general ROCm certification programme.

**Attribution/verification firewall:** Schaka owns relevant ROCm repairs, Kornienko original Leech-LILA, user/DASHI owns native model/federation adapters. Provided environment functionality is user-reported and source-supported; a new launcher commit is source-written, not a claimed physical run. Agda kernel proof, real model training, quality, distributed history and network claims remain independent.

## 2026-11-12 native GPU training results and observable performance/progress workstream

### User-run measured results (not an assistant-executed GPU benchmark)

Original Schaka ROCm 10.1 native execution on the **RX 580, HIP 7.16.26385** with the real dense teacher checkpoint and real token rows:
- Initial C2 **layer 1** smoke: 64 real token rows; 26 native GPU training batches; overall wall time 34.9 seconds; **reported peak memory 1.1 GB** (receipt source/allocator/RSS category not yet inspected); checkpoint SHA-256 prefix `404a3255`, suffix `fade280` (full hash not supplied in this conversation); resulting `c2_layer1.pt` / `c2_layer1.json` under `/mnt/truenas/comet-net/experiments/lila_native_launcher_smoke_20261112/`. Overall average **26/34.9 ≈ 0.745 batches/s** and ~1.342 seconds/batch, inclusive of setup and validation. Not a GPU-kernel-only throughput measurement. Exact tokens/s cannot be computed without actual batch row lengths/timing boundaries.
- Matched GPU quality experiment `/mnt/truenas/comet-net/experiments/lila_matched_quality_gpu_20261112/`: dense development CE **2.216053**, C2 gated development CE **2.564707**; dense wins by **0.348654 nats/token**. C2 final independent heldout hybrid CE **2.515797**; C2 strict student-only independent heldout CE **11.565138**. Both matched training arms used the same teacher, initial student-seed checkpoint, and exact **45 optimiser rows**, confirmed by user-reported matching SHA-256. **Not a teacher-free quality win or proof of source-preserving full-student compression.**
- LeechTransformer PR #4 commit `9138d8d29293416690caa97d07009a0acd4400e0` added native launcher support for dense matched control, reusing the same Schaka HIP device wrapper. Original Leech-LILA authorship: Anatolii Kornienko; independent runtime repair belongs to Schaka and the gfx803 contributors.

### Progress/throughput implementation (next rerun; source written)

On LeechTransformer PR #4 branch `experiment/consumer-preserving-multiscale-codec-20261031`, new `scripts/native_training_progress.py` and `scripts/summarize_native_training_progress.py`, integrated into `train_signed_wave_experts.py`, `train_guarded_moe_continuation.py`, and `train_early_layer_dense_control.py`. The progress callback logs **completed steps, input rows, next-token prediction targets, cumulative and interval steps/s, target-tokens/s, epoch, training loss, rough remaining time and `torch.cuda.max_memory_allocated/reserved`**; it synchronizes the device at reporting intervals to avoid recording mere queued work as completed compute. `--progress-every` defaults to five batches; optional per-run JSONL paths are atomic-latest and append-only. The training-summary tool combines measured receipt rows, without fabricating network throughput or model-quality fields. CPU-only source tests exist in `tests/test_native_training_progress.py`; **new tests and GPU runs are not yet locally executed by the assistant**.

For guarded C2 or dense matched model module, use the **existing native launcher**, preserving the original train/dev/heldout split:
```bash
bash scripts/run_native_schaka101_lila.sh --module scripts.train_guarded_moe_continuation -- \
  [the identical previously verified teacher/student/config/train/heldout/fit arguments] \
  --progress-every 5 --progress-jsonl /mnt/truenas/comet-net/experiments/NEW_RUN/c2.progress.jsonl

bash scripts/run_native_schaka101_lila.sh --module scripts.train_early_layer_dense_control -- \
  [the identical paired dense args, matching optimizer-fit rows] \
  --progress-every 5 --progress-jsonl /mnt/truenas/comet-net/experiments/NEW_RUN/dense.progress.jsonl

python3 scripts/summarize_native_training_progress.py \
  --progress /mnt/truenas/comet-net/experiments/NEW_RUN/dense.progress.jsonl \
             /mnt/truenas/comet-net/experiments/NEW_RUN/c2.progress.jsonl \
  --output /mnt/truenas/comet-net/experiments/NEW_RUN/throughput_summary.json
```
The bracketed arguments are placeholders referring to previously user-executed real paths; do not pretend they are actual shell arguments. The new logic must be checked locally before using it for a publication receipt. **Do not overwrite the prior source receipts** and do not rerun a substantive matched experiment until the new progress tests/checks are accepted. GPU kernels remain in the supplied ROCm 10.1 native runtime; no CPU fallback and no new compatibility audit.

### Performance measurement and exact remaining gates

| ID | Priority | Remaining performance/progress deliverable | Acceptance |
|---|---|---|---|
| PERF01 | P0 | `nativeGpuProgressStepAccounting` | Per-batch completed (synchronized) steps, epochs, samples, next-token targets, zero-overwrite structured log |
| PERF02 | P0 | `matchedNativeGpuThroughputDenominatorIdentity` | Same actual token lengths, train rows, batch, precision and timing scopes for dense and C2 |
| PERF03 | P0 | `nativeGpuAllocatorVsHostMemoryBoundary` | Distinguish GPU allocated/reserved peaks from NVML/rocm SMI or host RSS; no summation or false VRAM claim |
| PERF04 | P0 | `matchedGpuQualityCheckpointProvenance` | Full source hashes, matching 45 fit rows, teacher/student starting weights, dev vs independent heldout split |
| PERF05 | P1 | `nativeGpuTrainVsValidationTimingSeparation` | Kernels vs transfer, data loading, optimizer, calibration, evaluation and saving separate measured timing components |
| PERF06 | P1 | `grokkingProgressTimeToThresholdSound` | Quality threshold/censoring and epoch/step timestamps; no inference from final CE only |
| PERF07 | P1 | `nativeMoEFederatedCriticalPathTelemetry` | Per-shard/peer queue, copy, network, local/remote compute, reduction, cache hit/miss and synchronization |
| PERF08 | P2 | `throughputQualityMemoryEnergyParetoReceipt` | Matched CE/BPC and latency/tokens/s/VRAM/RAM/J/token, confidence intervals across seeds and reference-dense controls |

**Ledger accounting:** previous 92 planning names + eight PERF targets = **100 named obligations**, not 100 independently unpaid or kernel-accepted theorems. The finite Agda topology accepted by the user and the real native-GPU training are both genuine progress; neither proves the original training/quality advantage or physical federation performance.

**High-alpha next experiment:** Preserve the actual 45 fit rows and model versions; inspect the existing full TrueNAS receipts for matched loss/epoch traces and known token lengths; run a **single bounded same-data native GPU paired dense/C2 timing experiment with progress enabled**, then prioritise improving strict student-only CE 11.565138 before attempting SSD/remote expert throughput comparisons. The quality gap is a first-class blocker, not an artefact that networking should disguise.

## 2026-11-12 maximum cut — streaming overlap, bounded queues, and block-refinement federation

**Scope and mathematical correction.** Streaming *hides* independent network transfer behind other computation; it does NOT erase the causal path, queueing, WAN round-trip or synchronous denoising barriers. Model throughput, first-token latency, completed-block latency and energy separately. For an ideal two-stage steady-state system, a new independent item's interval is `max(transfer,compute)`; startup still needs `transfer+compute`. Arbitrary actual network and parallel multi-worker graphs require dependency-safe schedules and bandwidth/arrival assumptions, not this identity alone. In particular, block diffusion creates parallel candidate positions but may require multiple serial denoising rounds; no proof says diffusion universally outruns AR.

**New finite Agda owner:** `DASHI/Reasoning/FederatedStreamingBlockRefinementFiniteExact.agda` at commit `b47fc1df2e64a5d580405d25048ba684d0bc5d65`. The module provides: (i) concrete 8-unit transfer + 20-unit compute; first completion 28, pipelined three-item completion 68 versus sequential 84, steady-state interval 20, and bandwidth bottleneck negative example; (ii) intrinsically capacity-2 queue with enqueue/dequeue and explicit reject on full/empty; (iii) distinct immutable model revision, mutable history generation and block refinement generation, with stale cases rejected; (iv) conditional worker-reference refinement equality under per-input proof. **Agda module is SOURCE-WRITTEN, not yet kernel accepted by the user**. These are finite proof specimens, not a source-bound LILA denoiser.

**Executable scheduling specimen:** `scripts/federated_streaming_schedule_gate.py`, committed `7ac44144818767e88096534ccff0679018739323`, provides deterministic transfer/compute schedules, bounded queue backpressure and 12 synthetic test cases including causal-arrival/bandwidth negative controls and revision rejection. A locally developed equivalent executable was run with **12/12 tests passing**, including correction of a mistaken backpressure expectation; do not upgrade the newly committed repo copy to an independently verified check until run on user checkout. Its receipt explicitly declares no GPU, no network measurement, no diffusion-trained model, and no whole-model proof. Focused runner `scripts/check_federated_streaming_block.sh` at commit `56d3a1adf83cb89a08411f35a9f50e4830771ff9`; no Docker, no CI, no new ROCm qualification. It runs synthetic tests then the Agda proof using the existing local Agda installation, without unrelated Nix zkperf.

### New streaming/block-diffusion exact lemma and deliverable ledger

| ID | Alpha | Exact lemma / deliverable | Result and remaining physical weld |
|---|---|---|---|
| SBD01 | P0 | `streamingOverlapCriticalPathBound` | **Finite witness written:** 8+20 startup and 20-unit independent stream interval. **OPEN generally:** arbitrary DAG, RTT/bandwidth, arrival constraints, truly overlapping compute/transfer kernels, actual peer traces |
| SBD02 | P0 | `federatedPipelineQueueBounded` | **Finite witness written:** capacity-2 intrinsic queue saturation and empty/full rejects. **OPEN generally:** multi-peer resource budget, GPU memory reservations, bounded producer/consumer execution under failures |
| SBD03 | P0 | `denoisingHistoryRevisionConsistent` | **Finite witness written:** exact version-generation admission plus stale reject. **OPEN generally:** authenticated protocol, persistent full C2/C3 signed history, per-block/iteration exactly-once commits |
| SBD04 | P0 | `blockDiffusionExpertBatchSound` | **Conditional finite lemma written:** worker reference refinement equality preserves admitted value. **OPEN:** actual trained diffusion denoiser, transition kernel, tokenizer, mask schedule, source-expert tensor execution, numerical bound |
| SBD05 | P1 | `asynchronousRefinementConvergence` | **OPEN:** chosen denoising/update rule and contraction, bounded staleness, fairness, cancellation and counterexample for unsynchronised noncontractive transitions; cannot assert convergence from admission alone |
| SBD06 | P1 | `federatedDiffusionVsARResourcePareto` | **OPEN:** matched native-GPU prefill and block-generation throughput, latency, quality/task performance, iterations, bandwidth, per-worker RAM/VRAM and energy; no reuse of AR CE as diffusion training loss |

**Planning-count update:** previously 100 + 6 new SBD targets = **106 named ledger obligations**, which are programme gates, not 106 unpaid proof theorems. Each gate is explicitly split into finite specimen, original-source weld and hardware/empirical receipt. Previous 14/14 topology CPU and three Agda-2.9 finite modules remain user-accepted separately; do not count the new streaming module as kernel accepted until run.

### Updated phase-by-phase deliverables / dependencies

- **Phase 0 — Original source and identity:** retain Kornienko original dense/LILA weights and C2 history, source tensor shape, checkpoint/token provenance. New requirement: diffusion architecture is a separate student with a real objective and corrupt/refine transition; not a decoding reinterpretation of an AR checkpoint. Dependencies A01/TNET05/SBD04.
- **Phase 1 — Finite proof and scheduling bridge:** existing 3 Agda topology modules accepted; **check new Agda finite streaming module** and executable 12-case scheduling specimen; generalise communication schedule, backpressure and generation state. Deliver SBD01–03 source/Agda receipts, TNET01/TNET08 donor interface.
- **Phase 2 — Native GPU AR streamed baseline:** use supplied Schaka ROCm 10.1 on RX 580 and already trained C2/dense checkpoints; first run instrumented native AR model with *true asynchronous microbatching* (work that is independently ready) and a measured stalled/no-overlap negative control. Record GPU steps/s, completed tokens/s, PCIe/network transport, queue pressure and exact same quality. Native GPU runtime requalification is off the critical path. Dependencies PERF01–05, SBD01/02 source integration.
- **Phase 3 — Diffusion-trained branch:** implement separate diffusion tokenizer/corruption/masking schedule, iterative block denoiser and its actual native GPU training; evaluate original source-bound signed-history step changes and source-selected expert batching. Deliver SBD04 and explicit denoising iteration count; preserve AR control and failed historical C2 teacher-free quality.
- **Phase 4 — Multi-miner federation:** actual selected expert remote GPU compute on two or more workers, ACKed block/history generations, failover, bounded queues, dynamic retry/revision and multiple parents. Deliver SBD03/SBD05 when justified, N01–N16/TNET04/07/10/13/16; do not infer from finite queue examples.
- **Phase 5 — Native quality/resource Pareto:** compare matched (a) AR dense, (b) AR C2, (c) microbatched streaming AR C2, (d) trained block diffusion and (e) federated streaming block diffusion; measure same evaluation tasks, quality, model/storage bytes, p50/p95/p99 tail, tokens/s, GPU/RAM peak, energy and all physical network bytes. Deliver SBD06/PERF07–08, plus source-wise attribution. AR CE and denoising loss must never be naively compared.
- **Phase 6 — End-to-end BIDI and promotion:** original source ↔ Agda ↔ native GPU kernel ↔ authenticated per-worker packet ↔ history reconciliation ↔ observed quality/latency, no skipped source bindings. Deliver F02, TNET16, SBD01–06 physical/source closures as earned.

**New max-cut priority:** `new Agda kernel + scheduler receipt` → `native-GPU streaming AR same-checkpoint baseline` ∥ `original tensor partition/quality diagnosis` → `real block-diffusion model+training` → `multi-peer revision-safe streaming` → `quality/resource Pareto` → `whole-model BIDI`. The already measured dense development CE 2.216053, C2 gated 2.564707 and strict C2 student-only heldout 11.565138 remain baseline negative controls; adding a diffusion branch is an independent research hypothesis, not a way to relabel those scores.

**Focused local test:**

```bash
cd /home/c/Documents/code/dashi_agda-master-topology
git fetch origin
git pull --ff-only
bash scripts/check_federated_streaming_block.sh --cpu-only
# In the already working Agda-2.9 environment (do not rebuild ROCm):
bash scripts/check_federated_streaming_block.sh --kernel
```

Preserve output and first type error. Do not rerun when a separate kernel-check service is actively using that worktree; preserve the user's dirty original checkout. No background execution or native GPU run was performed by this authoring change.

### Post-ledger implementation extension: finite block-batch refinement transport

Agda source `DASHI/Reasoning/FederatedStreamingBlockRefinementFiniteExact.agda` additionally provides `mapResult` and `blockBatchRefinementPreservesReference` for arbitrary finite lists of independently proven source-equivalent refinement values (commit `133599d88ec8df0bf3320bf377add3e1780311ce`). This materially strengthens the conditional SBD04 specimen from a single proposal to a batch, **without assuming tokenwise independence of the actual denoising neural network**. It only preserves results when the required per-element equalities are supplied; proving the original model has that property is still OPEN. Requires local Agda kernel receipt.

## 2026-11-12 next cut: native-GPU selected-expert streaming, original source interface

**User-run verification admitted:** original published `origin/master` at `ba6af7cd2` — **12/12** synthetic scheduling tests PASS; Agda 2.9 `FederatedStreamingBlockRefinementFiniteExact.agda` kernel PASS, recorded by user in `artifacts/federated_streaming_block/agda29-parallel-20261112-212131-DASHI__Reasoning__FederatedStreamingBlockRefinementFiniteExact.agda.log` of the isolated topology worktree. Thus SBD01–04 finite witnesses are verified; **general source, physical WAN and diffusion-model gates stay OPEN**.

### Native-GPU implementation, without ROCm rebuild

New native source experiment on `chboishabba/LeechTransformer` PR #4 branch `experiment/consumer-preserving-multiscale-codec-20261031`:
- `scripts/native_streamed_selected_experts.py`, integrated with the existing Schaka ROCm 10.1 launcher `scripts/run_native_schaka101_lila.sh` and original `HistoryOrbitMoE.execute_selected`.
- Loads exact **dense teacher + full MoE student** checkpoints and real token-ID windows via existing `load_pair`; captures the actual selected teacher's layer normalized activation and computes source-owned expert routing/weights from `HistoryOrbitMoE.step`.
- Captures a **finite independent microbatch** from each token row's first normalized position, with **explicit zero initial history for every row**; captures original source expert output and selected updated histories. This is real checkpoint-derived expert compute, not complete autoregressive stateful generation or an existing trained diffusion denoiser.
- Pins CPU copies of the admitted activation, selected IDs, selected histories and source weights, then compares **sequential CUDA H2D copy+selected expert compute** with **two-stream asynchronous H2D staging + GPU selected-expert compute**; bounded in-flight queue, CUDA events for dependencies, actual event completion before observation. Both alternatives execute the *same* selected GPU expert math and compare with source outputs/history under explicit tolerances.
- Records repeats in alternating sequential/pipeline order, actual elapsed seconds, microbatch/s, row/s, staged bytes/s, allocator peak allocated/reserved and full source checkpoint/token SHA-256. Distinguishes source preparation time (outside timing), actual GPU workload, and PCIe-only staging from physical WAN/network, end-to-end tokens/s, production distributed execution or teacher-free quality. No CPU GEMM fallback, no new ROCm qualification.
- `tests/test_native_streamed_selected_experts.py` exercises actual selected-source parity and refusal for duplicate IDs on CPU-constructed unit data; these tests are code-written, not yet run by user. A GPU run has **not** yet been observed.

**Run a bounded native-GPU experiment** with real existing source paths; do not use `c2_layer1.pt` if it is merely an adapter rather than a full trained MoE student checkpoint:
```bash
cd /path/to/LeechTransformer
git fetch origin
git switch experiment/consumer-preserving-multiscale-codec-20261031
git pull --ff-only
# Unit tests (no GPU performance assertions):
/nix/store/vq1lgpc49im7qvvxgxabykyfs47l2ykb-gfx803-schaka101-torch-candidate-overlay/bin/gfx803-schaka101-python -m unittest discover -s tests -p 'test_native_streamed_selected_experts.py' -v
# On the already-working Schaka 10.1 native GPU wrapper:
bash scripts/run_native_schaka101_lila.sh \
  --module scripts.native_streamed_selected_experts -- \
  --teacher /actual/teacher.pt --student /actual/full_student.pt \
  --config /actual/config.json --token-ids /actual/real_tokens.npy \
  --layer 1 --batch 2 --max-rows 16 --queue-depth 2 --repeats 3 \
  --output /mnt/truenas/comet-net/experiments/lila_streamed_selected_20261112/receipt.json
```
The paths `/actual/...` are **placeholder** paths and must be substituted with the previously used real checkpoint, student, tokenizer and config paths, preserving identity; do not invent physical inputs. The output directory must be fresh and no competing GPU jobs should share the card. The command is a runnable **bench only**; it is not a background service, training launcher or live federation. Source-written only until host receipts arrive.

### Exact delta to existing maximum-cut ledger

No additional named programme lemma IDs; these implementations contribute partial *source-interface* witnesses to:
- **SBD01/TNET08:** actual native CUDA copy/compute pipeline, queue depth, event completion and synchronisation. **Open:** measured useful overlap and general multi-device critical path, WAN RTT/throughput, network packet dispatch.
- **SBD02/TNET02:** finite in-flight queue and real CUDA allocator peak measurement. **Open:** multi-peer RAM/VRAM/workspace reservations and failure-aware backpressure.
- **SBD03/N01/N07/N12:** selected history source update equality for independent zero-initial-history microbatches. **Open:** authenticated, ACKed, durable *recurrent* signed history with reordering/retry/peer failure.
- **SBD04/TNET04/TNET13/GPN07:** actual source-owned IDs and weights paired with `execute_selected`, compare output and updated selected histories on same HIP device. **Open:** whole-model tensor/denoiser source BIDI, full top-k traces and trained diffusion model.
- **SBD05:** asynchronous iterative denoising convergence still **OPEN**. No iterative denoising is yet implemented.
- **SBD06/PERF07–08:** matched AR microbatch/copy throughput receipt pending. Diffusion-vs-AR resource Pareto remains **OPEN**.

**Next after a passing same-GPU receipt:** add an authenticated two-process/two-device transport using original `federated_authenticated_session.py` and JQ1 selected-state packets, with acked generations and original observer equality; then measure actual WAN/local-link latency overlap on real remote GPU peers. Independently implement a truly trained block-diffusion model and measure its quality/iterations; do not conflate AR microbatch streaming with diffusion training.

**Programme scope:** remains **106 named roadmap targets** from the previous ledger, including 6 SBD targets. Native LILA quality negative controls (dense dev CE 2.216053, C2 gated dev CE 2.564707, strict C2 student-only heldout CE 11.565138) remain unchanged. These new GPU streaming executors are not yet an improvement claim.

## 2026-11-13 accelerated maximum cut: native selected-expert federation across independently owned GPU workers

### Accepted native evidence and change of emphasis

The user's completed original RX 580/HIP 7.16.26385 source-selected PCIe experiment (`/mnt/truenas/comet-net/experiments/lila_streamed_selected_20261113/`) processed **16 real token rows, eight microbatches, three repetitions**, with exactly **zero selected expert output and selected-history error**. **Pipelined 168.5 microbatches/s, sequential 188.1 microbatches/s**, or `168.5/188.1 = 0.8958` (~**10.4% slower pipelined**). This was **one-card pinned-host/PCIe staging** and is now an important negative performance control, not an indication that worker-to-worker network overlap has been proven. No further tiny same-GPU overlap loops are on the high-alpha critical path.

### Larger integrated source implementation

`chboishabba/LeechTransformer` existing PR #4 branch `experiment/consumer-preserving-multiscale-codec-20261031` now contains the following mutually integrated implementations, source-written in the present round:

1. **Original expert source weld**: `models/history_orbit_moe.py` adds `execute_selected_subset`; the original `execute_selected` signature and full-k requirement remain the default. The new optional subset mode permits each worker to execute only its *own nonempty subset* of the original top-k expert IDs without rerouting or reading inactive histories. Applies the original orientation scorer, FFN and transition modules; returns unweighted outputs and only selected updated histories, preserving source-owned mixture weights.
2. **Persistent one-peer native transport**: `scripts/native_federated_selected_worker.py` implements a bounded framed TCP session with monotone HMAC-SHA256 request/reply numbers, model SHA-256, history revision, exact JQ1 selected activation/history packet and signed worker output/history payload. The source verifies and recombines unweighted responses; inactive histories remain authoritative; bounded outstanding request window and per-request RTT/bytes/throughput receipts. Worker loads full student state on **CPU** and places only needed orientation + assigned expert FFNs + assigned transition modules on worker **GPU**, rather than whole LeechGPT.
3. **Actual multiworker owner graph**: `scripts/native_multiworker_coordinator.py` reads a source-reviewed owner manifest and requires >=2 workers, all original E expert IDs covered exactly once, no overlaps; creates independently authenticated TCP sessions per worker, sends selected subsets to their owners, overlaps in-flight rows under a configured bounded window, collects per-peer unweighted results and selected history updates, restores original weighted reduction and checks all originally inactive histories remain unchanged. Releases source session acknowledgement only after full peer-reduction and history parity; signs worker self-reported GPU/HIP identity, refuses nonnative execution. Source records physical per-peer request/response bytes, per-worker completed requests, row throughput, and p50/p95/p99 row latency; backend is the existing working native Schaka 10.1 wrapper. **No test of multiple physical GPU hosts occurred in this assistant session.**
4. **Tests and one-command focused check**: `tests/test_native_federated_selected_worker.py` (TCP/HMAC/JQ1 session, tamper/replay/stale-model negatives), `tests/test_native_multiworker_coordinator.py` (real original `HistoryOrbitMoE` selected subset parity; two separately owned real socketpair workers; duplicate/missing owner negatives), and `scripts/check_native_federation_contracts.sh` (all three selection/transport/multiworker suites under pre-existing Schaka Python). They are **SOURCE-WRITTEN, not yet user-kernel/host executed**. Test CPU tensors are oracle checks only, not native GPU deployment or another ROCm qualification campaign.
5. **Coordinated 2+ GPU host handoff**: `docs/NATIVE_MULTIWORKER_FEDERATION_INTEGRATED_20261113.md` gives the complete one-run peer setup, SSH port forwards, secure per-peer key/session handling, full student SHA equality, ownership manifest, native worker and coordinator commands. Related one-peer integrated protocol runbook: `docs/NATIVE_SELECTED_FEDERATION_INTEGRATED_20261113.md`. These are explicit source-to-execution contracts, not completed deployments.

Attribution: original Leech-LILA architect Anatolii Kornienko; Schaka/gfx803 contributors own ROCm 10.1 native repairs and patched Torch; DASHI/user integration owns the new federation runtime and Agda correspondence. Native GPU only for actual execution; CPU for finite Agda and synthetic contract oracles.

### Updated exact maximum-cut gate matrix (existing IDs; no artificial new obligation count)

| Gate | Implemented source / verified physical | Exact remaining source/physical closure |
|---|---|---|
| **SBD01 / TNET08** | 12/12 finite scheduler + Agda2.9 PASS; GPU PCIe 16-row parity PASS but pipeline 10.4% slower; multi-peer queue/window code written | True remote multi-GPU measured overlap and critical-path schedule under controlled RTT/bandwidth; actual heterogeneous route/queue telemetry |
| **SBD02 / TNET02** | Intrinsic finite queue PASS; real per-peer outstanding window and only owned expert FFN/transition GPU residency source-written | Actual peer GPU/CPU/SSD capacities, memory/workspace reservation, congestion and failures, bounded physical schedule proof |
| **SBD03 / N02/N07/N12** | Finite revision gate PASS; JQ1 + per-peer HMAC/session + monotonic response, output/history parity-before-source-ACK implementation written | Actual per-token recurrent signed history across windows, authenticated persistent history revision/lease, replay after process failure, atomic/durable ACK/rollback and replica consistency |
| **SBD04 / TNET04/TNET13** | Finite conditional batch theorem PASS; original `HistoryOrbitMoE.execute_selected_subset` and exact source mixture recombination implemented; two-owner contract tests written | On-card multiworker original-model receipt, whole-output history traces and float bounds, actually trained diffusion transition correspondence; whole-model source equivalence |
| **TNET03/TNET05/TNET16** | Actual source expert ID partition and disjoint ownership implemented; all E source manifest coverage validated | Arbitrary original trained tensor dimensions, subexpert/neuron weight partition/reconstruction, original source DAG and whole-run bidirectional semantic equivalence |
| **GPN07–09 / PERF07–08** | Native Schaka backend reused, per-peer byte/time/performance fields written; earlier one-card negative performance measured | Multiple physical GPUs and peer links, measurable throughput/latency/energy and same-work local baseline, dynamic membership/replication/placement |
| **SBD05** | Still OPEN | Specify block refinement and real asynchronous update rule; bounded-staleness convergence or correct failure/counterexample theorem |
| **SBD06** | Still OPEN | Genuine trained block-diffusion student and matched AR/diffusion output quality/resources; no reinterpretation of autoregressive CE as denoising loss |
| **Learning quality A/O/R** | Native C2 trained; matched dense dev CE 2.216053 vs C2 dev CE 2.564707; strict heldout student-only CE 11.565138 | Fix original strict student quality, quality-preserving source model replacement and fair dense negative controls; no teacher-free promotion |
| **F02 / full end-to-end BIDI** | Finite Agda + original selected methods + authenticated runtime bridges present in separate stages | Prove/source-check actual checkpoint, real recurrent history, cross-peer failures, physics/performance receipts and observer-level consumer preservation for one whole run |

**Ledger count unchanged:** previously 106 named target obligations, including the six new SBD gates; subheadings here are progress against existing named targets, not more artificial lemmas. The Agda kernel checked finite module remains distinct from newly source-written multiworker code and physical deployment.

### Revised deliverable phases: reduce micro-sprints, integrate larger cuts

- **P0 — Done / negative control accepted:** finite 3-module federation topology Agda, finite streaming/revision Agda2.9 PASS, 12/12 scheduler PASS, real native C2 training and matched quality comparison, real source-selected PCIe two-stream negative performance result. No further ROCm qualification is required as a precondition.
- **P1 — Source-integrated now; one host gate pending:** user executes `bash scripts/check_native_federation_contracts.sh` once on the updated Leech PR branch. Fix the first actual failure if any; no proof promotion without run receipts.
- **P2 — Physical 2+ peer tranche (one integrated run):** use the exact commands in `docs/NATIVE_MULTIWORKER_FEDERATION_INTEGRATED_20261113.md`, with separate working native GPUs, actual complete matched student checkpoints and 256 real rows. Establish auth/source mixture/history parity and peer RTT/throughput/bytes, contrasted with source-matched local selected expert execution. Do not use the already-slower 16-row PCIe benchmark as the remote baseline.
- **P3 — Real recurrent/historical semantics + fault tolerance:** carry *all* per-token signed history with source authoritative generations/ACK; make replay, stale reply, peer failure, restart and bounded producer/consumer queue tests integral. Join N/TNET/SBD source BIDI under original model semantics. Move from one-position independent rows to authentic stateful sequence execution.
- **P4 — Original shards, persistent resources and scheduling:** per-expert, then within-expert actual tensor placement under real GPU/CPU RAM/SSD; proof/receipt for selected-shard coverage, evictions, predictive prefetch, bandwidth contention and makespan optimisation. Do not assume six×512 shape is native to every target model.
- **P5 — Native block-diffusion lane:** separately *train* a real block denoiser with matching text/task-quality evaluations and signed-history transition, then compare streamed AR, trained diffusion, and distributed diffusion at matched resources; address SBD05 convergence and SBD06 resource Pareto.
- **P6 — Final end-to-end source correspondence and release decision:** original source/weights/histories ↔ Agda theorem ↔ original worker output ↔ network-authenticated/ACKed state ↔ measured quality/performance. Retain negative controls and attribution.

### Current handoff / explicit not-done list

Use the same working Schaka native 10.1 environment, without rebuilding it. On Leech PR #4 checkout:
```bash
bash scripts/check_native_federation_contracts.sh
```
Then, **only when two independently operable native GPU worker hosts exist**, use the complete multi-host launch in `docs/NATIVE_MULTIWORKER_FEDERATION_INTEGRATED_20261113.md`. Single-host loopback with two processes cannot establish hardware parallelism and may exceed RX 580 memory. New source code was published and checked for presence, but its regression suites, real sockets between machines, native multi-worker throughput, durable history and diffusion training were **not executed by the assistant**.

**Highest alpha remaining:** P1 + P2 integrated protocol/kernel acceptance → P3 faithful recurrent and durable selected-history semantics → P4 real tensor/source partition and memory Pareto ∥ P5 genuinely trained block diffusion → P6 original semantic/quality/resource end-to-end convergence. This is a larger unit of work than prior 16-row GPU overlap microbenchmarks and avoids more generic ROCm correctness audits.

### 2026-11-13 final accelerated-tranche correction — no duplicated source expert compute during throughput evaluation

Follow-up on PR #4 integrated multi-GPU code:
- `models/history_orbit_moe.py` source-written `select_source_experts(x,history)` factors out the **unchanged exact original routing prefix** of `step`. For source-issued remote work, obtaining top-k IDs/mixture weights must not unnecessarily evaluate local FFNs/transitions in parallel with executing the same operators on remote workers. Existing `step` now directly reuses `select_source_experts`; route-only regression test covers raw and C2 routing.
- `scripts/native_multiworker_coordinator.py` uses route-only dispatch ordinarily; `--source-verify-every 16` (default) computes full reference experts on 1 of 16 real rows, preserving parity checks while greatly reducing redundant source FFN computation. `--source-verify-every 1` is full-parity admission (all rows), `0` is throughput-only with **no source-parity claim**. Record exactly how many rows were checked and null error maxima when no rows were checked. Each request still gets peer HMAC/revision, tensor shape, ownership, finite output and inactive-history checks.
- The report now distinguishes source normalisation/router/verification overhead, physical network bytes and p50/p95/p99 row times, worker-self-reported HIP identity, and unproven physical GPU independence. Exact source↔peer equality is established only for sampled rows; `completed_rows_per_second` is an actual *source+network+worker* workload measure, not GPU-kernel-only or full autoregressive tokens/s.
- Tests at `tests/test_native_multiworker_coordinator.py` contain `test_route_only_matches_original_step_without_expert_execution` and the two-owner socket/HMAC source reduction test. Both are written but **not executed on the user's hardware in this turn**.
- Final implementation head on LeechTransformer PR #4 is at least `e90fda4bc482fd7bb903e00f3980a1aae34e4567`, the integrated multiworker runbook and source changes; Dashi roadmap remains the separate formal programme authority. **No new numeric physical result is claimed**.
- User request to stop incremental microbenchmarks: the immediate deliverable is **one integrated 256-row, two independent native GPU hosts, bounded window 8, source verification every 16 rows**, with real full student checkpoints, actual peer identity/ownership, authenticated SSH tunnels and original source metric receipts. This replaces the 16-row same-card PCIe testing loop as the critical path.

**Explicit remaining after this source tranche:** 1. Local contract tests/source toolchain execution and repair if necessary; 2. Real multi-host GPU run with physically distinct devices; 3. Genuine recurrent history, persisted atomic ACKs, peer retry/replication and authenticated membership; 4. Real subexpert tensor partition and physical memory Pareto; 5. diffusion-trained model and convergence gates; 6. full original execution ↔ Agda proof ↔ GPU/peer semantic BIDI and comparative quality. The user's earlier 12/12 scheduler and Agda2.9 finite module remain ACCEPTED. The previously measured 168.5 vs 188.1 microbatches/s local pipeline negative control remains unchanged. Ledger retains **106 named obligations**, not newly invented gate counts.

## 2026-11-13 integrated latest-PR audit and accelerated multiworker blocker repair

**Source audit performed first, not a duplicate small-benchmark sprint:** Actual connected GitHub PR #4 `chboishabba/LeechTransformer` at `e90fda4bc482fd7bb903e00f3980a1aae34e4567` already contained `HistoryOrbitMoE.select_source_experts`, `execute_selected_subset`, authenticated `native_federated_selected_worker.py`, `native_multiworker_coordinator.py`, two-owner test/socket integration and a 256-row multi-host runbook. DASHI `master` already had its source-integration roadmap at `963c50be780d056be30e4f3e34b42cccedea99de`. Do not recreate those modules or spend more rounds re-measuring the smaller 8-microbatch staging experiment.

**Physical user result (13 Nov):** native RX 580/HIP 7.16.26385, actual selected expert and updated history zero-error parity, 16 original token rows, 8 microbatches, 3 repeats. Sequential **188.1 microbatches/s** vs PCIe pipeline **168.5 microbatches/s**, pipeline `168.5 / 188.1 ≈ 0.896` = **10.42% slower**. Hardware-accurate negative performance witness. Cannot claim beneficial streaming overlap for that workload. Still cannot infer inter-host performance.

**Critical integration repair made in PR #4 during this audit**:
1. Worker `load_student` had an escaped Python comment swallowing `return model`, making actual worker loading return `None`; repaired.
2. Worker `serve` used undefined `owned`, preventing normal startup; now strict `parse_owned_experts` validates the intended IDs and moves only owned expert FFN + transition modules and shared orientation to native GPU, retaining full source checkpoint in CPU memory.
3. The multiworker default `--source-verify-every 16` route-only path set original source reference `None` but used `torch.zeros_like(reference)`, causing failure. New `reduce_source_selected` performs source-ordered weighted reduction, validates vector dimensions/finiteness and expert coverage, compares source output/history only for sampled rows, and leaves unverified error values **None**, not fake zero or invented parity.
4. Manifest now rejects duplicate peer endpoints, sessions and key-file paths, in addition to missing/overlapping expert ownership.
5. Source tests expanded with sampled+unsampled reduction parity, malformed expert ownership/manifest identities, and a **32-row, two-worker authenticated socketpair/JQ1/monotonic session test with 4 sampled source-parity rows**. The local CPU model tests remain labelled protocol oracles, not physical native federation receipts.
6. Fair native benchmark comparator `scripts/native_local_selected_baseline.py` now runs the **same 256 real source rows**, source normalization, original top-k routes, model layer, and verify-every-N policy with local resident GPU selected experts. New `scripts/compare_native_selected_federation.py` accepts local vs remote receipts only if original teacher/student/token hashes, layer, rows, source sampling and verification counts match; it reports the observed throughput ratio without claiming independent physical hardware attestation.
7. `scripts/run_native_schaka101_lila.sh` now admits the local comparator. The consolidated `scripts/check_native_federation_contracts.sh` includes source-selected, peer protocol, two-owner and fair-comparator suites.

**Evidence boundary:** These corrective commits and source tests were published and read back; the assistant did NOT run new native GPU jobs, new host contracts or physical SSH/TCP worker tests on user hardware. In particular, a tested single-GPU executor is **not** proof that these newer modules passed on two hosts; physical acceptance remains OPEN. Preserve author attribution and existing Schaka Nix closure; no generic ROCm requalification.

### Revised integrated P0–P6 deliverables (no new artificial named gate count)

| Phase | State | High-alpha next deliverable / exact remaining |
|---|---|---|
| P0 original finite and one-card native baselines | **ACCEPTED** | Agda 2.9 12/12 streaming + finite topology, real native C2 and quality experiment, negative 168.5/188.1 selected PCIe overlap; no rerun needed |
| P1 original source multiworker transport and local contract integration | **CODE REPAIRED / LOCAL TEST OPEN** | Run `bash scripts/check_native_federation_contracts.sh` once. If it fails, repair first real compiler/runtime/contract cause; do not claim the source as accepted until tests pass |
| P2 genuine physical native multiworker and same-work economic comparator | **SOURCE-WRITTEN / PHYSICAL OPEN** | Use 2 independently operative GPU workers, disjoint complete expert owner graph, distinct sessions/keys and SSH tunnels; run **one 256-row original real-token comparison** at `--source-verify-every 16` and `--window 8`. Run same-data local resident native GPU comparator, then the receipt-based fair throughput/latency/bytes comparison. Save coordinator/worker/tunnel logs. Different endpoints alone do not attest distinct hardware |
| P3 source-level recurrent history, atomic durable receipts and failover | **OPEN** | SBD03 + N02/N07/N12: authentic within-sequence per-token history, monotone source lease, ACKed commit after all peers, independent retry, durable state and restart, stale packet/replica negative controls; conditional finite kernel theorem is donor, not complete source weld |
| P4 true neuron/expert shard capacity and optimal streaming schedule | **OPEN** | TNET02/05/08/11/13/16: source tensor manifest, exact shard split/reconstruction with actual dimension, GPU vs host vs SSD placement, worker capacity, prefetch, multihop queues, measured critical path |
| P5 trained block-diffusion branch vs streamed AR and model quality | **OPEN** | SBD04/05/06: actual corruption/mask objective, native GPU trained denoiser, real multi-step block refinement/marked history and convergence assumptions, matched task quality versus AR/dense. Fix C2 strict student-only heldout 11.565138 instead of relabeling gated hybrid 2.515797 |
| P6 full source↔Agda↔GPU↔peer BIDI and release | **OPEN** | F02 + TNET16: original model entire generation and checkpoint semantics, authenticated physical worker history and causal observer, hardware and quality/energy Pareto; no conclusion until joined receipts exist |

**Ledger remains 106 named targets, not 106 unresolved kernel lemmas.** Finite SBD01–04 kernel contracts PASS; the physical/original-model portion of SBD01–04 remains open. SBD05 convergence and SBD06 diffusion-vs-AR Pareto are genuinely OPEN. Original multiworker numeric receipt still unavailable. This tranche is an integrated protocol repair + local baseline + measured physical handoff, not a new model-quality outcome.

**Canonical physical handoff:** `chboishabba/LeechTransformer/docs/NATIVE_MULTIWORKER_FEDERATION_INTEGRATED_20261113.md`, appended accelerated repair and exact local/remote/comparison commands. Use the already-working Schaka native wrapper and actual `$TEACHER/$STUDENT/$CONFIG/$TOKENS` checkpoint paths; **never treat adapter-only `c2_layer1.pt` as a full MoE checkpoint**. Required next artifacts: full host contract log, 256-row local resident `local.json`, 256-row remote two-GPU `remote.json`, matched `comparison.json`, and peer/tunnel logs. If the user has only one usable GPU host, P2 remains gated; do not disguise source-only tests as independent physical federation.

## 2026-11-13 user-directed research pivot — QUALITY / WORKING first; federation parked

**Explicit priority correction:** User requests no further prioritisation of the physical two-host federation experiment at present. Treat already completed local federation evidence as retained infrastructure: Leech PR #4 at `affd660` passed **24/24** local contract tests (user-run; includes socketpair, not two physical GPU hosts). The native RX 580 local baseline on the original 64×64 token capture processed **64 rows in 2.162631646 s (29.593574 rows/s)**, layer 1, 4 of 64 sampled original source parity checks with **0.0** max output and selected-history error, Python Torch allocated peak **259,494,400 bytes** and reserved **274,726,912 bytes**, device RX 580/HIP 7.16.26385. This receipt does **not** show 64 complete teacher-free-generated tokens, or a quality improvement, or physical multiworker throughput. No second worker host is required for the current model-quality phase. User attached `local.json` with exact teacher SHA `581fdc3b4b6d169a03e2b06896e10d454fd4f819b40a2836c1d5b76849e4c674`, student SHA `f26a5d9246bd0e1f89330b4864124835e3df82bb86e4d1da23fdf5fb3c09224c` and token-file SHA `d3d7ba68d4316fccad9ae15b4b96a0b184071833927315d182c9237d72659160`. Those source inputs identify the federation **baseline**, not necessarily the larger original train/dev/heldout learning splits.

**Existing quality negative controls still authoritative:** dense development CE 2.216053; matched C2 gated development CE 2.564707 (dense advantage 0.348654); gated hybrid independent heldout CE 2.515797; strict full C2 student-only heldout CE 11.565138. 45 matched optimizer rows in historical experiment. Quality, teacher-free replacement and memory efficiency have NOT been demonstrated by the successful expert source parity or 29.59 rows/s local throughput.

### Q1 quality-first integrated implementation on existing native Schaka ROCm 10.1

**LeechTransformer PR #4 source:** `scripts/train_native_student_quality_curriculum.py`, `scripts/check_native_quality_contracts.sh`, `tests/test_native_student_quality_curriculum.py`, `tests/test_guarded_original_teacher_identity.py`, `docs/NATIVE_C2_QUALITY_CURRICULUM_20261113.md`. Existing native launcher admits `scripts.train_native_student_quality_curriculum`.

- `build_guarded_hybrid` in `scripts/train_guarded_moe_continuation.py` now restores ALL frozen original teacher `.ffn.` tensors from the actual dense teacher even when the candidate student's dense FFN keys differ, avoiding silent source-reference contamination. The new trainer **checks zero-gate hybrid development CE against the teacher** and fails before fitting if they diverge.
- Train-only development holdback is reproducibly grouped by exact token window, preventing duplicate source windows from appearing across fit and calibration; original independent heldout overlap is rejected. No heldout-derived model selection.
- On default `--stages auto`, source student is scored for **isolated one-layer replacement** on train-derived development rows, then trained through strictly cumulative **1,2,4,8,...,all-layer** active sets in that observed ranking. Explicit strictly expanding layer groups are also allowed. This avoids making an all-layer untrained student the sole starting training path. It's a development-selected model curriculum, not evidence it is superior.
- At each stage, actual original C2 router/odd expert + even channel parameters are trained using native GPU with (a) end-to-end next-token CE on the focused active student rollout, (b) KL to the original dense teacher next-token probability distribution and (c) local FFN MSE teacher target; pretrained shared source weights, source teacher, and other unselected student blocks remain frozen. Epoch selection and rollback use development CE ONLY.
- Independent heldout teacher, focused student and strict all-layer student CE are scored **after all stages**, and the output checkpoint is a guarded candidate with the dense FFNs physically retained. Explicit no-release flag; a quality pass requires all original model layers active and strict student-only CE <= matched dense heldout CE + declared tolerance. This does **not yet** physically export a teacher-stripped standalone checkpoint.
- JSON/JSONL progress receipts bind original teacher/student/token hashes, fit/calibration indices and source split sizes, training stages, epoch dev scores, native training throughput and GPU allocator stats; no change to original decoder/tokenizer or Schaka ROCm.
- `bash scripts/check_native_quality_contracts.sh` runs focused CPU semantic tests under the *existing pinned Schaka torch Python*, including deliberately perturbed student dense FFN negative control and the zero-gate teacher source identity. **Tests are source-written; not yet host-executed by this assistant**. Training itself is source-written, not observed on RX 580 yet.
- The source runbook provides one substantive native GPU experiment using the original real train IDs, original independent heldout, complete student and teacher checkpoints, with a fresh TrueNAS artifact directory. **The 64×64 federation benchmark capture is not a substitute for a useful learning corpus**, and `c2_layer1.pt` is only an adapter, not the full student model.

### Revised active phases, deliverables and exact remaining lemmas

| Phase | State as of 13 Nov 2026 | Deliverable and exact remaining gates |
|---|---|---|
| P0 native GPU / Agda finite / local original model infrastructure | **USER-VERIFIED DONE for bounded scope** | 14/14 finite topology + 12/12 streaming; Agda 2.9 finite modules accepted; native RX 580 26-batch teacher-sourced C2, matched quality negative control, 24/24 local transport tests and 64-row local parity/throughput. None establishes full teacher-free quality. |
| **Q1 source-identical progressive student learning** | **SOURCE IMPLEMENTED; HOST TEST OPEN** | Run one focused quality contract suite and one substantive pinned native-GPU progressive curriculum using real training/independent heldout files. Close teacher FFN source identity + actual dev CE improvement receipts, no heldout selection. Relevant A01–A06, O01–O03, R02, PERF01–04. |
| **Q2 actual standalone student quality and extraction** | **OPEN, highest alpha** | Strict full student-only CE must move substantially toward or below dense matched CE; retain controls for staged layer/architecture, negative controls for low-data overfit; then implement/export genuinely teacher-free checkpoint with model output parity before discussing compression or inference speed. Exact source/candidate `originalDenseFFNZeroGateBidi`, `cumulativeFocusedStudentRolloutSource`, `fullStudentOnlyHeldoutNoTeacher`, `teacherStrippedStudentCheckpointBidi`. New names are specific weld targets mapped onto existing A/O/R gates, not added programme items. |
| **Q3 quantitative learning efficiency** | **OPEN** | Actual multi-seed native GPU CE vs fit rows, optimizer steps, time, VRAM, model memory, FLOP/token and teacher-free inference. Compare identical source training/dev/heldout data to dense control; no 64-row extrapolation. PERF02–08. |
| Q4 trained block diffusion | **OPTIONAL / OPEN** | Only begin with actual denoising model, objective and source semantics; compare against improved AR student at matched resources. SBD04–06; no speed claims derived from ordinary AR checkpoint. |
| F2–F6 remote miner-worker federation, SSD and physical WAN | **PARKED, not failed** | Existing source and formal infrastructure retained. Multi-host native run, durable signed history and topology optimisation remain OPEN but are no longer a condition on Q1/Q2 student training. N/TNET/GPN and F02 remain as roadmap targets. |

**Original target ledger remains 106 named obligations**. This update changes *priority and weld status*, not proof counts: finite SBD01–04 accepted, physical/source welds open, strict teacher-free quality open, model memory/throughput Pareto open. No new diffusion or GAN architecture victory or student-quality gain is claimed.

**Next maximum cut:** genuine data + full checkpoint → quality-only contracts → native progressive selected student end-to-end training on RX580 → development-ordered quality curve → final heldout teacher vs student-only CE → if successful, source-preserving teacher stripping and isolated student inference performance. Work on physical 2-host federation should not displace this until explicitly reprioritised by user.

## 2026-11-14 measured Q1 curriculum result — major student improvement, quality promotion still fails

**User-run physical GPU result:** the real RX 580 native Schaka 10.1 quality curriculum completed in **80.1 minutes (4,806 seconds)**, with checkpoint and receipts stored at `/mnt/truenas/comet-net/experiments/lila_quality_curriculum_20261113/`. Same experiment's independently held-out dense teacher cross-entropy **2.5834 nats/token**, strict all-student C2 CE **4.7630 nats/token**; gap **+2.1796 nats/token**, therefore quality promotion correctly **FAILED**. Earlier reported strict-student CE **11.565138** to new **4.7630** represents a **6.802138-nat** or **58.8% numerical CE reduction**; historical and new values should not be presented as strictly matched unless the heldout dataset and checkpoint protocol are verified. This proves the curriculum works as a physical native-GPU training programme, *not* that the teacher-free quality gate is closed.

**Source status:** LeechTransformer PR #4 head `bffa5f89005d1654ab3aeeb01d0dfef1c000818c` includes corrected CPU-colocated original teacher/student `build_guarded_hybrid` before CUDA migration. C2 curriculum implementation source complete; user physical run establishes 80.1-minute executed training. New `scripts/audit_native_c2_quality_stages.py` parses the produced `candidate.json` to rank actual cumulative-stage development-CE regressions and weak isolated layers, preserving source checkpoint/heldout SHA, best epoch, and train/development group sizes. This audit is **source-written, not yet run against the user's actual TrueNAS receipt**. It does not invent stage-specific failure causes.

**High-alpha quality cut before any more full 80-minute reruns:**
1. Read the actual `candidate.json` stage trajectory (not just its final score) and source checkpoint hashes; inspect stage 1→2→4→8→12 etc, best-vs-last epoch, initial single-layer development scan, and whether severe CE damage concentrates at a particular cumulative insertion.
2. Use the trained **full candidate checkpoint** as the next actual student initialization. Audit original trained model and preserved teacher/head/attention identity before editing optimizer. Avoid a new random MoE initialization and repeated broad source teacher prefill unless testing a control.
3. Choose a focused continued training cut from the observed dev degradation with **heldout untouched during hyperparameter selection**: repeated train/dev CE, student next-token KL, local teacher-FFN MSE, routing entropy, history amplification and layer-specific activation errors. If a low-data or cross-entropy collapse dominates, compare bounded controlled remedies (e.g. more fit rows, changed KL/MSE ratio, one incremental group at a time) before expanding to all layers.
4. The next promotion cut is strict full-student heldout CE <= matched teacher heldout CE + predeclared budget, plus a **physically teacher-stripped** checkpoint and exact source output parity. The guarded candidate checkpoint still physically contains dense teacher FFNs, even when its student-only forward branch avoids their execution.
5. Measure full teacher-free inference memory, completed tokens/s and student model bytes, on the same original checkpoint/token task; only then compare resource/quality Pareto. Do not reuse the local federation 29.59 selected-row/s as complete student token generation throughput.

**Phase update (no new artificial lemma tally):** P0 bounded original source proof/runtime and physical training accepted; Q1 progressive student training **PHYSICAL EXECUTION COMPLETE, partial quality success, promotion FAIL**; Q2 structural quality diagnosis, targeted continuation, true standalone student export **OPEN / top priority**; Q3 resource and multi-seed evaluation OPEN; diffusion Q4 deferred; remote federation F2–F6 explicitly parked. The roadmap continues to track **106 named obligations**. Exact unresolved quality welds: `fullStudentOnlyHeldoutNoTeacher`, `teacherStrippedStudentCheckpointBidi`, `cumulativeFocusedStudentRolloutSource` for actual full model, `originalDenseFFNZeroGateBidi` physical receipt/trace as needed, PERF02–08 fair quality/cost measurements. No new theorem falsely marked proved.

**Receipt-only analysis command (no GPU repeat):**
```bash
cd /path/to/LeechTransformer
git fetch origin && git switch experiment/consumer-preserving-multiscale-codec-20261031 && git pull --ff-only
python3 scripts/audit_native_c2_quality_stages.py \
  --receipt /mnt/truenas/comet-net/experiments/lila_quality_curriculum_20261113/candidate.json \
  --output /mnt/truenas/comet-net/experiments/lila_quality_curriculum_20261113/stage_audit.json
```
Do not infer particular failing layers until that analysis has actually consumed the stage records. Data from prior 64-row federation receipt is a separate benchmark and must not replace this training audit.

## 2026-11-14 full-formalism reconciliation: observed 80.1-minute backprop versus forward-only Dust/Noise/LILA

**New priority after the real GPU result.** The Q1 experiment is not the original proposed *forward-only* learner: it is a genuine **AdamW + reverse-mode `loss.backward()`** curriculum with teacher-forward, hybrid-forward (local FFN MSE), focused student-forward, reverse-mode and development scoring. 80.1 minutes = 4,806 seconds is the user-observed **whole-run** runtime on native RX 580; it cannot be equated to 4,806 seconds of backward passes, to a forward pass time, or to the runtime of future Dust. Note: the existing stage `TrainingProgress.summary()` includes inter-epoch development scoring/calibration; time before/after stage meter can include teacher loading, initial teacher/dev baseline, isolated layer scan, independent heldout, checkpoint serialization and logging. A fully partitioned wall-clock receipt remains OPEN.

**Source-backed pre-existing forward-only programme (do not duplicate its maths):**
- DASHI Agda PR [#1265](https://github.com/chboishabba/dashi_agda/pull/1265), branch `research/dust-noise-sophontic-maxcut-20261026`: `DASHI/Reasoning/DustNoiseAlgorithmExact.agda` (future reward Eq.1, activation credit Eq.2, outer product Eq.3, attention Eq.4); `LILAForwardOnlyDustAdapterExact.agda` consumes canonical `ObserverRefinementLatticeExact`, objective, paired interventions, loss-at-probe and a `ForwardOnlyTrace`. This adapter supplies typed interfaces and equality by assumption, *not* a full-proved numerical learning theorem or physical native GPU LILA.
- `Docs/formal/DustFiniteKCenteredExpectationDerivation20261026.md`: for iid zero-mean unit-covariance affine activation perturbations `a_i` and finite `K`, the centered credit is **sample-covariance times local gradient**, hence expectation `(K-1)/K*g`; exactly antithetic `(+1,-1)` has covariance 1 while two identical probes cancel. Finite rational Rademacher tests K=1..8 passed but general probability/Gaussian/kernel proof remained open. Crucial: actual Dust implementation's direct one-draw branch uses clean-reference reward; the within-population centering formula is not unconditionally the literal `nrep=1` path. See `DustPaperNativeAttributionAndRemainingProofs20261026.md`.
- `scripts/lila_dust_forward_exact_20261026.py` **executed** a 4-token finite LILA-style local semantic/nuisance toy: activation credit direction `(-1,0)`, weights `(0,0)→(1/8,0)`, toy loss `1/2→49/128`, synthetic shifted nuisance loss the same, 16 population noise draws per 4-token batch. This is a constructive exact *forward-only* learning witness, not trained Leech C2 or a realistic generalisation benchmark.
- `scripts/sovereign_lila_dust_projection_step.py` implements a **restricted real source target** `E8GPT.core.layers[-1].from_e8.weight` using `K` activation-perturbed forwards, population-centred per-token reward, optional future-credit decay, and outer-product parameter update. Its source-compatible CPU *analogue* with 8 probes and 10 total forward calls improved one-batch CE **2.3726654→2.3514826**, without backward; original E8GPT model/checkpoint execution remained unmeasured. This is in the **Sovereign-LILA-E8** lane, NOT automatically the same parameter/type as LeechTransformer C2 FFNs.
- [#1463](https://github.com/chboishabba/dashi_agda/pull/1463), `Docs/WeightSpaceProgrammingLilaE8Reuse20261103.md` separates source E8 root soft quantisation, orthogonal Q/K/rank-one attention bias, trainable readout/projection, WSP sparse patch, and Dust perturbative training. Projection edit success/abstract equivariance does not prove general teacher-free generative quality.
- `DASHI/Learning/GrokkingOperatorContract.agda`, `Docs/learning/GrokkingOperatorFormalism.md`, and prior learner/temporal trajectories concern specified loss/update/evidence and invariant-selection, not guaranteed low-loss initialisation or a closed-form solution to nonlinear AdamW training.
- External Dust authors **Samip Dahal, Bishwas Mandal, Serdar Gülbahar, Akshay Vegesna** own the algorithm and published performance; Q Labs October 2026 paper [Dust](https://qlabs.sh/research/dust/) specifically reports that activation-space virtual population enables many per-token candidates within a forward, while its current pretraining method is **not established as more compute-efficient than backprop**. It separates layer-type/head/attention estimators, head cached-logit sampling, and scalar residual ES. Do not replace those with generic weight-space SPSA and claim literal Dust or matched runtime.

### Source-accurate mathematical account of the 4.763 result

Teacher and strict C2 student CE on matched heldout evaluation are
`H_T=2.5834`, `H_S=4.7630`, so `ΔH=H_S-H_T=2.1796` nats/token and student/teacher perplexity ratio `exp(ΔH)≈8.8427684`. Student perplexity `exp(4.763)≈117.09669`; teacher `exp(2.5834)≈13.24208`. Earlier strict student CE 11.565138 to 4.763 gives a **6.802138-nat numerical improvement** (~58.8% reduction); if the earlier and new heldout sets are the same, `(11.565138-4.763)/(11.565138-2.5834)≈0.75733` of the previous teacher gap was closed. Without source-matched heldout hashes, this last comparison is descriptive, not a verified same-data causal result.

The CE is exactly `H(q)=-(1/N) Σ_t log q(y_t|x_{≤t})`; cannot independently reconstruct the observed CE from the Agda group action, finite signed history law, architecture dimensions, loss definition or wall-clock time alone. Exact reproducibility requires original heldout token IDs, **trained checkpoint weights**, model forward semantics and per-token logits or log probabilities. Their SHA, full score and logit-digest form a deterministic executable numerical certificate within a pinned GPU backend (floating-point tolerance stated). Any analytic local FFN error bound requires actual residual traces and downstream Lipschitz constants; a geometry-only theorem does not determine the trained weights.

For source C2 `F(-x,-H)=-F(x,H)` with symmetric routing, the architecture restricts odd expert updates; the even correction channel mitigates representational exclusion but can introduce extra trainable degrees of freedom and does not ensure teacher parity. The remaining student CE gap can result from multi-layer activation drift, history amplification/route changes, capacity, optimisation, dataset or other causes, not identifiable from one scalar CE. The source-controlled curriculum's 1,2,4,... stages are the correct initial diagnostic surface; inspect each best development CE, source FFN MSE, routing entropy and sign/history growth.

A per-layer *conditional* perturbation bound (not an observed result): if `e_{l+1}≤L_l e_l+δ_l` for compatible states and local error δ_l, then `e_L≤Σ_l δ_l ∏_{j>l} L_j`; for logits error infinity-norm ≤ε on identical targets, next-token CE difference ≤2ε. Prove actual model-specific Lipschitz/route stability and measure δ_l before using as a predictive theorem. Unstable top-k near ties defeats a naive global smooth bound.

### What forward-only can and cannot save

`T_backprop≈Σ_steps(teacher_forward+hybrid_forward+student_forward+student_backward+update)+development+I/O`. Current script does two student-containing forwards (for local MSE and focused rollout) plus an independent teacher forward **per optimizer batch**, not just one forward/backward. `T_Dust≈Σ_updates(K×recomputed_suffix_forward + teacher_target_or_cached_logits + reward/outer_update)+validation+I/O`. Dust's virtual-token population, cached prefixes and head slices may reduce practical probe cost, but no original-token training speedup follows from removing reverse-mode. Compare measured **loss decrease per second/joule**, stable final heldout CE, VRAM/RAM and source-identity receipts at equal token budgets. The 80.1min run is a baseline for the exact implemented curriculum only, not a justified cost forecast for another objective, checkpoint or accelerator.

A minimal exact forward-only estimator for scalar affine local loss with K iid Gaussian/Rademacher draws is `g_hat=[(1/K)Σ a_i a_i^T - abar abar^T]g`, hence expectation `(1-1/K)g` under the stated moments. Rescaling `K/(K−1)` corrects affine iid expectation for K>1, but is not literal source Dust and gives no nonlinear convergence guarantee. With scalar two-probe antithetic ±1, sample covariance 1 exactly; a balanced deterministic design can sharply lower bias in this toy case. Compare probe variance, credit interference, convergence and actual device time with the backprop anchor rather than selecting by pure estimator cosine.

### Larger Q2 maximum-cut research plan (no new obligations invented)

1. **P0 cost/quality evidence ingest, CPU only:** collect original `candidate.json`, stage logs/JSONLs and checkpoint SHA from TrueNAS. Use `scripts/audit_native_c2_quality_stages.py` for stage bottleneck and new `scripts/audit_c2_forward_only_cost.py` to decompose reported per-stage seconds/steps against the **4,806s observed whole wall**. Cost analyzer refuses to infer backward share or forward-only speedup without real forward/backward microbench numbers. It and `tests/test_audit_c2_forward_only_cost.py` are source-written, no user-host pass yet.
2. **P1 original-model causal loss/representation attribution:** run on the **existing 4.763 checkpoint**, no training: per-layer isolated replacement and cumulative replacement, actual source FFN residual norms, history amplification, top-k route margins/ties, heldout tokenwise CE errors, and symmetric C2/even channel tests. Measure source error propagation vs the conditional bound; identify the worst layer/subspace/transition before expensive training.
3. **P2 restore forward-only owner on real C2 weights:** port *actual Dust activation-credit/outer-product* only to an exposed expert FFN output projection or even-channel readout first, using teacher-input caches and a small **training-derived calibration split**. Freeze the remaining parameters and compare **same checkpoint, examples, forward token budget, dev CE and measured time** with AdamW, plain two-sided random-direction, and signed/orthogonal/antithetic probes. Do not confuse original E8GPT last projection with Leech C2 `HistoryOrbitMoE.experts[e][2]`, or claim the whole network is forward-only from a single readout. Explicitly calculate tokenwise future-reward scope when advancing to history transitions.
4. **P3 generalise only if it pays:** if local forward-only probe actually improves CE per wall time (and device memory) at matched quality, extend to selected history transitions/orientation, then all layers. Otherwise reuse the strong AdamW curriculum and adjust training/capacity/data rather than incurring K costly full-model forwards.
5. **P4 promote:** full standalone teacher-stripped checkpoint and exact numerical source BIDI on the actual model, independent heldout CE vs dense, end-to-end inference RAM/VRAM/latency/tokens/s, multi-seed controls. Never allow heldout for optimizer hyperparameter selection.

**Exact unresolved formal welds mapped to existing ledger:** `actualLeechC2DustActivationCreditSource` (literal output-projection trace and reward); `measuredForwardOnlyVsAdamWMatchedCost`; `nonlinearC2ProbeBiasVarianceOrDescent`; `recurrentHistoryFutureRewardCredit`; `tokenwiseC2SourceLogitReconstruction`; `conditionalLayerErrorPropagationOriginalModel`; `teacherStrippedStudentCheckpointBidi`. Dust-specific finite affine/antithetic results are existing donors, not new proofs; nonlinear/source and GPU cost remain genuinely open. Maintain **106** named programme gates, no new artificial gate count.

**Critical interpretation:** the 4.763 student is evidence for **trainability under the current backprop curriculum**, but neither proves backprop indispensable nor proves that a forward-only learner could have reached 4.763 in less than 80.1min. The direct discriminator is original-weight matched forward-only credit on targeted C2 modules, with a measured budget and quality, not a theorem extrapolated from the clock time.

## 2026-11-14 Q2.1–Q3 integrated implementation delivery (original Leech C2)

**User directive:** complete Q2.1 source observation reproduction, Q2.2 actual layer error localisation, Q2.3 forward-only C2 Dust learning, Q2.4 fair AdamW/Dust/SPSA competition, Q2.5 full learner and Q3 actual teacher removal. This tranche makes all corresponding *source consumers and executable host gates* available on Leech PR #4. The current runtime **cannot access the real TrueNAS `candidate.pt` and `candidate.json`**, so all new original-checkpoint source verification and physical quality/promotion results are still OPEN; no invented CE trajectory, forward-only speedup, native-device acceptance or new Agda kernel receipt.

**Original Leech implementation:** `chboishabba/LeechTransformer` PR #4, `docs/C2_QUALITY_FULL_MAXCUT_Q21_Q3_20261114.md`. Source files:
- `scripts/reproduce_c2_quality_and_layers.py`: original teacher/student checkpoint strict loading and SHA checks from the observed quality receipt; independent heldout target-token FP64 logprob digest and repeated CE; original train-derived dev isolated/cumulative student substitutions; teacher-forced C2 odd/even/reference FFN error, routing entropy, top-k margins and history norm. Source/weld diagnostic; model-specific propagation theorem still OPEN.
- `scripts/compare_c2_forward_only_optimizer.py`: original trained C2 `even_student[-1]` output projection is an actual source `nn.Linear`, not Sovereign E8GPT; restricted Dust mean-centred activation perturbation/future-credit outer product without backward; independent and antithetic probes; plain central SPSA; and matched AdamW readout-only control. All four arms reset the exact same source candidate, fit data and batch sequence. Output reports real dev CE, wall time, forward-call and target-token counts and VRAM allocator; same number of optimizer steps is **not** equal compute. No special caching or full source Dust attention/head training claimed.
- `scripts/export_c2_teacher_free.py`: enforce original source `quality_curriculum_receipt` stored within `candidate.pt`, original independent heldout hash/teacher CE (never user-supplied target); remove **physical** `.ffn.` and `.quality_gate` tensors; reconstruct independent `moe_guarded_ffn=False` source `LeechGPT` with odd/even students, strict state-load, compare original student-only logits and CE, quantify state-byte reduction. Export is allowed as explicitly **unpromoted**, `release_admitted=false`, even if numerical parity holds. Any missing channel or mismatch must fail closed.
- `scripts/benchmark_c2_teacher_free.py`: genuine native single-token autoregressive KV+expert-history greedy decode and source prefill separately for original guarded-vs-pure student, one GPU-resident model at a time; reports allocated/peak VRAM, exact generated token identity, prefill target-tok/s versus greedy generated-token/s. Physical speed/quality Pareto remains open.
- `tests/test_c2_quality_maxcut.py` plus `scripts/check_c2_quality_maxcut.sh`: finite CPU source-semantic checks under the existing Schaka torch Python; may be run before any GPU experiment. Other original curriculum/teacher identity/cost tests reused. **Tests have not yet been run on the user's host.**
- Existing `scripts/train_native_student_quality_curriculum.py` is usable as **warm-start Q2.5**: `--student` may refer to actual full trained `candidate.pt`, with explicit cumulative stages instead of random model restarts. Requires new real fit/development/independent heldout receipts; no new arbitrary claim of 4.763 improvement.

**Evidence and exact phase labels:**
| Phase | Source implementation | Acceptance still missing |
|---|---|---|
| Q2.1 tokenwise original score + 80.1min wall attribution | SOURCE-COMMITTED: original checkpoint hashes, target logprob digest, independent heldout CE, stage cost auditors | Actual TrueNAS stage receipts and observed replay; backward fraction cannot be inferred from 4,806s |
| Q2.2 layerwise causal diagnosis | SOURCE-COMMITTED: original isolated/cumulative, odd/even, teacher FFN, source top-k margins and history | GPU measurement, source-specific route stability and downstream Lipschitz/error theorem; diagnostics are not automatic causal explanation |
| Q2.3 actual C2 Dust | SOURCE-COMMITTED: true C2 even output projection, K forward-only noise probes, future-credit/outer update | Native GPU original model run; exact nonlinear estimator/attention/history credit proof; actual dev loss improvement |
| Q2.4 genuine optimizer/resource Pareto | SOURCE-COMMITTED: matched four-way initial weights/fit batches, measured forward/backward budgets | Repeated seeds, real quality per elapsed/forward token and energy, matched final validation |
| Q2.5 full learner continuation | EXISTING IMPLEMENTED native full student AdamW; source new forward-only readout is a local donor | Actual full-student quality >= teacher, multi-layer forward-only/future history if selected, original full-model source weld |
| Q3 teacher-free student | SOURCE-COMMITTED: physical stripping, independent strict load, exact logits/CE and true KV/history generation comparator | Host BIDI and physical memory/greedy decoding receipt, quality promotion, repeatability and standalone runtime readiness |

**Pre-existing formal owners:** DASHI #1265 for `DustNoiseAlgorithmExact`, `DustTwoProbeCenteringExact`, `DustFinitePopulationCovarianceExact`, `LILAForwardOnlyDustAdapterExact` and restricted original Sovereign E8GPT. Their kernel status is not silently promoted. DASHI #1094/#1095 geometric/semantic owners and pre-existing C2 signed-history transport are donors, not replacements for measured original-model source equivalence. **106 programme targets remain**; mapped exact outstanding weld names from the previous section remain unchanged. No new mathematically unsupported claim that forward-only always beats backprop.

**Default execution order:** 1) `bash scripts/check_c2_quality_maxcut.sh`; 2) existing stage and wall cost audits (CPU); 3) `reproduce_c2_quality_and_layers.py` on real trained source checkpoint; 4) select **one layer from train-derived dev**; 5) four-way native optimizer experiment from same checkpoint, compare loss per time/forward token; 6) independent pure student export/BIDI and true generator prefill/single-token generation benchmark; 7) continue full student only if measurements demonstrate a sensible path to teacher CE. All commands and guardrails in Leech `docs/C2_QUALITY_FULL_MAXCUT_Q21_Q3_20261114.md`. Federation and diffusion remain parked.

### Final Q3 source hardening (same 14 Nov implementation cut)

The independent standalone C2 runtime comparison now requires the `teacher_stripped_bidi_receipt` embedded in the exported pure checkpoint to match the **exact SHA-256 of the guarded source candidate and original token array**. It computes per-autoregressive-step float32 **complete vocabulary logit digests and full per-layer expert-history digests**, in addition to greedy decoded token identities and source heldout CE. `test_guarded_and_pure_cached_generation_history_bidi` covers the source semantics on a constructed two-layer CPU C2 model. The machine-evidence boundary remains **SOURCE-WRITTEN; user's native host tests not yet executed**, and no verified independent physical GPU BIDI or quality improvement is claimed. Canonical Leech PR #4 latest doc `docs/C2_QUALITY_FULL_MAXCUT_Q21_Q3_20261114.md`.

## 2026-11-14 physical RX580 Q2.1–Q3 results and evidence reconciliation

**User-reported TrueNAS host run from `/home/c/Documents/code/DASHIg/LeechTransformer`:** all artifacts in `/mnt/truenas/comet-net/experiments/lila_quality_curriculum_20261113/` (absolute paths are on user host, not mounted in GitHub tooling). No direct re-open of JSON or execution on this host was possible from this connector session. These are **user-reported receipts**, not independently fetched new GPU results. Physical device RX 580, HIP 7.16.26385.

**Q2.1 cost+reproduction ACCEPTED as user host evidence:**
- Original 80.1-minute total = **4806.0 s**, five stage loop summaries total **4685.3 s**, 825 optimizer steps. Difference **120.7 s** outside those stage loops (initialisation/selection/final evaluation/logging/serialisation and measurement scope). Whole-run average **5.82545 s/optimizer step**, stage-loop average **5.67915 s/step**. These are aggregate *not* per-backward or per-forward timings; stage loops include interepoch development evaluation. No joules measurement.
- Original independent heldout teacher CE **2.58340826**, source receipt **2.58340818** (absolute discrepancy ~7.9e−8); student CE **4.76298302** versus **4.76298299** (~3.3e−8); numerical source reproduction true.
- Best development CE by cumulative stage: layer 11 **2.2854**; layers 10–11 **2.3453** (+0.0599); layers 8–11 **2.7269** (+0.3815); layers 4–11 **3.3708** (+0.6439); full layers 0–11 **4.7916** (+1.4208). Largest *group insertion* regression is adding layers 0–3, not proof that each individually caused all of the loss.

**Q2.2 original source diagnostics, accepted as observational:**
- On **train-derived development rows**, isolated layer 1 C2 replacement CE **5.2445** (teacher-relative +2.7315), isolated layer 0 **4.6620** (+2.1490), isolated layer 11 **2.4059** (−0.1071). These place first priority on source layers 1 and 0, not on a generic all-layer longer training run.
- Teacher-input local layer 1 relative FFN MSE **127.02**, odd/even cross mean **−0.4916**. Destructive cross-term is observed in that chosen tensor statistic, but causality/sensitivity and exact correction remain to be measured.
- Layer 10 reported final-history RMS **107,049** and mean route boundary margin **4,466**; layer 11 RMS **1.28×10^9** and margin **6.80×10^7**. **Critical scope correction:** `reproduce_c2_quality_and_layers.py` registers `teacher.blocks[layer].ln2`, then calls the source `moe(x)` directly on **teacher-forced local normalized inputs**, with a fresh default MoE history. Thus these values are local teacher-forced source diagnostic outputs, **not a measurement of recursively propagated histories in the student's own autoregressive token rollout**. The latter remains a separate specific physical/causal gate. Large magnitudes are a stability warning; do not describe them as established student recurrent-history explosion yet.

**Q2.3/Q2.4 actual single native even-readout experiment, 8 steps each, identical checkpoint and batches:**
| Arm | Forward/back calls | Wall seconds | Peak PyTorch allocated MB | Final dev CE | Improvement from 4.791580 |
|---|---|---|---|---|---|
| AdamW | 8/8 | 43.19 | 277.5 | 4.774656 | +0.016925 |
| Dust independent K4 | 40/0 | 75.00 | 238.6 | 4.791549 | +0.000031 |
| Dust antithetic 2 pairs | 40/0 | 70.92 | 238.8 | 4.792441 | −0.000861 |
| SPSA K4 | 32/0 | 59.36 | 238.8 | 4.788315 | +0.003265 |

Source-executed forward-only C2 update is now genuine GPU empirical evidence that **backward is not a requirement to change weights**, but this single-layer restricted Dust mechanism did not match AdamW's local CE gain. AdamW improvement/sec ~0.000392, SPSA ~0.000055, independent Dust ~0.00000041; low step count/one layer/single seed, not a general optimizer comparison. Forward-only PyTorch allocator reduction ~38.7–38.9 MB (~14%) but greater wall time than AdamW due to separate full-model probes; no equal-compute or total-joules result. Next optimization is to cache the original upstream even-readout activations and recompute only model suffix, and to test source activation-credit gradient validity against reverse AD on **the same parameter and batch** rather than indiscriminately increasing K or learning rate.

**Q3 physical export / functional BIDI accepted for tested source:**
- `c2_pure_unpromoted.pt` 112.2 MB, SHA256 prefix `703583bc`; removed **56.7 MB**, **33.61%** source tensor bytes in frozen dense FFNs + quality gates; independently strict-loaded pure C2 model has full CE **4.762983** and **zero absolute logit discrepancy** against guarded `student_only=True`.
- One 8-token native KV+history generation reported identical greedy tokens `270,697,2008,1984,230,1999,302,270`, entire per-step float32 vocabulary logits and all expert histories hash-equal. This is a particularly strong **finite-trace** original-source identity certificate, not an all-sequence mathematical equivalence theorem. Quality promotion remains **FAILED** at CE 4.763 versus teacher 2.5834.
- Initial script measured guarded first, stripped second, only 8 generated tokens. Reported one-run guarded **2.82 tokens/s** versus pure **36.43 tokens/s** (apparent **12.92×**). PyTorch peak allocated **204.8 MB → 147.5 MB**. **Important attribution limitation:** original source guarded `student_only=True` already bypasses the teacher FFN forward (see `LeechBlock.forward`), so it is **not scientifically justified** to attribute a 12.9× compute speedup to eliminating dynamically executed teacher FFNs. It may reflect first-run kernel compilation/cold caching, sequential order, different resident memory/branch checks or hardware warmup. The one-run measured throughput ratio is valid as a receipt, not a causal sustained speedup.

**New native ABBA confound discriminator:** Leech PR #4 `scripts/benchmark_c2_teacher_free_abba.py`, integrated into the working `scripts/run_native_schaka101_lila.sh`. It separately warms guarded and stripped models and then alternates `guarded,pure,pure,guarded` / `pure,guarded,guarded,pure` for at least 2 cycles; hashes complete per-step logits/histories, tests source SHA and reports median/min/max genuine generated tok/s. Both models remain GPU-resident in this measurement; allocator peaks therefore **cannot be interpreted as independent model residency**, and energy/clock/thermal controls remain unmeasured. This is source-written only; no second GPU timing receipt yet.

### Revised phase gate status after host results
| Phase | Current status | Exact remaining max-cut |
|---|---|---|
| Q2.1 observations and aggregate timing | **PHYSICAL PASS** | Per-component timers and per-forward/per-backward wall cost still OPEN |
| Q2.2 source localisation | **DIAGNOSTIC PASS**, causal model open | Fix/compare layers 0 and 1, test actual recurrent student-history growth, routing sensitivity and 1.28e9 local teacher-forced history vs actual autoregressive growth |
| Q2.3 forward-only actual C2 learner | **NATIVE PASS for restricted one-readout no-backward update**, performance open | Verify source credit vs autograd and cached suffix, avoid treating 0.000031 CE as competitive |
| Q2.4 matched optimizer controls | **8-step physical first comparison PASS**, competitive equivalence OPEN | Matched forward token/time/energy budgets, several seeds, controlled hyperparameter tuning on development only |
| Q2.5 full teacher-free learner quality | **STILL FAILED** | Strict full student-only CE 4.762983 > teacher 2.583408, prioritize early-layer FFN approximation and stability before another 80min training |
| Q3 independently loadable teacher-stripped model | **PHYSICAL FINITE-TRACE BIDI + 33.61% tensor-byte reduction PASS**, deployment quality open | Warmed ABBA timing; actual model-only resident VRAM and stable long-context prefill/decode; source all-input equivalence theorem and competitive CE |

**Next work priority:** use the existing measured original checkpoint to (1) distinguish local teacher-forced history explosion from full student recurrence, (2) test early-layer 0/1 approximation and odd-even cancellation, (3) improve Dust efficient probes by caching prefix and measuring gradient credit, (4) benchmark ABBA warm inference before asserting performance gain. Physical multi-host federation remains parked; Q2.5 quality is dominant. No new named gate count; canonical programme still has 106 planning targets.

---

## 2026-11-14 integrated D4/B4–C3–E8–Leech–theta/zeta–Sophontic–LILA maximum cut

**Scope and date:** this reconciles the user's November 14 request with the canonical 106-obligation programme, not an extra 106 claims or a replacement roadmap. This subsection is an *audit and exact delivery plan*, **not** a new Agda kernel run, a proof of RH, a physical Leech/E8 isometry of trained weights, or evidence that changing a C2 router to C3 improves CE. Do not promote an equality of multiplicities to an equality of representations.

### 0. Accepted observations and next actual machine cut

The RX 580/HIP 7.16 original student and teacher were independently re-evaluated on the heldout inputs: student **4.76298302 CE**, teacher **2.58340826 CE**, numerically reproducing the saved curriculum receipts within ~1e−7 nats. Five-stage curriculum has 825 optimiser steps, measured total **4806.0 s**, stage-loop sum **4685.3 s**; this does not measure a per-backward cost. Standalone `c2_pure_unpromoted.pt` physically removes **56.7 MB** of dense fallback state (**33.61% tensor-byte reduction**) and preserves the observed 8-step full logits + expert-history fingerprints with exact output parity. It remains **not quality promoted**. Initial reported **12.9×** pure/guarded throughput ratio came from one unbalanced short run; warmed ABBA verification is still OPEN and guarded `student_only=True` already bypasses dense FFN compute. The native 8-step one-readout forward-only competitor improves dev CE ~0.000031 for independent Dust versus ~0.016925 for AdamW, with lower PyTorch peak allocated memory but greater elapsed time; no general forward-only superiority follows.

Train-derived development diagnoses: worst isolated replacements layers 1 and 0 (CE **5.2445 / 4.6620**); final source full-student stage best CE **4.7916**. Reported large layer-10/11 histories are *teacher-forced local MoE* diagnostics, not yet full recurrent student-runaway evidence. **Quality source maximum-cut remains layer-0/1 correction plus full-student rollout, not broad federation or another generic 80-minute training run.**

### 1. Already owned mathematics (do not repeat these donors)

| Carrier and role | Exact owner/source | Status of that owner's claim |
|---|---|---|
| Antipodal C2, three-phase C3, Fourier inverse/conjugation | `DASHI/Moonshine/C3FourierConjugationExact.agda`, `DASHI/Core/FiniteC3OrbitStabilizerExact.agda`, Leech `models/trialectic_wave_prior.py` | Finite algebra and neural source transformations; not trained model equivariance |
| Distinct dihedral D4, D4-root, B4-root and signed Weyl carrier | `DASHI/Foundations/TrialecticD4C3ResidualBoundaryExact.agda`, `DASHI/Physics/RootSystemB4Carrier.agda`, `RootSystemB4WeylAction.agda` | Finite carriers and naming safeguards, **not** complete D4 diagram triality/S3 on same F4 root carrier |
| C6 observer, two distinct involutions and coarse C3 phase | `DASHI/Moonshine/JInvariant369C6TenRankWeightTwelveCrossPollinationExact.agda` | Finite observer commuting/invariant claims; same C6 action as source LILA not proven |
| Finite C3 Monster phase and 3-local E8/Leech counts | `DASHI/Moonshine/Monster3BCyclicFourierDyadicBridgeExact.agda`, `MonsterThreeLocalE8LeechBridgeExact.agda`, `Monster3BHighestAlphaValidation.agda` | Exact character **multiplicity and arithmetic** identities, not orbital lattice-coordinate intertwiners |
| E8 rank/240 and Leech rank/196560 | `DASHI/Biology/ExceptionalLatticeGrokkingProtocolExact.agda` | Benchmark and explicit null-model protocol; not trained weights proven lattice-isometric |
| Eisenstein/Delta modular action | `DASHI/Physics/Closure/TriadicEisensteinTransformationTheorem.agda`, `DASHI/Moonshine/EisensteinDiscriminantWeight12Exact.agda`, `DeltaNormalizedWeight12SameObjectExact.agda` | All-SL2Z weight-12 **conditional analytic model** transformation and pinned Lean same-object eta24/Delta fact recorded; transfer and same-carrier source admission still required |
| E8 theta→J original source | `DASHI/Physics/Closure/LilaE8ThetaJBridgeSurface.agda` | **Explicit non-promoting request** for Theta(E8)=E4, E4^3/Delta−744, q normalisation; do not call complete |
| Riemann-zeta reflection / C3 orbit | `DASHI/Analysis/RiemannReflectionC3OrbitShapeBridgeExact.agda`, `RiemannMaassMoonshineCrossPollinationExact.agda` | Fixed-versus-inverse-pair **orbit-shape only**; not RH/Weil positivity/zero spectrum |
| Sophontic semantic paired interventions, forward-only Dust | `DASHI/Reasoning/LILAForwardOnlyDustAdapterExact.agda` (PR #1265), `ObserverRefinementLatticeExact`; canonical roadmap prior Sophontic section | Typed intervention/observer interface, some finite Dust evidence; real full-model semantic invariance, temporal learning, and deployment source weld OPEN |

**Critical three-zeta distinction:** `ζ₃` / `ζ₃²` are nontrivial C3 characters; `ζ(s)` is the Riemann zeta function; `Z_Λ(s)` is a lattice Epstein zeta function. In the Monster 3B module, `zeta`/`zetaSquared` also *name multiplicity fields* for characters, not values of the Riemann zeta function. The identity `240·3·(1+16+16²)=196560` is exact **count arithmetic**. It can be arranged in 3 cyclic sectors, but doing that is not an actual C3-equivariant partition of 196560 Leech vectors unless an explicit group action and bijection are supplied.

### 2. Classical same-object target identities, definitions, and exact gates

Use a chosen norm-two E8 lattice, an even unimodular rank-24 rootless Leech lattice, and a single q-convention `q = exp(2πiτ)`, `Θ_L(τ)=Σ_{v∈L}q^{(v,v)/2}`. Select the exact compatible E4/E6/Δ/J analytic carriers and their pinned proof authorities. **For Leech define J=j−744; j=E4³/Δ.** Intended classical identities:

```math
\Theta_{E_8}=E_4=1+240\sum_{n\ge1}\sigma_3(n)q^n,
\quad
\Theta_{\Lambda_{24}}=E_4^3-720\Delta
=\Delta(J+24).
```

For `Re(s)>4` under that norm choice, `Z_E8(s)=Σ_{v≠0}(v,v)^{-s}=240·2^{-s}ζ(s)ζ(s−3)`. The proof uses norm-2n shell multiplicities 240 σ3(n) and **absolute convergence** to exchange the Dirichlet sums. Its completed form and Mellin transform require own domains, Gamma/scaling and analytic-continuation proofs. Do not silently replace it by the Riemann explicit formula, claim that RH follows, or deduce neural CE from an arithmetic generating function.

The Leech theta identity is a modular-form **weight-12** identity; the expression `Δ(J+24)` is *holomorphic* even though `J` has a pole at the cusp. Need the same lattice and modular-form coefficients, correct q constant and q first-shell coefficient, not just 196560 equality. The source `LilaE8ThetaJBridgeSurface` is a TODO owner, not an established same-carrier theorem. Prior Lean eta24/Δ does **not** in itself pay for either lattice theta identification.

### 3. Exact unpaid lemmas, A/B/C split and source/acceptance conditions

| Gate | Named exact target (lemma or physical weld) | Source prerequisite; acceptance definition | State |
|---|---|---|---|
| M1a | `d4B4EvenSignedWeylInclusion` | On same `Vec ℤ⁴` carrier, D4 even-signed subgroup closed under B4 composition, root-preserving and injectively embedded, with checkable index-two cosets | OPEN — existing B4 signed action donor |
| M1b | `d4TrialityS3Action` | Exact norm-preserving order-3 outer D4 diagram automorphism, order-2 reflection, `srs=r⁻¹` and genuine faithful S3 action, not arbitrary C3 action | OPEN |
| M1c | `f4D4OuterTrialityQuotient` | Same F4/D4 root object, Weyl inclusion and explicit six-coset quotient with correct permutation action | OPEN |
| M2a | `e8RootCarrierNormInnerProduct240Bidi` | Original E8 coordinates, full 240 distinct norm-2 roots, membership/Gram and Weyl closure; reuse any authoritative source carrier already present | OPEN in inspected LILA-R2 surface; check other PR branches before reimplementing |
| M2b | `d4TrialityToE8LeechAction` | Actual injective/gluing coordinate map with norm/inner-product preservation and commuting D4/S3 action on **actual** E8 and Leech carriers | OPEN |
| M2c | `leechMinimalShell196560SameCarrier` | Explicit bijection onto all norm-4 Leech vectors and exact 196560 cardinality; source `240·3·819` only counting donor | OPEN |
| M3a | `thetaE8EqualsE4SameCarrier` | Original norm-2n shell counts for all n, or modularity + rank/constant/coefficient uniqueness on the same E8 lattice and q-carrier | OPEN |
| M3b | `thetaLeechEqualsDeltaTimesJPlus24` | Original Leech theta modularity, absence of norm-2 vectors and first nonzero shell, weight-12 uniqueness, *same* E4/Δ/J convention | OPEN |
| M3c | `e8EpsteinZetaMellinFactorization` | Absolute convergence for Re(s)>4, Dirichlet coefficient grouping, zeta-product equality and Mellin normalisation, source carrier identical to M3a | OPEN |
| M3d | `e8LeechDeltaSameObjectLeanAgdaWeld` | Reuse existing weight-12/Eisenstein and pinned Lean eta24=Δ proof with exact normalisation and checked cross-language digest/statement; no replacement postulate | OPEN |
| M4a | `c3PhaseVsRiemannZetaTypeSeparation` | Explicitly preserve cyclotomic, Epstein, Riemann and Monster multiplicity types, carry existing orbit-shape no-promotion witness | Existing type-separation donor; named interface check OPEN |
| M4b | `latticeMellinToAnalyticZetaSameObject` | Mellin theta with Gamma/π scaling, convergence/functional equation and matching classical Riemann-zeta product; not a spectral zero identification | OPEN |
| M4c | `spectralOperatorEqualsRiemannZeroCarrier` | Genuine self-adjoint spectral carrier, all-zero correspondence and prime-side trace, positivity; absent from theta route | OPEN; **separate speculative RH-scale programme**, not required for LILA |
| M5a | `sophonticC2SemanticInterventionDescent` | Original paired before/after-router intervention on actual model history, semantics and observer refinement; distinguish routing-change and route-fixed surfaces | OPEN full-source weld |
| M5b | `sophonticC3DirectedCycleIntervention` | Same three semantic states before/after cycle with cyclic phase and chirality, source recognisable signal that cannot be reduced to a C2-only *invariant scalar* observer | OPEN |
| M5c | `sophonticS3ReflectionReversesCycle` | Actual source semantic reflection reverses C3 orientation while preserving task-selected meaning and history contract, `srs=r⁻¹` | OPEN |
| M5d | `leechC2CanRepresentC3WithoutForcingIt` | Formal separation: C2 symmetry imposes parity but allows independent 2D C3 rotation planes; prove existence of compliant C2→C3 feature consumer and negative control where no nontrivial C3 is present | OPEN |
| M6a | `leechC2C3RouterInvariantUnderOriginalAction` | Actual `HistoryOrbitMoE` router features + selected indices/weights checked under sign and triple rotation; tie rules and untransformed parameter biases explicit | OPEN on trained original |
| M6b | `leechTrialityExpertHistoryTransport` | Actual original expert outputs, states, cache, top-k permutation and action on full selected histories, checked source-to-Agda transport | OPEN |
| M6c | `leechLilaRepresentationIntertwiner` | Explicit source embedding/projection from trained layer-0/1 activations to chosen E8/Leech lattice carrier, preserves stated metric/action under source tests; **do not infer from dimensions or token names** | OPEN |
| M7a | `trialityQualityLayer01Ablation` | Original 4.763 checkpoint inspected for actual routing geometry; matched fit/dev split, seed, active parameters and training/computation budgets: C2, C2×C3, S3-compatible and lattice-feature controls | OPEN |
| M7b | `originalC2EarlyLayerOddEvenCorrection` | Measured layer 0/1 local FFN and full-student dev CE improvement, no heldout selection | OPEN; highest empirical priority |
| M7c | `originalStudentRecurrentHistoryNormBoundOrCounterexample` | Real autoregressive student with KV+expert history, compare per-layer magnitudes and route margins with teacher-forced local probe | OPEN |
| M7d | `originalDustCreditMatchesSourceGradient` | Same trained early-layer readout, fit batch, exact mathematical perturbation objective, forward-only estimate vs reverse-mode gradient; caching and timed matched-token controls | OPEN |
| M7e | `teacherStrippedStudentCheckpointBidi` | Already original **finite hardware parity ACCEPTED**; general all-input transport, long-context state and deployment speed/quality remain OPEN | PARTIAL, don't downgrade physical result |
| M7f | `fullStudentHeldoutQualityPromotion` | Independently heldout full C2/C3/sophontic candidate CE vs frozen dense teacher with predeclared tolerance; no training on heldout | OPEN, currently FAIL 4.762983>2.583408 |

**A/B/C ownership:** A = foundational same-carrier maths (M1–M3), B = finite/Sophontic mathematical-to-runtime interfaces (M4–M6), C = original trained checkpoint, real native GPU tests and generalisation (M7). These are **new descriptive subtargets of the existing 106-gate programme**, not an assertion that their source Agda theorem names currently exist or their proofs are complete. The evidence ledger must distinguish *classical theorem*, *in-repository conditional formal proof*, *finite accepted sample*, *physical test*, and *unpaid proof*.

### 4. Sophontic conceptual decision: can C2 arrive at C3 results?

**Yes as expressive capacity, not as a consequence of parity alone.** For an orthogonal sign-flip action `s=−I` on a real two-dimensional C3 phase plane, any linear 120° C3 rotation `r` commutes with `s`, so a C2-symmetric model can represent and learn C3-structured features. Conversely a *one-dimensional real C2 invariant scalar* cannot faithfully carry a nontrivial C3 rotation. Signed odd expert outputs plus even channel and vector-valued hidden state may admit C3 orientation, but the actual 4.763 model's trained routing/weights are not thereby C3 equivariant. For **S3 D4 triality**, `srs=r⁻¹` uses a *reflection* s, not the central antipodal `−I` used in Leech C2. The same s cannot be both central and the nontrivial inversion conjugator on a faithful C3 plane; supply a distinct reflection or a semidirect action with its own source parameter transport. Sophontic interventions should explicitly distinguish phase/directed cycle, reflection, coarse observer and semantic preservation under each action.

### 5. Dependency-driven phases, precise deliverables and next execution order

| Phase | Status 14 Nov | Delivered / next actual artifact | Exit requirement |
|---|---|---|---|
| P0 original symmetry/data provenance | Existing finite proofs and checkpoint evidence | Publish C2/C3/C6, D4-root/B4-root/S3, cyclotomic/Riemann zeta distinction and exact source hashes in shared ledger | No role conflation; original source references pinned |
| A1 D4/F4 triality | Source B4 carrier exists; genuine same-root action OPEN | M1a–M1c Agda source imports and focused Agda 2.9 test | D4/F4 same-carrier coset/action laws kernel accepted |
| A2 E8/Leech lattice action | Finite counts EXIST, isometry/glue OPEN | M2a–M2c original coordinate enumeration and norm-preserving action proofs | 240 E8 and 196560 Leech shell with honest coordinate/provenance receipts |
| A3 theta/modular/zeta | Eisenstein/Delta donor EXISTS, lattice theorem weld OPEN | M3a–M3d, M4b; pinned Lean/Agda joint bridge, no new Delta postulate | Same-carrier E8/Leech theta, Mellin/Dirichlet domain accepted |
| B1 Sophontic observer and 2:3 semantics | Paired finite interfaces EXIST, original source bridge OPEN | M5a–M5d; paired C2, directed C3 and S3 semantic interventions + counterexamples | Correct observer descent and differentiated action identities |
| B2 LILA geometry intertwiners | `c2c3_wave` code EXISTS, checkpoint usage UNCONFIRMED | M6a–M6c with original router and train-derived activation geometry | Checkpoint config + C2/C3/S3 action residuals, no asserted global equivariance without proof |
| C1 early-layer learner quality | Q2.1 source CE PASS; Q2.2 diagnosis PASS | M7b–M7d on layer 0/1, source Dust-vs-AdamW gradient and cached probes | Real full-student dev CE decreases under matched quality/time controls |
| C2 standalone+promotion | Q3 finite BIDI PASS; CE FAIL | M7e–M7f, warmed ABBA, long context and independent quality | Source parity beyond 8 steps; true matched runtime and quality threshold |
| C3 representation triality ablation | Proposed; no actual source GPU ablation | M7a with frozen semantics, matched C2/C6/S3/lattice variants, null geometry | Measured dev/heldout quality, stability and efficiency, with correct action tests |
| D diffusion / F federation | Intentionally PARKED | Resume only after dominant learner quality/cost bottleneck resolved | Actual downstream denoising or WAN requirements |

**Execution priority (highest expected information, not theorem glamour):** (1) confirm trained `moe_route_geometry` and paired semantic/intervention inputs; (2) source layer-0/1 C2, C2×C3 and S3 action residual/odd-even scale and actual recurrent history; (3) frozen-weight geometry probes and matched early-layer correction; (4) cached Dust gradient/efficiency comparison; (5) E8/Leech theta same-carrier algebra joined from existing Lean/Agda donors in parallel; (6) only then expensive full-model training, extended inference/ABBA and independent heldout promotion. Do not block Q2.5 quality work on completion of speculative RH spectral bridge or E8 lattice VOA construction.

**Canonical source links:** DASHI modules named above at `https://github.com/chboishabba/dashi_agda`; existing Leech PR #4 `https://github.com/chboishabba/LeechTransformer/pull/4`, runbook `docs/C2_QUALITY_FULL_MAXCUT_Q21_Q3_20261114.md`. Precise source names here are **requested future lemmas**, not claims they already exist as accepted proof terms.

---

## 2026-11-14 maximum-cut implementation continuation — finite E8 shell arithmetic and original C2/C3 physical probes

**Existing 106 programme obligations remain the accounting owner.** This tranche adds executable source receipts, **not** an all-index same-carrier Agda theorem or a new RX580 receipt. Latest connected Leech PR #4 branch `experiment/consumer-preserving-multiscale-codec-20261031`, DASHI master. User's original 4.762983 independent heldout and 33.61% teacher-stripping results remain authoritative; no new GPU performance or CE gain is reported here.

### A3. E8/Leech theta/zeta exact-integer progress

New `scripts/check_e8_leech_theta_finite_same_norm.py` constructs the **actual elementary E8 coordinate cosets** in dimension eight: even-sum `D8 = {m∈Z⁸ : Σm_i even}` and the half-translate `D8+(1/2,…,1/2)`. The dynamic program tracks integer-coordinate parity and `4||v||²` **exactly**, summing both cosets at norm-square `2n`; it does **not** compute shell counts by copying the Eisenstein expected coefficients. Independent integer arithmetic in this development session checked the first five nonzero norm shells:
`a_E8(0..5)=[1,240,2160,6720,17520,30240]`, matching `a_E4(n)=240σ₃(n)` for n>0.
Existing modular expansion identities yield the **Leech modular-form candidate coefficients**, computed independently from `E4³−720Δ` by finite polynomial convolution: `[1,0,196560,16773120,398034000]` through degree four. The zero norm-2 shell and 196560 first nonzero coefficient are exact **candidate modular coefficients**, not a Leech-coordinate enumeration. The new regression `tests/test_e8_leech_theta_finite_same_norm.py` checks both series and fail-closed non-promotion flags.

**All-index bridge still OPEN:**
- `thetaE8EqualsE4SameCarrier`: prove original E8 lattice theta modularity and identify its modular form at every coefficient, using a same-carrier uniqueness theorem and specified q-norm, or derive an all-index divisor-shell law; five coefficients do NOT prove this.
- `thetaLeechEqualsDeltaTimesJPlus24`: produce the **actual Leech coordinate lattice**, prove rank-24 even unimodular rootlessness and theta modularity, and identify weight-12 modular form. No partial coefficient check can replace this source theorem.
- `e8EpsteinZetaMellinFactorization`: given full E8 shell identity and absolute convergence `Re(s)>4`, exchange `Σ_{n≥1}240σ₃(n)(2n)^(−s)` and get `240·2^(−s)ζ(s)ζ(s−3)`, with complex-power/Mellin normalisation and analytic continuation tracked separately.
- `e8LeechDeltaSameObjectLeanAgdaWeld`: re-use `DeltaNormalizedWeight12SameObjectExact` and pinned Lean eta24 instead of assuming same-object transfer from a citation. The inspected `LilaE8ThetaJBridgeSurface` still declares the theta bridge incomplete.

**No Riemann-hypothesis promotion:** cyclotomic `ζ₃`, Monster `ζ/ζ²` character multiplicities, analytic `ζ(s)`, lattice `Z_E8(s)` and the C3 fixed/inverse-pair orbit-shape witness remain distinct. `240·3(1+16+16²)=196560` is already a numerical equality and supplies no canonical Leech C3 partition or 240-root intertwiner.

### B2/C1. Actual source C2/C3/S3 checkpoint tests (new executable owners)

Leech PR #4 adds `scripts/audit_original_c2c3_router_actions.py` and `tests/test_original_c2c3_source_actions.py`. The audit STRICT-loads original `candidate.pt`, reports **saved `moe_route_geometry`**, source SHA and actual router under (i) central antipodal `−I` on hidden inputs and histories, (ii) simultaneous C3 rotation on specified 3-coordinate blocks, and (iii) an independent reflection. It checks the **finite group laws** `r³=1`, `s²=1`, `srs=r⁻¹` for triad reflection and `−Ir=r(−I)` for central C2, and measures original selected expert IDs/weights and exact source `c2c3_wave` feature residuals. Since the source inputs are **reproducible synthetic hidden states**, this is an algebraic/router contract, NOT semantic intervention or full transformer equivariance. The trained router may be `c2_invariant`, in which case C3 invariance is not guaranteed and its failures are expected, rather than a model bug. Reflection must not be silently conflated with the commuting central C2 generator.

New `scripts/audit_actual_student_recurrent_history.py` runs the **original guarded student-only** model token-by-token under genuine KV-cache and per-layer expert-history continuation, recording each layer's history RMS/max, router boundary margin and full-step next-token choice. Both original corpus-token forced and greedy policies are supported. This is the missing physical discriminator between the previously reported **teacher-input local** RMS `1.28×10⁹` at layer11 and the **actual student autoregressive history**. The latter must be executed and interpreted independently; no stability or blow-up diagnosis is pre-claimed. `test_original_c2c3_source_actions.py` adds a constructed two-layer CPU cached-history test; `scripts/check_c2_quality_maxcut.sh` runs it.

**Source run commands (native tests first):**

```bash
# DASHI: exact integer finite certificate; no GPU, no Agda kernel run
python3 -m unittest discover -s tests -p 'test_e8_leech_theta_finite_same_norm.py' -v
python3 scripts/check_e8_leech_theta_finite_same_norm.py --max-shell 5

# LeechTransformer: source-semantic CPU suite under working Schaka Python
bash scripts/check_c2_quality_maxcut.sh

# Existing real TrueNAS candidate, within LeechTransformer checkout:
ROOT=/mnt/truenas/comet-net/experiments/lila_quality_curriculum_20261113
bash scripts/run_native_schaka101_lila.sh \
  --module scripts.audit_original_c2c3_router_actions -- \
  --candidate "$ROOT/candidate.pt" \
  --output "$ROOT/c2c3_source_action_audit.json"
bash scripts/run_native_schaka101_lila.sh \
  --module scripts.audit_actual_student_recurrent_history -- \
  --candidate "$ROOT/candidate.pt" --teacher "$TEACHER" \
  --config "$CONFIG" --token-ids "$HELDOUT_IDS" --steps 32 \
  --output "$ROOT/actual_student_history_32.json"
```

`$TEACHER`, `$CONFIG` and `$HELDOUT_IDS` must refer to the original matched experiment files, not invented source paths; `--config` is optional where recoverable. Do **not** use heldout results to select geometry/optimizer parameters—this history audit is observation-only. For fit/dev selection run a separate probe on the original train-derived development token source.

### Revised exact status / deliverables

| Roadmap obligation | This tranche delivers | Unpaid acceptance |
|---|---|---|
| M3a `thetaE8EqualsE4SameCarrier` | Executable **original E8 integer coset shell** coefficients through n=5, exact finite equality to E4 | All-index E8 theta modularity and same-carrier theorem, original Agda/Lean kernel |
| M3b `thetaLeechEqualsDeltaTimesJPlus24` | Exact finite E4³−720Δ candidate coefficients through n=4 | Actual Leech lattice coordinate carrier/rootlessness and all-weight-12 theta theorem |
| M3c `e8EpsteinZetaMellinFactorization` | Exact finite sigma3/Dirichlet coefficient relationship | Complex convergence, Fubini/Dirichlet product and Mellin integral theorem |
| M5d `leechC2CanRepresentC3WithoutForcingIt` | Concrete C2-only/C2C3 source-router negative-control tests + exact triad S3/C6 relations | Original semantic/observer capacity and completeness theorem |
| M6a `leechC2C3RouterInvariantUnderOriginalAction` | Exact actual router source probe and saved checkpoint config | Source-wide proof including score tie rules and learned parameters; actual trained native receipt |
| M6b `leechTrialityExpertHistoryTransport` | Genuine recurrent-history tracer for source physical dynamics | Agda/Source action-intertwiner on selected histories; S3 noncommuting semantics |
| M7b `originalC2EarlyLayerOddEvenCorrection` | Existing layer0/1 error receipts retained | Physical quality-corrected dev CE, same budget and heldout independence |
| M7c `originalStudentRecurrentHistoryNormBoundOrCounterexample` | New actual KV/history observer, original policy preserved | Host 32-step native trace + stability law or counterexample |
| M7a `trialityQualityLayer01Ablation` | Trained config and source transformation probes available | Actual capacity-matched trained feature ablation, no 4.763 checkpoint claim yet |

**Do not reset source quality gates:** existing 4.763 independent heldout remains Q2.5 **FAIL**; native GPU teacher-stripped output parity and 33.61% tensor-size reduction remain Q3 finite BIDI **PASS**; apparent 12.9× throughput remains unbalanced until warmed ABBA repeated. The next decisive actual measurements are `c2c3_source_action_audit.json` and `actual_student_history_32.json`, then targeted early-layer quality repair. This tranche does not construct D4/F4 triality, E8-to-Leech coordinate intertwiners or completed infinite theta identities.

### E8/Leech code-theoretic donor check — ternary versus binary Golay

Checked `DASHI/Foundations/TernaryGolay/ExplicitCode729.agda`, `CompleteWeightEnumerator.agda`, `GolaySelfDualSubspace.agda`, `CoxeterToddRoutesBoundary.agda` and `DASHI/Moonshine/VNaturalOrbifoldConstruction.agda`. The existing 729-message ternary Golay code and composition count proofs are a genuine finite `F₃` donor with explicit duality and three-symbol structure; however **the extended binary Golay code used in a standard 24-dimensional Leech lattice construction is a distinct carrier**. A 12-symbol ternary self-dual code cannot be silently substituted for the binary length-24 Golay code or for a proof of Leech rootlessness. The Coxeter–Todd and FLM orbifold modules expose relevant separate boundaries; `VNaturalOrbifoldConstruction` supplies a typed conditional assembly, not completed locality/Jacobi/Monster VOA existence. Next M2c should identify the exact existing binary Golay 24-bit carrier, or construct one with its own weight enumerator, lattice glue and norm checking. The ternary Golay 729 proof remains reusable for C3 semantics and Coxeter–Todd comparisons, without importing false Leech isomorphisms.

---

## 2026-11-14 native C2/C3 action and full recurrent-history decisive receipts; next repair max-cut

**New original user-run evidence (RX580, HIP 7.16)** updates the earlier B2/C1 unknowns without creating new programme gates. DASHI finite E8/Leech source arithmetic tests **5/5 PASS**, Leech source contract suite **29/29 PASS** *at time of run*, and original-checkpoint router/history audits now have source-specific physical receipts. The newest additional history-cap unit tests/source are committed *after* those 29/29 and are **not yet host verified**.

- `c2c3_source_action_audit.json`: actual trained model is **`moe_route_geometry="c2_invariant"`**, 12 layers, 4 experts, top2. Empirical selected IDs/top-k weights invariant under antipodal sign in all twelve layers, maximum absolute weight delta **0.0**. Under cyclic triad C3 rotation, all twelve trained original routers change selected expert IDs/weights (max delta in ~0.065–0.189); reflection changes weights ~0.038–0.187. This is a seeded synthetic-hidden-state router action probe; the model is not thereby globally C2-equivariant, and no C3 or S3 trained intertwiner is present. The key consequence for Sophontic: **C2 permits C3 as representational capacity, but this specific checkpoint never trained a C3-invariant router**.
- `actual_student_history_32.json`: original full strict student-only KV+history transitions were actually run on 32 consecutive source tokens, with learned expert-bias included in margin calculation. Layer10 final RMS **251.07**, max **1212.2051**, margin **278.5124**; layer11 final RMS **10990.6821**, max **42608.7734**, margin **27628.9336**. Layer11 RMS step1 **0.3162**, step16 **46.2432**, step32 **10990.6821**. Layers0–9 remained below RMS 0.9 **for this one input/32-step trace**, not a global bound. These numbers now establish large state growth in an **actual recurrent student**, not just previously noted teacher-forced local proxy. Token choices were data/source-sequence forced by default, although model histories were genuinely recurrent; a free-running greedy continuation remains a separate control.
- **Correction of an overstrong interpretation:** 32 observed steps of a nonlinear, expert-switched, input-driven recurrence do not imply a well-defined fixed linear transition matrix `A` with `ρ(A)>1`, still less a proved spectral-radius lower bound. We have witnessed rapidly growing norms, severe downstream top-k margin saturation, and a potential dynamical quality hazard. To claim local Jacobian gain/spectral radius, evaluate the actual selected-transition Jacobian on recorded states or prove a source-specific bound; routing changes make global differentiability conditional.

**New exact source intervention owner** in Leech PR #4: `scripts/screen_c2_history_even_repair.py`, `tests/test_c2_history_even_repair.py`, allowed launcher and consolidated contracts. This implements an **inference-only reversible** controlled intervention grid, ranked entirely on original train-derived **development** rows from verified receipt (not heldout):
1. Layer10/11 selected history transition cap `h→h min(1,R/||h||)` with R=1,4,16,64; exact finite invariant `||h_e(t)||≤R` for initially bounded histories, because selected states are clipped and unselected states are copied. C2 antipodal oddness is preserved because the radial clip is odd. This is a post-transition bound on *retained* state, not a spectral-radius theorem or a guarantee of bounded intermediate FFN activations.
2. Layer10/11 attenuation `h→αh` α=0.1 or 0.5 for comparison. Attenuation without cap is not a general nonlinear stability proof.
3. Layer0/1 even-channel output scaling β=0,.5,.75,1.25,1.5, separate and small combined controls, to test whether early-layer odd/even cancellation actually hurts full student CE.
4. All intervention candidates evaluated as original strict student-only **full development CE** from the SAME immutable pretrained candidate; no retraining, no checkpoint replacement, no independent heldout model selection, and no claimed improvement until physical measurement.

Run after pulling latest Leech PR #4:
```bash
cd /home/c/Documents/code/DASHIg/LeechTransformer
bash scripts/check_c2_quality_maxcut.sh
ROOT=/mnt/truenas/comet-net/experiments/lila_quality_curriculum_20261113
bash scripts/run_native_schaka101_lila.sh \
  --module scripts.screen_c2_history_even_repair -- \
  --candidate "$ROOT/candidate.pt" \
  --teacher "$TEACHER" --config "$CONFIG" \
  --train-ids "$TRAIN_IDS" --curriculum-receipt "$ROOT/candidate.json" \
  --batch 1 --output "$ROOT/c2_history_even_dev_repair_screen.json"
```
Use the **already existing original** source teacher/train/config actual paths; do not invent or overwrite artifacts. `--config` can be omitted if embedded. **The user has not reported running this new repair screen**; acceptance pending.

### Revised phase scoreboard and proof/experiment targets

| Phase | Changed status | Next accountable source exit |
|---|---|---|
| A3 E8/Leech theta | Finite exact integer 5/5 PASS, not all-index | `thetaE8EqualsE4SameCarrier`, `thetaLeechEqualsDeltaTimesJPlus24`, `e8EpsteinZetaMellinFactorization`: same-object infinite theta, convergence and cross-language weld OPEN |
| B2 Leech C2/C3 source router | **PHYSICAL SOURCE PROBE ACCEPTED** for C2-only checkpoint | C3 and S3 actions are non-invariant controls here; genuine `c2c3_wave` training or parameter transport and full Sophontic semantics remain OPEN |
| C1 original histories | **ACTUAL 32-STEP RECURRENCE MEASURED**, large late-layer growth CONFIRMED | `originalStudentRecurrentHistoryNormBoundOrCounterexample`: postcap C2-preserving finite invariant written/test pending, actual trained candidate postcap CE, recurrent Jacobian/selection stability OPEN |
| C1 original early quality | Layer0/1 static mismatch established previously | `originalC2EarlyLayerOddEvenCorrection`: dev-only even scaling screen pending; source full student CE gain not yet measured |
| Q2.3/Q2.4 learner | Prior single-readout Dust/SPSA/AdamW 8-step native comparison unchanged | Cached source activation credit/gradient fidelity, fair repeated budget and early-layer correction OPEN |
| Q2.5 quality | Original full teacher-free CE **4.762983** vs teacher **2.583408** | Independent heldout promotion FAIL; don't use heldout to select cap or early-channel scale |
| Q3 standalone | 33.61% tensor reduction, exact tested logits and 8-step histories accepted | Warmed ABBA, longer cached trace, independent quality promotion OPEN |
| C3 triality/Sophontic | Current C2 router proven empirically *not* C3/S3 invariant under tested action | Matched `c2c3_wave`/S3 versus C2 features with actual trained model and semantic intervention; no geometry improvement claimed |

**Most decisive next physical evidence:** baseline and dev-only capped/attenuated late recurrence vs early odd/even scaling in `c2_history_even_dev_repair_screen.json`; controlled full-student recurrent history for winning variant; only then a small train-derived warm-start correction, not a second 80-minute 825-step curriculum. D4/F4 and E8/Leech same-carrier proofs remain separate formal work; neither is a prerequisite for this immediate C2 quality repair.

---

## 2026-11-14 17:31 AEDT original C2 repair screen and persistent bounded warmstart

New original user-run RX580 evidence closes **source contract 33/33 PASS** and tests 21 frozen C2 history/even interventions on *nine train-derived development rows*. Original unmodified full student dev CE **4.791580**. Best `even_0_scale_0` gives **4.771828** (−0.019753); `even_0_scale_0.75` gives **4.782848**; `even_1_scale_1.25` **4.785780**; zero layer1 even branch **4.942530** (strong negative control). No independent heldout data used for this screen. After 21 comparisons on only nine development windows, **winner selection bias may be substantial**. The improvement is not a generalization claim and cannot be credited as full quality promotion.

Untrained `late_cap_64` alone yields **4.791690**, a +0.000110 regression relative to baseline; `late_cap_4` yields **4.802763**, +0.011183. Do not say that caps intrinsically improve model CE. On a **different** original 32-token recurrent-history trace, the combined `even0=0;cap64` changes layer11 RMS **10990.68→2.83**, max coordinate **42608.77→10.48**, route margin **27628.93→1.18**, whereas `even0=0` alone makes layer11 RMS **15419.25**; layer10 source RMS **251.07→114.94** (even0=0) and **2.73** (combined). So caps establish a *bounded observed trajectory and smaller margin*, **not** a proved stationary attractor, better unmeasured combined development CE, spectral-radius result or general recurrent Lipschitz bound.

**Next implemented source cut:** on Leech PR #4, `HistoryOrbitMoE.cap_history` is now a config-owned, default-off, C2-odd radial projection of each selected transition output (both source `step` and `execute_selected`). New `LeechConfig` fields `moe_late_history_cap`, `moe_even_layer0_scale`, `moe_even_layer1_scale` persist the physical layer10/11 history cap and layer0/1 even gains through saved checkpoint and independent pure export, without new state tensors or mutable test hooks. Original checkpoint with cap None and gain 1 must retain exact semantics. Source `scripts/train_c2_bounded_quality_repair.py` warm-starts the real 4.763 candidate, freezes shared weights and other experts, trains only early even branches and optionally late transition weights, ranks best steps on the **same original fit/dev** split with original SHA/duplicate-window checks, no heldout read, and stores the config + original heldout provenance for later validation. Uses nonzero layer0 starting even gain **0.75**, because `even0=0` is a *dead gradient* for that branch and cannot be used as its trainable starting point with fixed zero multiplier. Source `scripts/export_c2_teacher_free.py` accepts this warmstart provenance while retaining strict original heldout/teacher reference and no release admission. `tests/test_c2_native_bounded_warmstart.py` adds five new constructed source contracts to existing `scripts/check_c2_quality_maxcut.sh`. **All new code is committed; 38/38 tests and native trained CE are NOT yet measured.**

**Phase updates:**
| Gate | Evidence | Remaining physical or mathematical acceptance |
|---|---|---|
| M7b `originalC2EarlyLayerOddEvenCorrection` | Frozen C2 layer0 even null improves dev 0.019753 nats over 9 source rows; 0.75 attenuated gain improves 0.008732 | Original native warm-start train and **fresh duplicate-group-disjoint** development validation or cross-validation beyond 21-screen winner |
| M7c `originalStudentRecurrentHistoryNormBoundOrCounterexample` | Source true recurrent 32-step late growth and bounded R64 finite trace, source-config C2-odd radial operator implemented | New source CPU tests, native trained cap state, full long-context/generative stability, exact model-wide error bound |
| Q2.5 student full quality | Unmodified 4.762983 independently reproduced heldout, quality FAIL | Candidate warmstart dev gain robust across unscreened train-derived windows; **one-shot final heldout** vs matched teacher 2.583408 |
| Q3 physical teacher stripping | Original pure model exact finite BIDI, 33.61% tensor removal PASS | Repaired-config standalone strict BIDI/persistence + warmed ABBA and quality Pareto |
| A1–A3 / B1–B2 | Existing D4/B4/F4, E8/Leech theta/zeta, Sophontic/C3 targets unchanged | Genuine same-carrier kernel proofs and source action intertwiners, not solved by this local intervention |

**Immediate native source command** in Leech `docs/C2_QUALITY_FULL_MAXCUT_Q21_Q3_20261114.md`: run updated consolidated contracts, then 24-step bounded warm-start with `--history-cap 64 --layer0-even-scale 0.75 --train-late-transitions` on the *original full source checkpoint*. Preserve both the original and warm-started checkpoints; neither source writing nor a bounded history theorem is evidence of an independent heldout CE improvement. Before further tuning, increase independent, duplicate-group-disjoint development evidence: the nine screened rows are insufficient for reliable 21-way selection.
