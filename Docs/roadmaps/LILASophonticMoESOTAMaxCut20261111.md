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
