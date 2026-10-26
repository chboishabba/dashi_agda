# Dust paper-native formalisation audit — 26 October 2026

## Original source and author credit
Dahal, Samip; Mandal, Bishwas; Gülbahar, Serdar; Vegesna, Akshay (2026), *Dust: Pretraining Transformers Without Backpropagation*, https://qlabs.sh/research/dust/ . Minimal original source code https://github.com/qlabs-eng/dust (MIT); Q Labs alone owns claimed training results. Noise speedrun is a **separate** research/competition root (https://github.com/qlabs-eng/noise), not evidence about every Dust-paper experiment. Sophontic/Michels and LILA are independent downstream applications. DASHI owns exact finite examples, type interfaces, integration and counterexamples only.

## Paper equations as stated, not merely analogy
Section 2.2: for each draw i and token t, Gaussian activation noise a_{i,t}~N(0,I), perturbed output y_t+sigma*a_{i,t}; `c_{i,s} = mean_j(ell_{j,s}) - ell_{i,s}`, notably the *population mean* of the perturbed losses, NOT clean baseline loss; (1) `r_{i,t}=sum_{s>=t} gamma^(s-t) c_{i,s}`; (2) `ghat_t=-1/(K sigma) sum_i r_{i,t} a_{i,t}`; (3) `Ghat_W=sum_t ghat_t x_t^T`. Section 2.3 attention-internal route (4) `c_{i,s}=-<ghat_s, Delta o_{i,s}>` followed by future credit. Different estimator paths for attention-local internals, head cached-logit sampling, and the 2L residual mixing scalar ES are essential and cannot be folded into Eq. (2) without source-specific refinement.

## Reuse and verified status
`DASHI/Reasoning/DustNoiseAlgorithmExact.agda` already contains the paper-shaped `ForwardOnlyTrace`, Eq. (2) credit, Eq. (3) outer product, separate Eq. (4) `AttentionCredit` and estimator-path tags; `DustNoiseFiniteProofCoreExact.agda` contains finite sign/XOR preliminaries. `scripts/check_dust_reference_equations.py` computes exact rational synthetic causal-token instances. `scripts/lila_dust_forward_exact_20261026.py` runs a downstream LILA-style toy optimiser, but does NOT prove the original Gaussian stochastic estimator unbiased. No unconditional theorem of unbiasedness is claimed, no Agda kernel acceptance claimed.

### New finite estimator diagnostic
`scripts/check_dust_finite_population_centering_counterexamples.py` locally tested with stdlib Python, <10 sec. For affine loss L(h)=3h+4 and population noise vectors, exact finite Eq. (2) produces `3 × population_variance(a)`: balanced antithetic (-1,+1) gives 3; (0,1,2) gives 2; constant (+1,+1) gives 0; (-1,0,1,3) gives 105/16. The paper's Gaussian setting supplies a *stochastic distribution* and an associated noise covariance; these finite examples are not counterexamples to a properly stated Gaussian expectation result. They establish why no unconditional all-finite-populations exact-gradient theorem is valid.

Also important: with **sample-mean centering including the target draw**, finite-K Gaussian affine expectation is `(K-1)/K * gradient` for independent scalar standard-normal noise. This finite-K factor is not automatically eliminated by Gaussianity. More generally for affine losses the conditional finite-population estimate is gradient multiplied by a sample covariance matrix (using normalisation 1/K). That is a new proof target under a concrete finite probability measure, not a theorem of this PR.

## Paper experiments and empirical authority
Original reported method: FineWeb, BPE-4096, base 8-layer width-512 transformer, 8×2048 sequence tokens per batch, three seeds per cell for main SGD; Dust population 64–16384 across source sweeps, separate tokens budgets 100k through 20M. Source authors compare to backprop and EGGROLL and extrapolate some larger-population regimes. Their paper itself states Dust is not yet compute-efficient enough to replace backprop and leaves programs-in-loop/long-looped networks for future work. Do not conflate the separately marketed Noise speedrun with these particular Dust tests or report an extrapolated asymptote as a measured result.

## Exact remaining paper-native max-cut
1. Define actual Gaussian random variables/finite draw sample as a probability-space object; prove correct conditional expected credit for finite K (including population-centering attenuation) and limiting K behaviour with stated integrability/smoothness.
2. Replace user-supplied sum congruence in Eq. (3) by actual finite-sum congruence, plus vector/matrix outer product rather than only scalar coordinate.
3. Refine attention-head estimator and block-layer interference from actual source functions in `dust.py` and `model.py` with literal same-object variable/shape correspondence; treat cached logits and residual mixing ES as distinct.
4. Independently run relevant source implementation (hardware permitting) and report methodology/timing/hyperparameters. Original repo's minimal implementation expressly omits performance optimisations, so failing to match published runtime is not automatically algorithm contradiction.
5. Only then attach LILA/Sophontic objectives as downstream consumers. No scientific claims or original credit transferred to DASHI.

CI intentionally omitted per user preference.


## 26 October source-code refinement audit: DIRECT reward branch and moving Noise benchmark

**Exact upstream observed implementation:** `qlabs-eng/dust/dust.py`, class `DUST`, method `direct_errors`, fetched from the original public source on 26 October 2026. Implementation first sets `reward = self.clean_loss.unsqueeze(0) - perturbed_loss`; it **subtracts per-chunk mean only for `nrep > 1`**. Accordingly the previous abstract `populationMeanPerturbedLoss - perturbedTokenLoss` law applies ONLY to multi-draw chunks. It is not the literal `nrep=1` code path. `DUST.step` also distinguishes attention recomputation, 256-column cached-logit head slabs, two-sided scalar ES, and final SGD, so the existing generic estimator path enum is incomplete as a source refinement.

Added `DASHI/Reasoning/DustDirectRewardBranchExact.agda` with a source-specific one-draw clean-reference reward and two-draw within-chunk centering, plus rational ring-theorem candidates: clean-baseline invariance for nrep=2, anti-symmetric reward pair and source singleton clean-shift law. No fresh kernel receipt is claimed.

The finite-K `(K-1)/K` attenuation applies under iid draws **within the sample-mean-centred group**, and relevant *group size is `nrep`, not necessarily total draws over repeated chunks or GPUs*. With nrep=1, no chunk centering happens. This correction materially changes interpretation and any putative unbiasedness theorem.

**Current Noise source rule set** at https://github.com/qlabs-eng/noise (read 26 Oct): historical 10M-token tracks archived `archive/10M`; present 30M tokens, 37.7M-param fixed-model tracks and separate open-architecture track. Main track score is 1,114,112 validation predictions; fixed-model speedrun threshold validation CE 3.5; wall time measures first-to-last update, **excludes validation and permits untimed fresh-state compile warmup**. Learning may query forwards and follow at most one nonlinear step; no chained backprop. Current README attributes different records to distinct contributors and scripts; none of them should be collapsed into the earlier 10M 1.6-second claim or represented as a reproduced speed measurement.

**Priority now:** source-hash-pin `dust.py` and each Noise record script, then prove source-step refinements branch-by-branch (nrep=1 / nrep>1; head; local attention; residual scalars; optimizer and execution cost). Leave GPU timings empirical and per-track. New branch theorem candidate and source observations are committed; no CI/Agda kernel claim.


## 26 October 2026 max-cut: source-pinned Dust step routing and LILA handoff

**Dust upstream source:** `qlabs-eng/dust/dust.py`, Git blob `c7d08ee9edc3a51dfbd9e73bbf787b9ca819c5c2` (GitHub connector exact file fetch, 26 October 2026). The source explicitly separates:
- `direct_errors` on writer, MLP-hidden, embedding, and attention-hub sites, with chunkwise centering **only if `nrep > 1`**;
- `head_error` on cached logits in **256-column slabs** with a batchwise reward centering branch `if b > 1` (NOT the `nrep > 1` condition of direct errors);
- `local_errors` for q/k/v/gate/value embeddings; q is local to the same token whereas other kinds propagate score to future tokens using gamma;
- `scalar_gradients` using symmetric **two-sided weight-space ES** for residual and initial-stream scalars;
- `reassemble` using linear outer-product or embedding scatter-add;
- `step` assembling parameter estimates and calling **SGD with momentum**, with per-group rates from `make_optimizer` (embedding 1000, value embeddings 0.3, lambda params 0.03, default recipe lr), rank-average and valid-token normalization.

`DASHI/Reasoning/DustReferenceStepContractExact.agda` now pins this routing with `DustParameterKind`, `DustEstimatorRoute`, `referenceRoute`, `SourceStep`, and deliberately opaque `LILAHandoff`. **This is not yet a literal operational refinement:** the output of `referenceRouteIsLiteral` is reflexivity and `referenceTransitionByContract` consumes a supplied update law, not a proof that upstream PyTorch code implements it. The consumer awaits actual LILA model parameter, task and held-out-pair types from the parallel worker; this PR does not change LILA sources.

**Noise competition context:** https://github.com/qlabs-eng/noise/ README fetched on 26 October 2026 (source-level current track definitions; archived 10M challenge distinct from 30M challenge). Fixed-model 30M validation loss and timing, plus 30M open-architecture track, have distinct comparator criteria. No single historical speedup can serve as all-track evidence.

**Remaining exact-maxcut gates (not generic ontology):** (1) per-route runnable Python/reference fixtures against original Dust `dust.py` and `model.py`, including chunk-centering, head slabs, attention gamma and two-sided ES; (2) true Agda finite-sum estimator probability theorem and kernel receipts; (3) specific Noise record-script source equivalences and optimiser state transitions; (4) LILA trainable parameter and held-out-pair handoff after parallel worker's actual definitions become available; (5) resource and semantic correctness Pareto BIDI. Preserve distinct attribution for Dust founders and Noise community record authors.


## 26 October source-specific head-centering cut and LILA coordination

Added `DASHI/Reasoning/DustHeadBatchCenteringExact.agda` for upstream `DUST.head_error` (dust.py blob c7d08ee9edc3a51dfbd9e73bbf787b9ca819c5c2): **two batch examples** within one noise draw, with reward centering along *batch*, independent of the number of probe draws. Source-written rational identities establish zero-sum rewards and the nontrivial baseline-shift coupling: changing the clean loss on batch item A by `shift` changes centered A reward by `shift/2` and B reward by `-shift/2`. The direct-loss `nrep>1` centering theorem therefore MUST NOT be substituted for the cached head route. Checked 243 exact-rational tuples with local Python (not Agda typechecking); no CI or kernel receipt.

Another worker's `Docs/formal/SovereignLilaDustActualLearnerIntegration20261026.md` is now present in #1265. It source-audits real `E8GPT` and points out native stochastic layer noise and mutating resonator memory. Our integration consumes its eventual source-pinned trainable-parameter interface only; no changes to its content, no duplicated optimiser and no claim of real E8GPT Dust training execution.

Still unresolved: genuine 256-column cached logit partition refinement (tanh clipping, masked targets, softmax partition), attention future-lag routing, finite probability Agda theorem, real Noise record-specific training-step source, and held-out actual E8GPT training comparisons.


## 26 October independent Noise-record source audit — no LILA duplicate

**Ownership check:** `Docs/formal/SovereignLilaDustActualLearnerIntegration20261026.md` in #1265 already owns the *planned* concrete `E8GPT` instrumentation, RNG/memory controls, layer parameter update, AdamW comparison and held-out geometry assays. #1094/#1095 own semantic/geometric reasoning and teleodynamics. No separate LILA implementation, RNG adapter, or new experimental ontology should be built here; consume those outputs when they are committed and actually executable.

**Original Noise source**, https://github.com/qlabs-eng/noise, inspected at exact Git file blob:
- `train/val/run.py`: blob `000fe5a79252f0a4caf691cb558bf1a362b93930` (2026-10-26); source records **Boost → Cut**, independent input-key/gate and future-token probes, with Adam betas (0.5,0.98), warmdown, a trajectory EMA, and a loss-scored end merge. The run's header specifies that separate finite-difference measurements are scored against measured hubs, never fed in a chain as a second probe target. Source/credit description is **author code**, not an independent verified benchmark.
- `train/speedrun/run.py`: blob `ea8e0945e6bf032ef2faeab8cd938ee0898c0e46` (2026-10-26); source describes an **identity-path warm start**, then Cut-lite with `future_draws = key_path_draws = 0`, 8-row updates, chain-rerun accelerations, then a held-out end merge. Source identifies fused query/activation/move kernels, head-moments approximation, and compiled graph warmup. Its `cosine >= 0.9999` equivalence statement is a **source-authored claim**, not a newly reproduced numeric receipt.
- The source README separates **30M-token** tracks, including fixed-model CE and speedrun-to-3.5, from archived **10M-token** tracks. The 8-minute-20-second record does not supersede the older 1.6-second **10M** result on the same metric; the task differs. No new performance reproduction is claimed.

**Immediate nonoverlapping proof obligations, Dust/Noise owner only:**
1. A source-level typed distinction between probe pathways: measured hubs; own-query/key/value conditional one-step credit; independent future-token probes versus Cut-lite with those pathways disabled.
2. Optimiser-state semantics for record-specific Adam and ANVIL paths, staged identity warm start, EMA and end-merge selection; not equivalent to original Dust's momentum SGD.
3. Exact timing/accounting boundary: warmup excluded, forward-scored end merge included, validation excluded; retain the fixed dataset/model/epoch and output head constraints.
4. For any proposed mathematical guarantee, link the literal block update and loss measurement to the proof's assumptions; finite Walsh reconstruction cannot establish an independent input-K, chain-rerun or full Noise update without a separate source refinement.
5. Wait for the **actual other-worker LILA patch** and code-level receipts before importing those types. Avoid parallel edits to the LILA owner's planned learner patch.

**Evidence grade:** direct upstream source-code inspection and Git blob identifiers; algorithmic decomposition is DASHI audit. Not an Agda kernel theorem, a GPU re-execution, a current leaderboard verification beyond the README, or an actual Sovereign-LILA training run. Attribution for the Noise main paper remains with Gülbahar/Mandal/Vegesna/Dahal; individual record scripts and contributions retain the contributors identified upstream.
