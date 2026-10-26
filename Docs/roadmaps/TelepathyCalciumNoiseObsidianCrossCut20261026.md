# Cross-tranche intake: calcium-channel PSI, Noise/Dust, Obsidian (2026-10-26)

## Attribution / authority
User-provided screenshots are leads, not experiments or independent replications. Credit the account `ryanrossner_phd` for the displayed calcium-channel hypothesis, Samip (@industriaalist) and named Noise/Dust contributors for their speedrun claims, and Steph Ango (kepano) for `kepano/obsidian-skills`. Do not attribute their claims to DASHI. Do not treat model architecture/agent-skills popularity as proof of quality.

## A. Calcium channels: candidate causal interaction, not telepathy evidence

Screenshot: L-type (CaV1.1/CACNA1S) inhibition reportedly opens a T-type (CaV3.2/CACNA1H) 'hearing' channel. The sketch also mentions GABA, glutamate receptors, neuregulins and multiple channel proteins. This is an author's proposed mechanism; no raw experiment, control, preregistration or blinded receiver-decoding result is supplied.

Source-bounded caveats: CaV1.1 is primarily associated with skeletal muscle excitation-contraction coupling, while CaV3.x channels have neuronal functions. Drug inhibition, channel mutation, shielding, receptor interference, subjective experience and actual extra-sensory message decoding are different causal variables. A Faraday enclosure blocks/attenuates *specified electromagnetic bands* only to its measured attenuation and aperture performance; it does not imply block of all conventional signal paths. No drug administration or mutations are proposed as a human DIY experiment.

Reuse `DASHI.Core.ExperimentalCoordinateDesignExact`, `DASHI.Core.InverseProblemIdentifiabilityBidiExact`, `DASHI.Reasoning.FibreRoutingSufficiencyCausalInterventionSnowballExact`, `DASHI/Biology/FiveHT2ACalciumIdentityGeometryBoundaryExact.agda`, and `DASHI/Biology/CrossModalityFunctionalObservationBridge.agda`. The last two are potential *donors* pending same-object inspection, not validation of this telepathy model.

Operational axes:
- assignment unit, sender message entropy, receiver decoding, time-lock/latency;
- calibrated field spectrum and shielding transfer function;
- channel expression and perturbation *only in appropriately authorised cellular models*;
- EEG/EMG, hearing, visual, mechanical, electronic leakage, experimenter effects;
- preregistered repeated decoding benchmark with nested-trial uncertainty and independent laboratories.

The distinguishing outcome is receiver message information under robust isolation, not the presence of a channel, altered perceptions, or a positive self-report.

Formal target: for randomized message `M`, decoded response `R`, leakage `L`, and biological perturbation `C`, distinguish `I(M;R | L,C)>0` from confounded correlations. Estimating conditional mutual information does *not* by itself establish causality; compare actual randomized interventions and experimental custody.

## B. Noise speedrun / Dust zeroth-order optimisation

Primary social claim dated 22 October 2026: 1.76 h -> 1.6 s for an unspecified benchmark; approx 3960x, rounded as 4000x; Dust was claimed up to 10000x more compute-efficient than prior SOTA. Verification of wall clock, hardware, token count, baseline, generalisation, model quality, total search compute, parallelism and held-out evaluation is absent from screenshot. Source: https://teapawt.org/industriaalist (original post mirrored); do not silently generalize from tiny 10M-token speedrun to frontier training.

Integrate with existing `DASHI/Cognition/PNF/OptimizationAdmissibilityUnderNondeterminismExact.agda`, `DASHI/Core/CandidateFunctionalCore.agda`, and experiment-coordinate contracts. Treat candidate solver/gradient-free optimiser as a nonauthoritative *proposal generator*, with kernel proof certificates and empirical generalisation independently verified.

Benchmark axes: (1) accepted held-out objective, (2) serial latency, (3) full accelerator joules/FLOPs, (4) number of candidate evaluations and total search attempts, (5) training tokens, (6) reproducibility/seeds, (7) proof kernel acceptance, (8) all-in costs. Apply Pareto dominance only over compatible quality constraints. A 4000x latency improvement on one benchmark is not a 4000x improvement in end-to-end research throughput.

## C. Obsidian 'second brain' tooling

Original confirmed root: https://github.com/kepano/obsidian-skills . Public repository contains agent instructions for Obsidian Markdown, Bases, JSON Canvas, CLI, Defuddle and Knap; this is not itself a mandatory database or repository-of-truth layer.

Screenshot names three other projects without unambiguous owners/URLs: `claude obsidian`, `obsidian second brain`, and `second brain starter`. Resolve repository identities before dependency introduction. Do not import social-post star counts as a source of software correctness.

Candidate integration: export a *read-only generated* claim-source-experiment graph as Markdown files with stable IDs, typed link relations and provenance fields, optionally JSON Canvas, while Git and Agda/Lean remain canonical proof authority. Version hashes and provenance of source files must not be overwritten by Obsidian frontmatter. Follow existing provenance/PNF owners and prevent two-way synchronization from editing proofs without explicit review.

## Cross-cut max-cut
1. Preserve single canonical causality/identifiability and experimental-coordinate owners.
2. Keep 'observer changed', 'causal interaction detected', 'information decoded', and 'mechanism identified' as four noncollapsible claim types.
3. Run zero new medical interventions; request existing safe data and original methodological documents first.
4. Assess zeroth-order methods on full *quality-conditioned* experiment/Pareto frontier, not reported wall-clock alone.
5. Establish original GitHub repo identity for remaining tool suggestions before installation.


## 2026-10-26 original Noise repository correction and bounded calculation

Primary repository: https://github.com/qlabs-eng/noise, *Noise: Speedrun for Pretraining Without Backpropagation*, credited to Serdar Gülbahar, Bishwas Mandal, Akshay Vegesna and Samip Dahal (2026). Original README specifies a **37.7M-parameter transformer**, **10M FineWeb tokens**, and **validation cross-entropy**. Its two tracks (minimum validation loss versus speedrun to loss 4.2) must not be conflated. The social claim compares a 1.76-hour initial run and a 1.6-second threshold run: `1.76*3600/1.6 = 3960`. The screenshot's 4000x is rounded. This is not a claim of uniform full-training scaling or improved held-out loss for the faster run. Source-derived fixed arithmetic fixture: `scripts/audit_noise_quality_conditioned_20261026.py`. It deliberately does **not** grant Pareto dominance without independent workload, compute, and full-search receipts. The source repository, not the screenshot author alone, owns benchmark authorship.

Obsidian primary owner: https://github.com/kepano/obsidian-skills, with Markdown, Bases, JSON Canvas, CLI and other skills. No direct vault modification or automatic installation is part of this PR.

Calcium hypothesis: author's screenshots remain hypothesis-only. No pharmacological or electromagnetic self-experiment is warranted; channel-identity and brain-to-brain signal-decoding are independently typed obligations.
