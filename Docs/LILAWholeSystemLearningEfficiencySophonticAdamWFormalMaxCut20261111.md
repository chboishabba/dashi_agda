# LILA whole-system goal / bidirectional learning-efficiency maximum cut
Date: 2026-11-11. Canonical formal-first integration for DASHI PR #1442 and
LeechTransformer PR #4. This is a **proof-obligation and experimental contract**,
not a completed optimizer theorem or claim that a particular neural mechanism
has been established. Full repo owner/attribution boundaries remain in force.

## 0. Correct scientific target and Pareto admission

Kornienko's original Leech-LILA scientific claim is about **less compute,
fewer neurons/parameters, faster fitting and generalisation, better compression
and possibly improved loss/quality** from geometric architecture, not
necessarily higher final accuracy after both controls saturate. A result in
which Leech and ordinary transformers both reach 100% test accuracy can still
be evidence for a genuine time/resource Pareto gain—*if* matched controls
and a predeclared cost/quality objective establish it. Current two-WD
DASHIg results show **mixed timings**, not dominance. Keep the external
author's reported TinyStories BPC/compression benchmark distinct from our
mod-97 modular classifier and from the 200-step 64-window dense smoke
(`lambda_geo=0` and no heldout generalisation).

Define the primary multiobjective experimental vector at checkpoint t:

```
Q(t) = (
  heldout CE, heldout BPC, task/paired correctness,
  time-to-predeclared-quality threshold, consumed training FLOPs,
  wall time, joules when measured, peak GPU bytes,
  model parameters, genuinely active per-token neurons/parameters,
  active FLOPs, inference latency, model/checkpoint/wire bits,
  cross-context/off-target intervention error
)
```

Only comparable metrics on the **same task, split, tokenizer, hardware
conditions and accounting policy** admit Pareto comparison. "Fewer
neurons" requires a precise definition: physical instantiated units,
active gated units per token, effective-rank/dimensional carrier,
and/or independent usable feature count are different observables.
"Compression" requires original text character denominator and the
actual serialized bits including metadata. Don't treat loss nats as
bits/character without tokenizer and character mapping.

We need a *time-to-quality / capacity-to-quality frontier*, rather than
comparing only terminal accuracies. Use right-censored thresholds when
unreached. Predeclare a joint utility policy or report the nondominated
frontier; do not choose weights after observing the winner.

## 1. Existing exact Agda owners: reuse and limits

| Existing owner | What exists | What it does NOT imply |
| --- | --- | --- |
| `Learning/GrokkingOperatorContract` | abstract step, separate data/model codes, literal MDL monotonicity, first passage and decomposition receipts | AdamW is such an operator, true optimizer monotonicity |
| `Learning/GrokkingCOLBridge` | conditional typed COL lift and monotone iteration; `RegularisationCodingBridge` and `GrokkingMechanismWitness` sockets | weight decay = MDL; empirical grokking proves contraction |
| `Learning/Mod97WeightDecayReceipt` | separate p97/AdamW empirical row schemas, right censoring | optimizer source-code refinement or seven-point universality |
| `Reasoning/DASHIgGrokkingEmpiricalBridgeExact` | pinned Leech/plain 2×WD actual finite receipt rows and derivative summaries | Leech superiority or original TinyStories results |
| `Learning/GrokkingCircuitTemporalAlignmentExact` | extraction/intervention-rule and checkpoint identity, temporal before/with/after receipt | causal learning mechanism without original intervention |
| `Cognition/PNF/LLMGrokkingLearningFutureExact` | identical fit now, divergent generalisation futures | predictor of real trained LILA future |
| `Cognition/PNF/FullLearningStateFutureQuotientExact` and `LearningProvenanceFutureExact` | counterexample: same weights/output, distinct optimizer/provenance and future; reopening residual | weights alone are a complete reproducible training checkpoint |
| `Cognition/PNF/GrokkingInvariantSubspaceSelectionExact` | finite two-candidate zero task-action defect selects a character rule | AdamW or LILA selects this rule or universally generalises faster |
| `Cognition/Teleodynamics/LilaOrthogonalAttentionExact` (PR #1095) | shared Q/K orthogonal attention gauge distinction | original reported regularisation gains are impossible |
| `Cognition/Teleodynamics/LilaGeometricRegularizerExact` (PR #1095) | independent task+alignment/resonance regulariser source contract | geometry is an E8/Leech automorphism or a neural win |
| `Reasoning/LilaWeylGrokkingFibreMaxCutExact` (PR #1095) | reuse of actual E8 Weyl full group and DASHIg finite timing receipts | same-action original LILA semantic transporter |
| `Reasoning/SemanticInterventionEquivarianceExact` (PR #1094) | typed paired intervention, representation/model equivariance, action composition and non-promotion firewalls | inference from sign to semantic negation, fit to cause |
| `Reasoning/GeometricReasoningCandidateSelectionExact` (PR #1094) | E8/Monster/unstructured candidates, separate heldout action and compression comparison receipts | a particular candidate wins without data |
| `Reasoning/LILAForwardOnlyDustAdapterExact` (PR #1265) | conditional original observer / semantic loss + forward-only probe adapter | real all-layer Dust LILA, convergence, gradient equivalence or hardware speedup |
| `Reasoning/LeechE8PriorStrataBidiExact`, `LeechPuncturedNineLearningBridgeExact` | rank-8/240 and 8-point punctured plane separate; C2 coefficient action versus site antipode | 8=8 isometry, Leech-valid root action |
| `Reasoning/TrialecticBoundaryFaceNonfactorabilityExact`, `DialecticInvariantGeometry` | dyads do NOT determine face; typed stance/invariant field | C2 activations encode moral opposition or all context |
| `Topology/TernaryCylinderPantsGeometryExact`, `Reasoning/TernaryPantsSynthesisS3BridgeExact` | finite 1→3 branch and S3 transport | smooth cobordism or actual neural stitch |
| `Reasoning/TypedHyperfabricPantsGluingBridgeExact`, `WavePantsBundleGluingAdapterExact` | typed five-coordinate `InterfaceMatch`; zero canonical versus nonzero phase-changed residual | reorganisation constructed, arbitrary sheaf gluing paid |
| `Reasoning/LeechJointStateConsumerQuotientExact` | selected histories + inactive-state consistency and fibre-constancy | arbitrary history erasure or consumer equivalence |

The model implementation, Python/AdamW source and runtime use actual floating-point
operations. The finite Agda carrier does not by itself prove PyTorch IEEE
determinism, autograd, data provenance, device state, or neural outcome.
Actual kernel status of imported unsafe/non-`--safe` modules remains a
separate audited proof gate. Reuse existing theorems; no parallel
toy definition is a substitute for an original-object bridge.

## 2. The central real learner state and AdamW equation

**A0 — source/model identity (precondition).** Fix model revision and source
checkpoint (including configured QR kernel, resonance and tokenizer), source
training and validation data, ordered batch schedule, exact intervention
policy, optimizer code/revision, hardware/dtype and RNG contract.

**A1 — complete training state.** An admissible learner state is at least

```
S_t = (theta_t, AdamW.m_t, AdamW.v_t, AdamW.step_t,
       optimizer hyperparameters and groups, RNG_t, scheduler_t,
       training data provenance, cursor_t / batch_t,
       geometry and expert history_t, model revision,
       steering/intervention history_t, observation policy)
```

A neural forward/inference consumer may forget AdamW history. A future
learning consumer cannot generally do so; this is already made precise by
the `FullLearningStateFutureQuotientExact` counterexample.

**A2 — exact-real AdamW specification.** For per-step batch gradient
`g_t = gradient_theta L(theta_t, batch_t)`, step-count
`t>=1` and per-group weight decay `lambda`:

```
m_t = beta1*m_(t-1) + (1-beta1)*g_t
v_t = beta2*v_(t-1) + (1-beta2)*(g_t ⊙ g_t)
mhat_t = m_t/(1-beta1^t)
vhat_t = v_t/(1-beta2^t)
theta_t = (1-eta_t*lambda)*theta_(t-1)
          - eta_t*mhat_t/(sqrt(vhat_t)+eps)
```

Parameter-group variants, gradient clipping, epsilon placement, fused/
foreach implementation, loss scaling, floating precision and scheduler
must be explicit in the chosen implementation witness. This equation is
a mathematical reference, NOT a proof the runtime implements it or that
it monotonically reduces loss/MDL. An exact finite rational or abstract
ordered-field specification must handle sqrt/division assumptions.

**A3 — original geometric loss** `L_total=L_CE + lambda_geo*L_res`.
`L_res` matches actual resonance source (max basis alignment per state)
including its subgradient/tie rule; shared orthogonal Q/K gauge is a
distinct candidate and its dot-products cancel in exact arithmetic.
Must pay the same model/geometry source revision.

**A4 — learning-trajectory comparison.** Define a stopping time

```
T_q(R) = first t where measured independent heldout quality
         crosses fixed q under receipt R, or right-censored
```

Then define admissible “faster” at one quality target as
`T_q(geometry)<T_q(control)` with the same batch-token budget
and proper censoring, plus independently compare wall time,
FLOPs, energy, number of active neurons and serialized bits.
Only a multi-seed, matched implementation and hardware-receipt
predicate can promote a statistical claim of benefit.

**A5 — no automatic monotonicity.** AdamW can increase total
loss on some steps and data-level heldout CE need not be
monotone. Thus the literal `LearningOperator.mdlMonotone`
contract must NOT be inhabited merely by setting
`step=AdamW`; either prove the selected step-specific
inequality with assumptions (descent lemma, smoothness,
bounds, accepted step-size/line search) or use a
nonmonotone, progress/censored-trajectory observation
interface. Similarly weight decay is not literal codelength
without a `RegularisationCodingBridge`.

## 3. Exact remaining lemma/theorem ledger (prioritized max-cut)

| ID | Priority | Original-source lemma/payment | Admission condition |
| --- | --- | --- | --- |
| L00 | P0 | `originalLilaConfigurationAndCorpusIdentified` | source hashes/config/tokenization, valid data disjointness and original-author benchmark metric |
| L01 | P0 | `adamwStateRoundtripSameFuture` | complete `S_t` reopens, and a resumed batch produces equal specified next step; real PyTorch export verification |
| L02 | P0 | `adamwReferenceStepImplementsSelectedKernel` | actual AdamW parameter groups/clip/epsilon/bias correction/float detail refine a selected reference update |
| L03 | P0 | `sameCheckpointSameTokenScheduleComparison` | paired initial weights and model/data/compute policy fixed, no hidden change in attention implementation |
| L04 | P0 | `sharedOrthogonalGaugeCancelsAttentionScores` | actual orthogonality and Q/K application site, absent asymmetric positional transformation; test residual |
| L05 | P0 | `originalResonanceSourceLossSameFormalLoss` | actual model forward/loss and configured nonzero `lambda_geo` mapped to the formal gradient/proxy |
| L06 | P0 | `resourceAndQualityReceiptNonPromotion` | typed active-neuron/parameter/FLOPs/time/energy/BPC and quality observations; no terminal-accuracy-only winning rule |
| L07 | P0 | `grokkingFirstPassageCensoringAndTimeRescale` | existing `FirstPassage` reused, actual t10/t50/t95 and separate fit/heldout curves; no invented uncensored times |
| L08 | P0 | `matchedResourceParetoDominanceSound` | comparisons admit only same-task/hardware/protocol receipts, no post-hoc endpoint selection |
| S00 | P0 | `sophonticPairedCorrectnessSameSource` | real labelled original/altered prompts, intervention class, correct outcome; flip-rate alone rejected |
| S01 | P0 | `neuronInterventionActualActivationRefinement` | model revision, exact layer/hook, tensor/direction and causal overwrite, source tensor hash |
| S02 | P0 | `interventionRepresentationDecoderCommutes` | reuse PR #1094 representation-equivariance→model-equivariance theorem, inhabit real encoder/action/decoder |
| S03 | P1 | `steeringNecessitySufficiencySeparatelyPaid` | matching ablation/injection controls, independent assessment and off-target KL |
| S04 | P1 | `interventionTemporalCheckpointAlignment` | reuse `GrokkingCircuitTemporalAlignmentExact` run/checkpoint and frozen extraction/intervention rules |
| E00 | P0 | `actualE8RootChartToNeuralTensor` | original selected hidden tensor to 8D root carrier, not an eight-point cardinality argument |
| E01 | P1 | `originalLearnedWeylIntertwiner` | same-action for original LILA output/latent under genuine root/Weyl transform; composition on heldout interventions |
| T00 | P1 | `trialecticFacePreservedBeyondDyads` | original face-sensitive consumer has explicit face/history or residual; negative collision test |
| T01 | P1 | `ternaryPantsBranchStalkInterfaceMatches` | neural branch/channel realization satisfies original five-coordinate `InterfaceMatch` |
| T02 | P2 | `reorganisedHyperformActuallyGlued` | actual incidence/state reorganisation and restrict/reopen, not seam certificate alone |
| H00 | P1 | `signedC2C3HistoryRouterBidi` | source neural router weights, action and full history update commute under admissible chosen action |
| H01 | P1 | `selectedConsumerFutureSufficiency` | selected history plus inactive retained state and future action; no indiscriminate quotient |
| O00 | P1 | `adamwVersusDustMatchedQualityCost` | same model and data, original Dust source algorithm/variance controls; no claimed unbiasedness/full GPU acceleration from finite test |
| O01 | P2 | `regularisationCodingBridgeFromMeasuredSource` | independently admitted finite codelength and bounded coding/optimizer link, not weight decay=MDL by naming |
| O02 | P2 | `grokkingMechanismWitnessFromOriginalTrajectory` | true invariant-subspace dynamics/contraction or nonmonotone replacement; empirical logistic curve insufficient |
| F00 | P1 | `originalSourceToAgdaImportClosureAccepted` | Agda 2.9 actual module/import head receipts, no postulates/false Golden status |
| F01 | P2 | `wholeSystemSemanticAndConsumerDiagramCommutes` | implementation neural/steering/history/federation and source semantic consumers, with needed residuals and explicit errors |

These are **named obligations**, not a statement that declarations already exist.
Prior existing records are not to be copied and renamed to manufacture progress.
The sharpest proof cut is L01–L05 + S00–S02 + E00; everything else
then obtains a real source object to consume.

## 4. Bidirectional (“BIDI”) traceability obligations

**Specification → executable:** for every finite/typed formal object,
provide original repo revision, model variable and tensor shape,
algorithm/matrix formula, on-device observation, serialization
identity and a negative-control counterexample. A producer
must generate a machine-readable receipt with content hashes,
not only a prose title.

**Executable → specification:** every measured change in
quality, neurons, FLOPs, grokking onset, steering effect,
history state, network cost or GPU precision must say which
formal carrier and predicate it witnesses and the limits
of its finite sample. A numerical observation may falsify
an assumed bound but cannot establish global universal
identities from a finite number of samples.

**Causality/provenance:** match LLM proposal provenance
and steering source checkpoint; selection and evaluation
must use disjoint datasets. Sophontic-style paired
correctness, label-preserving nuisance interventions,
genuine label-changing interventions and structural
interventions must be separate. Existing semantic
response types do not identify activation negation with
argument opposition, nor infer an ontology from action fit.

**Shared/full-state boundary:** a packet containing a
selected activation/history quotient must retain enough
inactive state for any future learner or consumer requiring
it. Use `LeechJointStateConsumerQuotientExact` and
`FullLearningStateFutureQuotientExact` for fail-closed
future equivalence. A passing inference check does not
prove future-training equivalence.

## 5. Roadmap phases and actual deliverables

| Phase | Status | Deliverable/exit gate |
| --- | --- | --- |
| P0 provenance and baseline | **DONE scoped** | Original bounded 200-step GPU dense, restart 100, 8 hashed checkpoints; original mod97 grokking 7-WD, preliminary Leech/plain 2-WD; bounded receipts preserved |
| P1 whole-system formal goal contract | **THIS DOC SOURCE-COMPLETE; exact lemmas OPEN** | one graph of source-state/optimizer/geometry/steering/history/consumer, bounded resources, explicit non-promotion, named L00–F01 |
| P2 original geometric learning efficiency | **OPEN** | nonzero resonance same-model/seed, pure gauge negative controls, original TinyStories BPC, t_q/FLOPs/active-neuron Pareto |
| P3 LLM/Sophontic steering | **OPEN** | original checkpoint and post-transition steering, paired correctness, nuisance controls, layerwise causal interventions |
| P4 cross-architecture grokking | **PARTIAL** | finished nonzero lambda_geo, second optimizer, multiple seeds/tasks, invariant-subspace trajectory and temporal alignment |
| P5 E8→369/pants source/Agda weld | **DONORS PRESENT; REAL WELD OPEN** | genuine tensor→root/site, semantic action/face/historical state, five-coordinate pants seam, actual reorganisation |
| P6 C2/history, compression, whole-system federation | **C2 GPU ADMITTED; QUALITY NEGATIVE** | teacher-free quality or demonstrated history/codec cost advantage; future-preserving BIDI transport |
| P7 formal acceptance / release | **OPEN** | actual Agda 2.9 import-closure checks, source-provenance mapping, multi-seed independent physical receipts |

The phases may progress partly in parallel after P1; do not
make C2 quality an unconditional prerequisite for original
LILA geometry, steering or dense consumer-codec research.

## 6. Execution decision / top delta

Do **not** launch further GPU implementation or benchmark
work under a claim that the whole system is formalised until
the L00–L08 experimental admissibility conditions and
S00–S02 intervention/source interfaces have owners.
In particular, formally distinguish active sparse neurons
from total parameter count and trained usable features.

Immediate formal-first handoff:
1. Model the real AdamW update/config/checkpoint as a
   source-labelled complete-state transition, consistent
   with our already verified step-100 resumed GPU training.
2. Compose the existing geometry/resonance and
   grokking first-passage observations with that same
   transition rather than invent a new `LearningOperator`.
3. Instantiate Sophontic paired intervention/representation
   sockets with selected true LILA tensor hooks and
   independent correct outcomes, then reuse E8→369 and
   trialectic/pants paths only where genuine neural
   actions and typed source channels exist.
4. Keep the geometric speed/sparsity claim as an explicit
   quantitative Pareto predicate with meaningful
   right-censoring, not a demand for higher final accuracy.

### Attribution / proof status

Original Leech-LILA: Anatolii Kornienko; upstream
Sophontic intervention evaluator remains an independent
external owner; semantic intervention formalisms and
DASHI mod97/grokking/Agda constructions are DASHI
contributions; Dust algorithm credit remains with
Dahal/Mandal/Gülbahar/Vegesna; Schaka GPU-runtime
patches remain external. No new AGDA kernel check or
physical run was made by this documentation tranche.
