# Corrected Leech-LILA prime decomposition: 384 = 16 × 3 × (3²−1)

**2026-11-01.** This supersedes the earlier proposed default `384 = 128 × 3` triad-only *architectural* framing, without denying its literal arithmetic.

## A. What the prior really is

- `384 = 2^7 × 3 = 16 × 24 = 16 × 3 × 8 = 16 × 3 × (3²−1)`.
- For eight attention heads, `48 = 2 × 24 = 2 × 3 × (3²−1)`.
- The current hidden state supports `[8 heads, 2 24D blocks/head, 3 lanes/block, 8 punctured-sheet coordinates/lane]`.
- The eight-point carrier is the actual existing DASHI balanced-ternary `T² \ {(0,0)}`, i.e. four antipodal directions times two orientations. This is `9-1 = 8 = 2³` in **cardinality**; it is NOT an isomorphism to three independent binary sign operations. The nine-sheet is an additive `C3×C3` group when completed at the centre, not the cyclic `C9` group.
- Its eight nonzero POINTS and eight nonconstant CHARACTERS of its Fourier dual are different types. One zero-frequency character completes the nine dual modes; one spatial centre completes the nine point positions.

Exact in-repo mathematical owners:
`DASHI/Moonshine/OggSSPP2BalancedTernaryPuncturedPlaneExact.agda`,
`DASHI/Foundations/Base369FaceSheetPunctureIncidenceIdentityExact.agda`,
`DASHI/Moonshine/C3FourierConjugationExact.agda`,
`DASHI/Foundations/PhaseQuotientNonaryGroupSeparationExact.agda`.
The latter proves **NO group isomorphism** `C3×C3 ≅ C9`, despite the nine-point set bijection. The analytic `j` same-point level-9/27 fibres remain distinct:
`DASHI/Moonshine/JInvariant369CanonicalLevelObserverTowerExact.agda`,
`JInvariant369PhaseLevelSeparationExact.agda`,
`JInvariantFormulaic369FibreObserverRepairExact.agda`.
A modular-phase/j observer or a matching nine-count does not certify a same-object neural representation.

## B. Constructive point-to-wave mapping, not a count analogy

Let `G=F3²`, `P=G\{0}` (eight sites). For each real eight-vector `a:P→R`, extend by `f(0)=0` to a nine-site signal. Let `Qf=f - (mean f) 1`. A canonical real non-DC Fourier basis `B∈R^{9×8}` for the four conjugate frequency pairs has:

`B^T B = I_8`, `B B^T = I_9 - 11^T/9`.

`wave=B^T f` and `g=B wave=Qf`. Reopen the original eight-point amplitudes as `f(u)=g(u)-g(0)` for `u≠0`.

This is an invertible `R^8 ↔ R^8` rechart but **not** an isometry of the raw punctured-eight norm. It preserves the nine-site zero-mean wave norm. For arbitrary full nine-site payload, retain the independent centre amplitude `c=f(0)`: `(wave,c)` reopens all nine values. Missing centre information must NEVER be guessed. The existing p=2 `OggSSPP2TrialecticNineCentreResidualBidiExact.agda` gives a *discrete dependent centre-only* residual example, not proof of continuous-neural centre coding.

Translations by `t ∈ G` act exactly on Fourier pair `(a_k,b_k)` by a two-dimensional rotation of angle `2π(k⋅t)/3`. This gives nine group actions, each of order dividing three. Their source-point action moves the distinguished centre, so when transported back to the punctured chart the action re-gauges the centre; it is **not** a plain eight-site permutation. Site inversion `u→-u` conjugates Fourier sine coefficients; simultaneous amplitude negation `f→-f` negates both sine and cosine. These are distinct C2 actions, and neither is an opposing argument.

`scripts/certify_punctured_nine_exact.py` checks the identities using **symbolic** `√3` and rationals with SymPy (the exact computation was independently executed locally): orthonormality, projector, invertible puncture gauge, all nine translation matrices, and all 81 pairwise group compositions. `models/punctured_nine_wave_prior.py` is the Torch float32/64 implementation with explicit residual centre functions and full tensor (384=48×8) reshape. `tests/test_punctured_nine_wave_prior.py` exercises numerical roundtrips and learned routing.

## C. Concrete learning prior and expert sign

The opt-in `HistoryOrbitMoE(route_geometry="punctured9_wave")` first converts each eight-position chunk of activation and retained expert history to the non-DC real Fourier basis. Per Fourier conjugate pair it computes three genuine joint C2/translation invariants:

`energy = a²+b²`,
`dot = a_x a_h+b_x b_h`,
`wedge = a_x b_h-b_x a_h`.

The **oriented wedge** changes sign under exchanging activation/history roles, not under simultaneous C2 inversion; it exposes relational direction without pretending an opposing argument maps to the global negative latent. For `d=384`, four real frequency pairs per eight-sheet, three independent lanes per 24D block, sixteen 24D blocks. The router uses 576 floats (=3d/2) per expert instead of 768 raw activation+history floats (=2d). It retains a separately learned signed orientation chart, separately weighted nonlinear experts, and recurrent historical transitions. Its selected routes and softmax weights are invariant under joint C2 and simultaneous `F3²` translations *by construction of the features*, up to numerical precision; whole expert outputs are C2-conjugate but NOT automatically translation-equivariant or Sophontically correct.

This is a **learner inductive bias**, not a claim that the current dense checkpoint has these properties. Full 12-layer dense FFN even/odd distillation and explicitly provided face context remain the training architecture.

## D. Distributed/codec Pareto (do not conflate sufficiency)

For one `d=384` candidate, the raw pair `(x,H_e)` is 768 FP32 floats (3072 B); router-only invariants are 576 floats (2304 B), 25% fewer. But with E=4:
- sending `x` once + four histories: `(E+1)d×4=7680 B`;
- sending four separately derived router quotients: `E×3d/2×4=9216 B`, *worse* than shared raw;
- sending `x` plus the two selected full histories: `(k+1)d×4=4608 B` before routing IDs, revisions, ACK and return data.

At 1 Gbit/s ideal one-way serialization is 0.06144 ms shared raw, 0.073728 ms four quotients, 0.036864 ms selected full; at 10 Gbit/s divide by ten. None pays RTT, authenticates history, or restores an expert's tensor from a router-only quotient. Thus actual *local routing and selected expert placement* may win where transmitting all quotient features does not. `scripts/punctured_nine_federated_cost.py` and regression demonstrate this without a WAN benchmark.

The previous measured dense codec baseline (1.077×, raw faster under 1/10 Gb assumptions) is still a valid independent baseline; it does NOT reject wave/history/consumer-aware compression. Wave symmetry can eliminate remote compute or data only with a **consumer-specific commuting square**, state-version/ACK and full correction when needed.

## E. Non-antipode/analytic-j exact boundaries

DASHI has Sophontic paired semantic interventions, typed argument-response non-antipode (`ArgumentResponseNonGeometricOppositeBidiExact`), directed 3+6=9 cyclic/anti-cyclic channels (`ChannelC3OrbitDecomposition`), irreducible trialectic face (`TrialecticBoundaryFaceNonfactorabilityExact`), and actual phase-wave finite carriers. These are prior owners for training/evaluation rather than identities magically attached to a sign. No global sign ↔ ethical outcome or argumentative disagreement correspondence is asserted.

The analytical j work gives important **observer, fibre, phase, and modular-level constraints**, not proof that learned 24D blocks are Monster/Leech group representations or that `C3²` equals `C9`. Original Leech-LILA attribution: Anatolii Kornienko (DOI 10.5281/zenodo.18784424). Original prior math authors remain credited in canonical DASHI sources. No ESD edits.

## F. Local execution

```bash
# Exact finite mathematical certificate (optional SymPy dependency):
python -m pip install sympy
python -m scripts.certify_punctured_nine_exact

# Punctured-nine neural checks:
python -m unittest tests.test_punctured_nine_wave_prior
python -m unittest tests.test_punctured_nine_federated_cost

# Run the actual dense-to-signed MoE teacher transfer using its training tokens:
python -m scripts.train_signed_wave_experts \
  --checkpoint data/best_model.pt --config leech_dense_config.json \
  --token-ids /path/to/train_ids.npy --layer -1 \
  --experts 4 --top-k 2 --expert-width 192 \
  --transition-rank 24 --route-geometry punctured9_wave \
  --epochs 3 --device cpu --output artifacts/punctured9_adapters.pt
```

The mathematical identities were checked in a separate local SymPy run; the branch's full test suite, Agda typecheck, and actual checkpoint student training have NOT been executed here. No observed accuracy, WAN gain or genuine Leech automorphism is promoted.


## 11 November 2026 — original LILA claim, LLM steering and E8/369/pants source weld

**Original scientific-source correction.** Kornienko's original
Leech-LILA README explicitly claims improved language-model
performance/efficiency from a Leech-inspired frozen orthogonal
kernel and/or geometric resonance. This is an original-author
claim—not merely our separate downstream
consumer-relative codec research objective—and deserves
direct metric-faithful independent replication. The actual
384D saved dense baseline uses a QR orthogonal 24D matrix
shared between Q and K, whose dot-product action cancels
in exact arithmetic; `lambda_geo=0` in the measured
checkpoint. That excludes a direct gain from a shared
Q/K gauge alone in ideal attention, not all
possible separately trained resonance effects.
The latest 200-step real original-dense gfx803 training
run completed, eight checkpoints verified, a
100→200 process restart accepted, ~900.64/955.09
target tokens/s, peak allocated ~526.7 MiB;
zero resonance means it does not test LILA's
original geometry-benefit claim. No Agda theorem
or empirical neural gain is inferred.

**New independent research lane: LLM-guided neuron
steering** on the actual original model and
step-200 checkpoint. A source-labelled proposal
LLM may select candidate layers/units/activation
directions and counterfactual prompts, but causal
acceptance requires separate fixed labelled
held-out evaluation, dose response,
injection/ablation necessity/sufficiency and
random/equal-norm/unguided controls. Both
the proposal trace and intervention operator
must be linked to original checkpoint, tokenizer,
layer/hook state, historical step, target
observable, source counterfactual labels
and independent evaluator. LLM claims of a
'semantic neuron' are hypotheses, not the
proof-bearing semantic source.

**Agda donor hierarchy explicitly reused:**

- `Reasoning/LeechE8PriorStrataBidiExact`:
  E8 rank eight and 240 roots versus separate
  8-index punctured `F3²`; equality of
  cardinalities is NOT an isometry/action.
- `Reasoning/LeechPuncturedNineLearningBridgeExact`:
  point antipode distinct from coefficient sign
  and C3 Fourier chart. No semantic sign inference.
- `Reasoning/Leech369TrialecticWaveLearningArchitectureBidiExact`:
  384/24/3 tensor charts, C2/C3 action, six directed
  plus three self channels, independent trialectic face.
- `Reasoning/DialecticInvariantGeometry`:
  predicate-valued stance involution/intersection,
  conceptually distinct from activation inversion.
- `Reasoning/TrialecticBoundaryFaceNonfactorabilityExact`:
  two states can have equal three dyadic edges
  and distinct face relations. A face-sensitive
  steering consumer MUST retain face evidence,
  context or an explicitly validated residual.
- `Topology/TernaryCylinderPantsGeometryExact` and
  `Reasoning/TernaryPantsSynthesisS3BridgeExact`:
  finite triple-branch refinement, 27
  synthesis cells and S3 branch transport.
  No smooth topology/TQFT promotion.
- `Reasoning/TypedHyperfabricPantsGluingBridgeExact`:
  explicit realised-edge-stalk `InterfaceMatch`,
  but no incidence rewrite or automatic path
  memory elimination.
- `Reasoning/WavePantsBundleGluingAdapterExact`:
  exact zero canonical wave defect and nonzero
  phase-changed defect; **arbitrary bundle/sheaf
  local-family gluing remains unpaid**.
- `Reasoning/LeechJointStateConsumerQuotientExact`:
  consumer-specific selected history and retained
  inactive-state condition; no blanket state loss
  or implied complete multi-context seam.

**Exact new original-object Agda cut:**
A1 selected actual `LeechGPT` checkpoint activations
→ 8D/24D/ternary index and history carrier;
A2 actual learned intervention action ↔ C2/C3/S3
commuting diagram with source-labeled observable;
A3 typed `BranchChannel` realisation of independent
neuron-steered contexts with true
`InterfaceMatch`, face/history carry and
separate actual reorganisation/gluing;
A4 mismatch negative controls proving why
boundary-only/phase-only context cannot
support face-sensitive steering;
A5 Agda 2.9 kernel acceptance of changed
safe leaves/import closure and true
model-to-proof refinement. These are
**OPEN**, not completed theorems by
writing this roadmap.

**Canonical executable-facing roadmap** is
LeechTransformer PR #4
`docs/LILA_ORIGINAL_CLAIM_NEURON_STEERING_E8_369_PANTS_ROADMAP_20261111.md`.
Do not conflate the original author's claim,
our finite Agda mathematics, acquired
GPU training, future LLM steering, or
geometry improvement measured on a
held-out evaluation.
