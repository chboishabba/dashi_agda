# GELU parity, history-indexed experts and the original Leech-LILA safety observation

Date: 2026-10-31. This source-calibrated bridge distinguishes three levels:
real-valued analytic identity, the existing abstract involution/parity
interface, and hardware-specific PyTorch approximation semantics.

## Existing formal owners

- `DASHI/Physics/YangMills/PhysicalInvolutionParityExact.agda`: generic
  `Involution`, `EvenUnder`, and `OddUnder`. It explicitly insists that
  parity depends on a named domain involution, not a numerical label.
- `DASHI/Foundations/BalancedTernaryAntipodalOrbitExact.agda`:
  27 signed trit triples, 13 two-element antipodal classes plus the fixed
  centre; the quotient therefore has 14 total classes.
- `DASHI/Biology/TriadicKernelLiftQuotientExact.agda`: 9 signed pairs,
  5 classes under global negation.
- `DASHI/Reasoning/HistoryTimeIndexedConsumerFibreExact.agda` and
  `DASHI/Reasoning/LeechSignedHistoryExpertBidiExact.agda`:
  history-indexed consumer and finite sign-conjugate transition owners.
- `DASHI/Cognition/ResponseKink.agda`: qualitative recruitment and
  suppression shape only, not an analytic GELU theorem.

**Caution:** `DASHI/Foundations/PhysicsLinearAnalysisParity.agda` has
explicit postulate sockets. New golden formalism must not introduce
these axioms as kernel-verified analytic evidence. Reuse a safe
involution owner or prove a finite algebraic theorem directly.

## Exact real-arithmetic GELU decomposition

Let g(x)=x Phi(x), where Phi is the standard normal CDF.
Using Phi(-x)=1-Phi(x),

    g(-x)=g(x)-x.
    odd_g(x)  = (g(x)-g(-x))/2 = x/2.
    even_g(x) = (g(x)+g(-x))/2
              = g(x)-x/2 = x erf(x/sqrt(2))/2.
    g(x)=odd_g(x)+even_g(x).

Thus GELU is neither odd nor even. The *odd part is exactly linear*;
the genuinely nonlinear part is even under scalar inversion.

This does not imply a standard neural FFN `W2 GELU(W1 x + b1)+b2`
has the same clean parity relative to x. Input/output biases,
noncommuting learned matrices, normalization, residuals, and historical
state can spoil a naive sign parity. Derive the conjugated full operator
or retain exact corrections. Also PyTorch `nn.GELU` may use
floating-point approximations; analytical identities should not be
misrepresented as bitwise equal across all devices.

## History-constituted parity / expert design

For state z=(x,H), define a specified involution I acting on both
activation *and history*. Given F(z), define the exact equivariant
pair F_+(z)=F(z), F_-(z)=I(F(I(z))).
This is **conjugation**, not the assertion that F is odd. A routed
mixture has a canonical parity split under I only when a suitable
additive codomain, action and consumer are supplied.

For a scalar GELU gate along a signed canonical direction, the
odd part (linear transport) and even nonlinear part may be
represented as distinct chart contributions. Histories, orientation
witnesses, action metadata, and correction residuals are retained
in the codec. A trit quotient symbol is a *routing/code symbol*,
not a mathematically proven representation of a float activation.

Avoid conflating three different properties:
  (1) the gate-level scalar parity identity,
  (2) the history-dependent expert-family conjugation,
  (3) equivariance of the entire trained Leech model.
Only (1) is proved from the standard normal CDF reflection identity;
the finite abstraction for (2) is source-written in this branch;
(3) remains experimental/conditional.

## Original author's hypothesis and provenance

Anatolii Kornienko, comment March 9 2026:
https://github.com/SPUTNIKAI/sovereign-lila-e8/issues/3#issuecomment-4029035489

He reported early disturbing E8 story outputs (~50k steps), becoming
kinder by ~100k, while he had not observed a corresponding phase
in Leech-LILA. He hypothesised a frozen geometry suppressing
unwanted semantic modes. A separate March 9 comment requests
lambda_geo ablation and multiple train/validation curves:
https://github.com/SPUTNIKAI/sovereign-lila-e8/issues/3#issuecomment-4028844907

This historical observation is not an established 'evil is negative'
axis or evidence of inherent model safety. Genre, prompt sampling,
checkpoint timing, data provenance and training history confound the
comparison. The original Leech-LILA README itself labels its QR kernel
as a placeholder for actual Leech vectors.

## Experimental steelman, including negative controls

Compare the E8 and Leech variants with matched token budget, parameter
count, optimizer, dataset, evaluation prompts, sampling, seed panels,
checkpoint interval and lambda_geo. Require author-provided logs
where possible; distinguish training anecdotes from reproducible runs.

Record at each checkpoint:
  - held-out CE/perplexity; stable rank and condition number;
  - Q/K kernel state, training geometry loss and resonance;
  - signed/parity decomposition of pre-GELU and post-GELU activations;
  - history-dependent routing sign and expert-state evolution;
  - independent behavioral evaluations for harmfulness and
    over-refusal, uncertainty intervals and prompt-genre controls;
  - lossless codec bytes including orientation, correction, references
    and decoder state; measured distributed tokens/sec.

Test at least: dense no-geometry, QR-kernel-only (which cancels in
exact QK scores), geometric-loss-only, QR plus geometric loss,
unconstrained learned router, sign-conjugate history router,
and history-ablation variants. True Leech automorphisms require an
explicit imported action and closure proofs. Correlation between
sign orientation and an externally labelled behavior does not
prove that they are logical opposites.

## Next Agda kernel obligations

A. Introduce a *safe* abstract additive involution carrier and
projections even(f)=(f+f∘I)/2, odd(f)=(f-f∘I)/2,
or a division-free doubled formulation, proving
parity, reconstruction, and pair cancellation from explicit laws.

B. Instantiate GELU reflection only from proved normal-CDF
identities or declare the analytic theorem an external authority
boundary; do not conceal unproved facts behind `refl`.

C. Prove signed-history expert chart conjugation and replay
compatibility for declared finite transitions (already initiated).

D. Establish source-to-PyTorch simulation or exact IEEE wire
roundtrip separately, including nonlinear computation, mask,
history version and time-indexed consumer.

Do not touch `*ESD*` surfaces. No unsolved metas, `postulate`,
or terminating pragmas permitted in new Golden Agda modules.


## Commuting-square and C3 comparison (31 October update)

Source-level owner audit:
- `DASHI/Moonshine/C3FourierConjugationExact.agda` proves conjugate pairing
  of the two nontrivial characters of cyclic order-three phase.
- `DASHI/Moonshine/C3RiemannConjugationBridgeExact.agda` separates the
  involution/fixed-locus analogy from any Riemann-zero identification.
- `DASHI/Analysis/RiemannReflectionC3OrbitShapeBridgeExact.agda`
  states explicitly that the comparison stops at orbit shape.
- `DASHI/Moonshine/JInvariant369ReflectionEquivarianceExact.agda`
  provides explicit finite involutions on 3, 6, 9, 27 carriers and
  demands observer intertwining to obtain a commuting square.

For our expert the correct square is
  conjugate(F,I)(I z) = I(F z),
where z includes the activation AND history. The new
`conjugateIntertwinesInverse` theorem in
`LeechSignedHistoryExpertBidiExact.agda` proves this finite identity.
This is a genuine reuse of *commuting square proof architecture*;
there is no identification of a network expert with zeta zeros,
Monster representations or the C3 regular representation.

A second square remains to prove for an actual router/observer q:
  q(I z) = I_Q(q z),
with concrete chart, time-indexed memory and corresponding
orientation action on the quotient carrier. For a float32 tensor
the finite sign group must also specify exact bit-level handling of
negative zero and NaN payloads.

**Parity correction:** On an additive real codomain,
  even_F(z)=(F(z)+F(I z))/2,
  odd_F(z) =(F(z)-F(I z))/2,
and F(z)=even_F(z)+odd_F(z) exactly.
A residual R is *not* part of this exact decomposition. Introduce
R only for compressed/learned/approximated implementations:
  R(z)=F(z)-decode(estimated_even,estimated_odd,...).
For a full history transition, ensure all state/output coordinates
have specified additive structures, not just their signed trit labels.
Doubled parity formulas may be used to avoid division-by-two
in discrete carriers; do not equate that with an exact real-valued
GELU theorem.

C3 conjugation is an order-two automorphism of an order-three
phase group. The group order-three operation and the reflection
operation are different; neither is a declaration of ethical polarity.


## 2 November evidence-driven steelman: the C2 student fails before any safety claim

The user has run the real C2 `train_only_quality_diagnosis.json`
for the original 384D / 12-block / 4-expert top-2 signed
candidate. Source authority is the local machine artifact, not a
kernel proof or a dataset release. On **4032 next-token training
targets**, dense CE=2.54566636, complete student CE=8.60841485,
and uniform CE=7.62461899. Isolated replacement of layer 1 gives
CE +3.42024; layers 0..1 yield CE +4.00670. All logits are finite.
The teacher-forced small-layer probe shows layer-1 student RMS
0.345658 versus teacher 0.0372746 (9.273x); relative MSE 86.6193;
derived uncentered cosine about 0.0202. Signed orientation is positive
only 6/256 selected assignments in this *small* teacher-forced probe,
and [120,6,126,4] are the observed expert route counts.

**Competing explanations, not verdicts:**
- insufficient optimization (one epoch, small train corpus, all layers
  trained on teacher-forced states but deployed recursively);
- insufficient student even/odd width and rank-24 transition capacity;
- a learned hard sign whose surrogate derivative saturates;
- hard top-k starvation of rarely selected experts;
- recurrent history-scale amplification;
- aliasing between teacher-forced FFN data and student on-policy states;
- mismatch from indiscriminately replacing all 12 FFNs at once.

No observation uniquely identifies the cause. A scale-only clamp
cannot recover an output whose teacher/student direction alignment
is nearly zero. A sign learned as mostly negative does **not**
classify outputs as harmful or disagreeing. Nor can a finite C2
conjugation identity prove that a fitted neural student preserves
teacher CE.

**Steelman tests:** compare a capacity-matched non-geometric FFN
distillation control, pure even/odd with no history, forced/fixed
orientation, balanced versus learned top-k routing, frozen versus
learned history, uncompressed/full-rank versus rank-24 transition,
and teacher-forced versus on-policy hidden trajectories. Require
same corpus, tokenizer, seeds, budget, task CE, FFN norms and
selected-route statistics. Layer 1 first, then layer 0 and deeper
layers. Source training/heldout/checkpoint hashes are mandatory
for reproducible interpretation. Test original Leech geometry-only
hypotheses separately with active geometry-loss variants, QR-only
and no-geometry controls. The saved dense teacher used zero
geometry-loss coefficient and an orthogonal Q/K gauge that cancels
in exact attention scores.

**Proposed exact parity capacity obstruction (open safe Agda target):**
Let I be an involution on an input and history state space,
V a real inner-product output space, and F any target map.
Define E(z)=(F(z)+F(Iz))/2 and O(z)=(F(z)-F(Iz))/2.
For ANY candidate S with S(Iz)=-S(z),

    (||F(z)-S(z)||² + ||F(Iz)-S(Iz)||²)/2
        = ||E(z)||² + ||O(z)-S(z)||²
        >= ||E(z)||².

Thus an odd-only student has an unavoidable pairwise squared-error
floor whenever the dense target has a nonzero even component.
Proof is elementary using the inner-product parallelogram identity,
but it is **not yet a source-written/kernel-accepted Agda theorem**.
Reusing the actual involution and additive owners is required.
The existence of an even channel removes this obstruction only
at the expressivity level, not at finite capacity, optimizer or
recurrent-history deployment level. Scalar exact-CDF GELU gives a
linear odd term and nonlinear even term; it does not imply the
biased matrix FFN or trained router is odd/even as a whole.

The unchanged `LeechSignedHistoryExpertBidiExact`,
`LeechQualityGateTeacherErasureExact` and selected consumer-fibre
lemmas remain conditional finite results. Prior Python regression
acceptance (125 tests + 7 subtests, focused 34/34; reported by
user for PR #4) is **not** a proof of the numerical training
objective or of actual PyTorch↔Agda same-object refinement.
Source attribution remains Kornienko for Leech-LILA; Sophontic
semantic tests are independently authored, and Ibrahim's Monster
3B work remains separate.


## 2 November executed-source cut: parity theorem vs fitted student

Exact source F02a now exists as
`DASHI/Reasoning/LeechOddOnlyApproximationObstructionExact.agda`.
Its `historyOddCannotMatchNonOddPair` uses the previously
defined `History.invertHistory` (joint activation+memory
involution). It proves **algebraic exact non-fitting of an odd
student at both mirrored states** if the target violates oddness.
It does NOT prove the norm-squared quantitative F02b MSE floor.
The full real-valued parity/projection and GELU source theorem
still require the correct scalar/inner-product owner.

F07 also exists in source as
`LeechLayerErrorTransportExact.agda`, proving a finite teacher
trajectory majorant given an explicit ordered error calculus,
triangle law, monotone scaling and actual per-layer Lipschitz
witnesses. It does NOT derive such constants for the
trained sparse top-k router or the historical transition. The
numeric F08 logit-infinity/NLL bound is checked on probed Torch
logits by `ablate_early_layer_quality.py`; the real-analysis
Agda proof is still open.

The original unedited C2 train-only receipt is now committed
under `LeechTransformer/docs/receipts/`. The layer-1 frozen-model
counterfactual test and focused layer-1 CE/KL continuation
are source-written in PR #4; none is a new executed training
result. The full negative-control and ethics/geometry steelman
above remains necessary. Kernel acceptance unexecuted. No
claim that orientation sign indicates benevolence/harm.


## 3 November 2026: negative matched layer-one quality comparison

The user's **executed, train-only development** comparison
(three epochs, same reported seed/CPU, nearly identical trainable
parameter count) gave dense teacher CE **2.513**, guarded
focused-C2 hybrid **2.486**, strict C2 layer-1 student **2.833**,
and ordinary dense single-layer GELU control **2.191**.
C2 odd+even has **1,185,606** trainable parameters versus
**1,185,413** in the dense control (193 difference).
The dense control wins by **0.642 nats** against strict focused
C2. The guarded 0.5 gate retains original dense FFN weights
and compute; its 2.486 score does NOT certify teacher erasure,
standalone MoE quality or network Pareto.

**Status correction:** D2 source/ablation and D3 focused training
have user-executed measurements, but D3 *quality-superiority gate
FAILS* for this trained candidate. D4 full 12-layer teacher-free
promotion stays OPEN; D6 remote codec/transport and D7 semantic
quality should not inherit any quality-win assertion. Existing
Golden F02a and F07 are conditional/algebraic properties, not
certificates of learned quality or a measured E8 advantage.

**Steelman caveat from exact source review:** The historical
C2 focused trainer internally withheld a calibration partition,
while the ordinary dense control trained over all supplied fit rows.
It also optimized extra hybrid CE/KL terms and averaged local
loss over all layers, unlike the dense control's single-layer
local MSE + direct CE/KL. Thus matched parameters, seed, epochs
and CPU are not identical optimizer data/loss contracts. The
observed negative ranking stands for the tested procedures,
but should not be construed as a causal falsification of
all history/signed/E8 student architectures.

The original code path remains untouched by default.
LeechTransformer PR #4 adds an opt-in
`--matched-control-objective` with one focused layer and
`--export-optimizer-fit-ids`: directly match the focused
student-only local MSE + next-token CE + logit KL, revoke
previous calibration gates before each training epoch and
export the actual C2 optimizer rows for the dense control.
This source was written **after** the reported negative
experiment. It has not been newly executed or verified in
the GitHub connector session. The concrete rerun instructions
are at `LeechTransformer/docs/early_layer_quality_rescue_maxcut_20261102.md`.
The comparison remains limited by different initializations,
FLOPs, memory, routing and one-seed uncertainty; measure those
instead of asserting a universal prior advantage.

Original model provenance and attribution: Anatolii Kornienko
(Leech-LILA; DOI 10.5281/zenodo.18784424), independent
DASHI/C2/E8 owners as already cited, Ibrahim's Monster
ownership unchanged. No ESD edits, postulates or theorem
reclassification. The local JSON files are not available
through this connector, so these scores are the user's
reported results rather than independently parsed artifacts.
