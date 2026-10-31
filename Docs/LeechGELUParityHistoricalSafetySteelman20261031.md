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
